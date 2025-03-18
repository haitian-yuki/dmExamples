import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.Prod.Lex
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Finsupp.Lex

-- This checks the axioms used by the Wellfounded instance of dm-ordering
#print axioms Multiset.instWellFoundedisDershowitzMannaLT
-- #axiom_blame

-- Example 1: Ackermann's function
-- https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html

/-- The classical Ackermann's function. -/
def ack : ℕ → ℕ → ℕ
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x1 y1 => (x1, y1) -- The `termination_by` clause instructs Lean to use a lexicographic order on the natural numbers.
decreasing_by -- This `decreasing_by` proof for the classical Ackermann's function can be inferred automatically.
  all_goals
    try (apply Prod.Lex.left; omega)
    try (apply Prod.Lex.right; omega)

-- Example:
#eval ack 3 2

-- Now move on to the stacked version of Ackermann's function.
/-- The label function that maps each list to a multiset of tuples. -/
def ack_mset : List ℕ → Multiset (ℕ × ℕ)
  | []  => {}
  | [_] => {}
  | z :: y :: L => (y,z) ::ₘ Multiset.ofList (L.map (λ x => (x+1, 0)))

-- Example:
#eval ack_mset [1,7,2,3,4,5,6]

/-- The `lt` relation between lists defined by the dm-ordering over their corresponding multisets. -/
def lt_ackstack (L1 : List ℕ) (L2 : List ℕ) :=
  @Multiset.IsDershowitzMannaLT _ (Prod.Lex.preorder _ _) (ack_mset L1) (ack_mset L2)

-- Provide the well-founded instance for the lexicographic order on (ℕ × ℕ).
instance : WellFoundedLT (ℕ × ℕ) := by
  exact Prod.wellFoundedLT'

/-- The stacked version of Ackermann's function. -/
def ackstack : List Nat → Nat
  | n :: 0 :: L             => ackstack ((n + 1) :: L)
  | 0 :: (m + 1) :: L       => ackstack (1 :: m :: L)
  | (n + 1) :: (m + 1) :: L => ackstack (n :: (m + 1) :: m :: L)
  | [m] => m
  | [] => 0
termination_by
  L => (InvImage.wf ack_mset (Multiset.wellFounded_isDershowitzMannaLT) : WellFounded lt_ackstack).wrap L -- This is where the `wellFounded_isDershowitzMannaLT` theorem is used.
decreasing_by
  · simp only [WellFounded.wrap]
    cases L
    case nil =>
      unfold Multiset.IsDershowitzMannaLT
      refine ⟨∅, ∅, {(0, n)}, ?_⟩
      aesop
    case cons a l =>
    let l' := Multiset.ofList (l.map (fun x => (x + 1, 0)))
    simp only [ack_mset]
    have : Multiset.ofList ((a :: l).map (fun x => (x + 1, 0))) = (a + 1, 0) ::ₘ l' := by simp_all [l']
    rw [this]; clear this
    have : ((a, n + 1) ::ₘ Multiset.ofList (List.map (fun x => (x + 1, 0)) l)) = (a, n + 1) ::ₘ l' := by simp_all [l']
    rw [this]; clear this
    unfold Multiset.IsDershowitzMannaLT
    refine ⟨l', {(a, n + 1)}, {(0, n), (a + 1, 0)}, ?_, ?_, ?_, ?_⟩
    · simp_all [l']
    · simp [Multiset.singleton_add, add_comm]
    · simp [Multiset.singleton_add, add_comm]
    · intro y a_1
      simp_all only [List.map_cons, Multiset.cons_coe, Multiset.mem_singleton, Multiset.insert_eq_cons,
          Multiset.mem_cons, exists_eq_or_imp, exists_eq_left, l']
      exact Or.inr (Prod.Lex.left _ _ (lt_add_one a))
  · unfold WellFounded.wrap
    simp_rw [ack_mset] at *
    unfold Multiset.IsDershowitzMannaLT
    let l := Multiset.ofList (L.map (fun x => (x + 1, 0)))
    refine ⟨l, {(m, 1)}, {(m + 1, 0)}, by simp, ?eqXY, ?eqXZ, ?y_lt_z⟩ -- here we choose X, Y and Z
    · simp [l, Multiset.singleton_add, add_comm]
    · simp [l, add_comm]
    · intro y y_in
      refine ⟨(m + 1, 0), ?_⟩
      simp_all only [Multiset.mem_singleton, true_and]
      apply Prod.Lex.left _ _ (lt_add_one m)
  · simp
    unfold WellFounded.wrap
    simp_rw [ack_mset] at *
    cases L
    case nil =>
      simp_all only [List.map_cons, List.map_nil, Multiset.coe_singleton, Multiset.coe_nil, Multiset.cons_zero]
      unfold Multiset.IsDershowitzMannaLT
      refine ⟨∅, (m + 1, n) ::ₘ {(m + 1, 0)}, {(m + 1, n + 1)}, by simp, by simp, by simp, ?_⟩
      simp_all only [Multiset.mem_cons, Multiset.mem_singleton, exists_eq_left, forall_eq_or_imp, forall_eq]
      exact ⟨Prod.Lex.right _ (lt_add_one n), Prod.Lex.right _ (Nat.zero_lt_succ n)⟩
    case cons a l =>
      let l' := Multiset.ofList (List.map (fun x => (x + 1, 0)) (a :: l))
      have : Multiset.ofList (List.map (fun x => (x + 1, 0)) (m :: a :: l)) = (m + 1, 0) ::ₘ l' := by simp_all [l']
      rw [this]; clear this
      have : ((m + 1, n + 1) ::ₘ Multiset.ofList (List.map (fun x => (x + 1, 0)) (a :: l))) = (m + 1, n + 1) ::ₘ l' := by simp_all [l']
      rw [this]; clear this
      unfold Multiset.IsDershowitzMannaLT
      refine ⟨l', {(m + 1, n), (m + 1, 0)}, {(m + 1, n + 1)}, by simp, ?_, ?_, ?_⟩
      · simp [add_comm]
      · simp [add_comm]
      · intro y y_in
        refine ⟨(m + 1, n + 1), ?_ ⟩
        simp_all only [List.map_cons, Multiset.cons_coe, Multiset.insert_eq_cons, Multiset.mem_cons,
          Multiset.mem_singleton, true_and, l']
        cases y_in
        case inl h => exact h ▸ Prod.Lex.right _ (lt_add_one n)
        case inr h => exact h ▸ Prod.Lex.right _ (Nat.zero_lt_succ n)

-- Examples:
#eval Multiset.ofList [1,2,2] = {2,1,2}
#eval ack_mset [1, 2] = {(2,1)}
#eval Prod.Lex (· < ·) (· < ·) (1,2) (3,0)
#eval [1,2,3,4,5,6,7].map (λ x => x + 1)
#eval ackstack [2,1,2] = ackstack [1,1,0,2]
#eval ackstack [1,1,0,2] = ackstack [0,1,0,0,2]
#eval ackstack [0,1,0,0,2] = ackstack [1,0,0,0,2]
#eval ackstack [1,0,0,0,2] = ackstack [2,0,0,2]
#eval ackstack [2,0,0,2] = ackstack [3,0,2]
#eval ackstack [3,0,2] = ackstack [4,2]
#eval! ackstack [4,2] = 11
