import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.Prod.Lex
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Finsupp.Lex

-- This checks the axioms used by the Wellfounded instance of dm-ordering
#print axioms Multiset.instWellFoundedisDershowitzMannaLT
-- #axiom_blame

-- Example 1: Ackermann's function
-- https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html

-- The classical Ackermann's function:
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
-- Define the label function that maps each list to a multiset of tuples.
def ack_mset : List ℕ → Multiset (ℕ × ℕ)
  | []  => {}
  | [_] => {}
  | z :: y :: L => (y,z) ::ₘ Multiset.ofList (L.map (λ x => (x+1, 0)))

-- Example:
#eval ack_mset [1,7,2,3,4,5,6]

-- Define the `lt` relation between lists by the dm-ordering over their corresponding multisets.
def lt_ackstack (L1 : List ℕ) (L2 : List ℕ) :=
  @Multiset.IsDershowitzMannaLT _ (Prod.Lex.preorder _ _) (ack_mset L1) (ack_mset L2)

-- Provide the well-founded instance for the lexicographic order on (ℕ × ℕ)
instance : WellFoundedLT (ℕ × ℕ) := by
  exact Prod.wellFoundedLT'

-- The stacked version of Ackermann's function
def ackstack : List Nat → Nat
  | n :: 0 :: L             => ackstack ((n + 1) :: L)
  | 0 :: (m + 1) :: L       => ackstack (1 :: m :: L)
  | (n + 1) :: (m + 1) :: L => ackstack (n :: (m + 1) :: m :: L)
  | [m] => m
  | [] => 0
termination_by
  L => (InvImage.wf ack_mset (Multiset.wellFounded_isDershowitzMannaLT) : WellFounded lt_ackstack).wrap L -- This is where the `wellFounded_isDershowitzMannaLT` theorem is used.
decreasing_by
  · unfold WellFounded.wrap
    cases L
    case nil =>
      simp_all only [Multiset.empty_eq_zero]
      unfold Multiset.IsDershowitzMannaLT
      refine ⟨∅, ∅ , {(0, n)}, ?_⟩
      aesop
    case cons a l =>
    let l' := Multiset.ofList (List.map (fun x => (x + 1, 0)) l)
    simp_rw [ack_mset]
    have : Multiset.ofList (List.map (fun x => (x + 1, 0)) (a :: l)) = (a + 1, 0) ::ₘ l' := by simp_all only [List.map_cons,
      Multiset.cons_coe, l']
    rw [this]
    have : ((a, n + 1) ::ₘ Multiset.ofList (List.map (fun x => (x + 1, 0)) l)) = (a, n + 1) ::ₘ l' := by simp_all only [List.map_cons,
      Multiset.cons_coe, l']
    rw [this]
    unfold Multiset.IsDershowitzMannaLT
    refine ⟨l', {(a, n + 1)}, {(0, n), (a + 1, 0)}, ?_⟩
    constructor
    · simp_all only [List.map_cons, Multiset.cons_coe, Multiset.insert_eq_cons, Multiset.empty_eq_zero, ne_eq,
      Multiset.cons_ne_zero, not_false_eq_true, l']
    · constructor
      · simp [Multiset.singleton_add, add_comm]
      · constructor
        · simp [Multiset.singleton_add, add_comm]
        · intro y a_1
          simp_all only [List.map_cons, Multiset.cons_coe, Multiset.mem_singleton, Multiset.insert_eq_cons,
          Multiset.mem_cons, exists_eq_or_imp, exists_eq_left, l']
          apply Or.intro_right
          apply Prod.Lex.left
          omega
  · unfold WellFounded.wrap
    simp_rw [ack_mset] at *
    unfold Multiset.IsDershowitzMannaLT
    refine ⟨Multiset.ofList (List.map (fun x => (x + 1, 0)) L), {(m, 1)}, {(m + 1, 0)}, ?_ ⟩
    repeat' constructor
    simp
    · let l := Multiset.ofList (List.map (fun x => (x + 1, 0)) L)
      change (m, 1) ::ₘ l = l + {(m, 1)}
      simp [Multiset.singleton_add, add_comm]
    · let l := Multiset.ofList (List.map (fun x => (x + 1, 0)) L)
      change (m + 1, 0) ::ₘ l = l + {(m + 1, 0)}
      rw [← Multiset.singleton_add]
      simp [add_comm]
    · intro y y_in
      refine ⟨(m + 1, 0), ?_⟩
      simp_all only [Multiset.mem_singleton, true_and]
      apply Prod.Lex.left
      omega
  · simp
    unfold WellFounded.wrap
    simp_rw [ack_mset] at *
    cases L
    case nil =>
      simp_all only [List.map_cons, List.map_nil, Multiset.coe_singleton, Multiset.coe_nil, Multiset.cons_zero]
      unfold Multiset.IsDershowitzMannaLT
      refine ⟨∅, (m + 1, n) ::ₘ {(m + 1, 0)}, {(m + 1, n + 1)}, ?_⟩
      simp_all only [Multiset.empty_eq_zero, ne_eq, Multiset.singleton_ne_zero, not_false_eq_true, zero_add,
        Multiset.mem_cons, Multiset.mem_singleton, exists_eq_left, forall_eq_or_imp, forall_eq, true_and]
      constructor
      · apply Prod.Lex.right
        omega
      · apply Prod.Lex.right
        omega
    case cons a l =>
      let l' := Multiset.ofList (List.map (fun x => (x + 1, 0)) (a :: l))
      have : Multiset.ofList (List.map (fun x => (x + 1, 0)) (m :: a :: l)) = (m + 1, 0) ::ₘ l' := by simp_all only [List.map_cons,
        Multiset.cons_coe, l']
      rw [this]
      have : ((m + 1, n + 1) ::ₘ Multiset.ofList (List.map (fun x => (x + 1, 0)) (a :: l))) = (m + 1, n + 1) ::ₘ l' := by simp_all only [List.map_cons,
        Multiset.cons_coe, l']
      rw [this]
      unfold Multiset.IsDershowitzMannaLT
      refine ⟨l', {(m + 1, n), (m + 1, 0)}, {(m + 1, n + 1)}, ?_ ⟩
      constructor
      · simp_all only [List.map_cons, Multiset.cons_coe, Multiset.empty_eq_zero, ne_eq, Multiset.singleton_ne_zero,
        not_false_eq_true, l']
      · constructor
        · simp [Multiset.singleton_add, add_comm]
        · constructor
          · simp [Multiset.singleton_add, add_comm]
          · intro y y_in
            refine ⟨(m + 1, n + 1), ?_ ⟩
            simp_all only [List.map_cons, Multiset.cons_coe, Multiset.insert_eq_cons, Multiset.mem_cons,
              Multiset.mem_singleton, true_and, l']
            induction y_in
            case inl h =>
              rw [h]
              apply Prod.Lex.right
              omega
            case inr h =>
              rw [h]
              apply Prod.Lex.right
              omega

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
