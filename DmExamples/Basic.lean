import Mathlib.Data.Multiset.DershowitzManna
-- import Mathlib.Order.RelClasses
import Mathlib.Data.Prod.Lex

#print axioms Multiset.instWellFoundedisDershowitzMannaLT
-- #axiom_blame

-- Example 1: Ackermann's function
-- The `termination_by` clause instructs Lean to use a lexicographic order on the natural numbers
-- https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html
def ack : ℕ → ℕ → ℕ
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x y => (x, y)
#eval ack 3 2

def ack_mset : List ℕ → Multiset (ℕ × ℕ)
  | []  => {}
  | [_] => {}
  | z :: y :: L => (y,z) ::ₘ Multiset.ofList (L.map (λ x => (x+1, 0)))

def lt_ackstack (L1 : List ℕ) (L2 : List ℕ) :=
  @Multiset.IsDershowitzMannaLT _ (Prod.Lex.preorder _ _) (ack_mset L1) (ack_mset L2)

-- Define lexicographic order on (ℕ × ℕ)
instance : WellFoundedLT (ℕ × ℕ) := by
  exact Prod.wellFoundedLT'

-- This is where the `wellFounded_isDershowitzMannaLT` theorem is used.
-- instance : WellFoundedRelation (List ℕ) where
--   rel := lt_ackstack
--   wf  := InvImage.wf ack_mset (Multiset.wellFounded_isDershowitzMannaLT)

-- Asking whether it terminates is an instance of the halting problem, which is undecidable in general.
def ackstack : List Nat → Nat
  | n :: 0 :: L             => ackstack ((n + 1) :: L)
  | 0 :: (m + 1) :: L       => ackstack (1 :: m :: L)
  | (n + 1) :: (m + 1) :: L => ackstack (n :: (m + 1) :: m :: L)
  | [m] => m
  | [] => 0
termination_by
  L => (InvImage.wf ack_mset (Multiset.wellFounded_isDershowitzMannaLT) : WellFounded lt_ackstack).wrap L
decreasing_by
  · unfold WellFounded.wrap
    cases L
    case nil =>
      have : ack_mset [n + 1] = {} := by simp [ack_mset]
      simp_all only [Multiset.empty_eq_zero]
      have : ack_mset [n, 0] = {(0, n)} := by rfl
      rw [this]
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
          have := @Prod.Lex.lt_iff ℕ ℕ _ _ (a, n + 1) (a + 1, 0)
          aesop
  · unfold WellFounded.wrap
    simp_rw [ack_mset] at *
    unfold Multiset.IsDershowitzMannaLT
    refine ⟨Multiset.ofList (List.map (fun x => (x + 1, 0)) L), {(m, 1)}, {(m + 1, 0)}, ?_ ⟩
    repeat constructor -- how does this work again?
    simp
    constructor
    · let l := Multiset.ofList (List.map (fun x => (x + 1, 0)) L)
      change (m, 1) ::ₘ l = l + {(m, 1)}
      simp [Multiset.singleton_add, add_comm]
    · constructor
      · let l := Multiset.ofList (List.map (fun x => (x + 1, 0)) L)
        change (m + 1, 0) ::ₘ l = l + {(m + 1, 0)}
        rw [← Multiset.singleton_add]
        simp [add_comm]
      · intro y y_in
        refine ⟨(m + 1, 0), ?_⟩
        simp_all only [Multiset.mem_singleton, true_and]
        have := @Prod.Lex.lt_iff ℕ ℕ _ _ (m, 1) (m + 1, 0)
        aesop
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
      · have := @Prod.Lex.lt_iff ℕ ℕ _ _ (m + 1, n) (m + 1, n + 1)
        simp_all only [lt_self_iff_false, Nat.lt_add_one, and_self, or_true, iff_true, gt_iff_lt]
        exact this
      · have := @Prod.Lex.lt_iff ℕ ℕ _ _ (m + 1, 0) (m + 1, n + 1)
        simp_all only [Nat.zero_lt_succ, and_self, or_true, iff_true]
        exact this
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
            cases y_in with
            | inl h =>
              subst h
              have := @Prod.Lex.lt_iff ℕ ℕ _ _ (m + 1, n) (m + 1, n + 1)
              simp_all only [lt_self_iff_false, Nat.lt_add_one, and_self, or_true, iff_true, gt_iff_lt]
              exact this
            | inr h_1 =>
              subst h_1
              have := @Prod.Lex.lt_iff ℕ ℕ _ _ (m + 1, 0) (m + 1, n + 1)
              simp_all only [lt_self_iff_false, Nat.zero_lt_succ, and_self, or_true, iff_true, gt_iff_lt]
              exact this

#eval Multiset.ofList [1,2,2] = {2,1,2}
#eval ack_mset [1, 2] = {(2,1)}
#eval Prod.Lex (· < ·) (· < ·) (1,2) (3,0)
#eval [1,2,3,4,5,6,7].map (λ x => x + 1)


-- Example 2:
