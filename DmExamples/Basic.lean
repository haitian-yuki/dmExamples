import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.Prod.Lex
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Data.Finsupp.Lex

-- This checks the axioms used by the Wellfounded instance of dm-ordering
#print axioms Multiset.instWellFoundedisDershowitzMannaLT
-- #axiom_blame

-- Example 1: Ackermann's function
-- The `termination_by` clause instructs Lean to use a lexicographic order on the natural numbers
-- https://leanprover.github.io/theorem_proving_in_lean4/induction_and_recursion.html
def ack : ℕ → ℕ → ℕ
  | 0,   y   => y+1
  | x+1, 0   => ack x 1
  | x+1, y+1 => ack x (ack (x+1) y)
termination_by x1 y1 => (x1, y1)
decreasing_by
  -- all_goals
  --   try (apply Prod.Lex.left; omega)
  --   try (apply Prod.Lex.right; omega)

  · -- have := @Prod.Lex.lt_iff ℕ ℕ _ _ (x, 1) (x + 1, 0)
    apply Prod.Lex.left 1 0
    exact Nat.lt_add_one x
  · apply Prod.Lex.right
    omega
  · simp_wf
    apply Prod.Lex.left
    omega

#eval ack 3 2


def ack_mset : List ℕ → Multiset (ℕ × ℕ)
  | []  => {}
  | [_] => {}
  | z :: y :: L => (y,z) ::ₘ Multiset.ofList (L.map (λ x => (x+1, 0)))

#eval ack_mset [1,7,2,3,4,5,6]

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
termination_by -- Can we not do this directly on multisets?
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
          sorry -- aesop
  · unfold WellFounded.wrap
    simp_rw [ack_mset] at *
    unfold Multiset.IsDershowitzMannaLT
    refine ⟨Multiset.ofList (List.map (fun x => (x + 1, 0)) L), {(m, 1)}, {(m + 1, 0)}, ?_ ⟩
    repeat' constructor -- how does this work again?
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
      have := @Prod.Lex.lt_iff ℕ ℕ _ _ (m, 1) (m + 1, 0)
      sorry -- aesop
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
        sorry -- exact this
      · have := @Prod.Lex.lt_iff ℕ ℕ _ _ (m + 1, 0) (m + 1, n + 1)
        simp_all only [Nat.zero_lt_succ, and_self, or_true, iff_true]
        sorry -- exact this
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
            -- rw [Prod.Lex.lt_iff]
            have := @Prod.Lex.lt_iff _ _ _ _ (m + 1, n) (m + 1, n + 1)
            have := @Prod.Lex.lt_iff _ _ _ _ (m + 1, 0) (m + 1, n + 1)
            cases y_in <;> sorry -- aesop

#eval Multiset.ofList [1,2,2] = {2,1,2}
#eval ack_mset [1, 2] = {(2,1)}
#eval Prod.Lex (· < ·) (· < ·) (1,2) (3,0)
#eval [1,2,3,4,5,6,7].map (λ x => x + 1)
#eval! ackstack [2,1,2] = ackstack [1,1,0,2]
#eval! ackstack [1,1,0,2] = ackstack [0,1,0,0,2]
#eval! ackstack [0,1,0,0,2] = ackstack [1,0,0,0,2]
#eval! ackstack [1,0,0,0,2] = ackstack [2,0,0,2]
#eval! ackstack [2,0,0,2] = ackstack [3,0,2]
#eval! ackstack [3,0,2] = ackstack [4,2]
#eval! ackstack [4,2] = 11
-- Example 2: Showing the well-foundedness of a term rewriting system.

inductive mytype
| nat (n : ℕ)
-- | boolean (b : Bool)
-- | string (s : String)

open mytype
#check nat 2
-- #check boolean True
-- #check string "hi"

def mytype_le : mytype → mytype → Prop
| (nat n₁), (nat n₂) => n₁ ≤ n₂

-- | (boolean b₁), (boolean b₂) => b₁ → b₂  -- Interpreting `false ≤ true`
-- | (string s₁), (string s₂) => s₁.isPrefixOf s₂  -- Lexicographic order
-- | _, _ => false  -- Different types are unrelated

instance decidable_mytype_le : ∀ (a b : mytype), Decidable (mytype_le a b) := by
  rintro ⟨a⟩ ⟨b⟩

  simp [mytype_le]
  infer_instance

  -- by_cases a ≤ b
  -- · apply isTrue; assumption
  -- · apply isFalse; assumption





-- sorry
#print List.isPrefixOf

#eval mytype_le (nat 2) (nat 7)

-- Example 3: Differentiation?
