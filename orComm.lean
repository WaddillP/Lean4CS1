-- orComm.lean
-- Disjunction is commutative: P ∨ Q → Q ∨ P

/-
Recall (Week02 §2.5): ∨ behaves like ⊕ (Sum).

  Introduction (⊕I / ∨I):
    Or.inl : P → P ∨ Q      -- pick the left disjunct
    Or.inr : Q → P ∨ Q      -- pick the right disjunct

  Elimination (⊕E / ∨E):
    given h : P ∨ Q, case-split on which side h came from
    (`match h with | Or.inl p => ... | Or.inr q => ...`) and produce
    a term of the *same* result type in both branches.

DERIVATION of  orComm : P ∨ Q → Q ∨ P
  goal: P ∨ Q → Q ∨ P
  step 1 [→I]  fun (h : P ∨ Q) => ?        ⟶ goal: Q ∨ P, with h : P ∨ Q
  step 2 [⊕E]  match h with                ⟶ two goals, both Q ∨ P:
                 | Or.inl p => ?               case inl: goal Q ∨ P, p : P in scope
                 | Or.inr q => ?               case inr: goal Q ∨ P, q : Q in scope
  step 3 [⊕I]  Or.inr p   (case inl)       ⟶ closed — p : P, so build Q ∨ P from the right
  step 4 [⊕I]  Or.inl q   (case inr)       ⟶ closed — q : Q, so build Q ∨ P from the left
  ∎
-/

theorem orComm {P Q : Prop} (h : P ∨ Q) : Q ∨ P :=
  match h with
  | Or.inl p => Or.inr p
  | Or.inr q => Or.inl q

-- No #guard/decide here: the value is a *proof*, not data (§2.6), so the
-- derivation trace above is the graded artifact. As a sanity confirmation
-- that the term type-checks, instantiate it at a concrete P and Q:

example : (2 = 2 ∨ 3 = 4) → (3 = 4 ∨ 2 = 2) := orComm

-- Logical reading: orComm is a proof that P ∨ Q implies Q ∨ P — for
-- arbitrary propositions P Q, not just this instance.
#check @orComm
