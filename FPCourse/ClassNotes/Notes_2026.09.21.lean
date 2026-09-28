/- @@@

# Notes 9/21/26


- Curry-Howard Injection: Deductive Reasoning (Prop) => Computation (Type)

- Deep vs Shallow embedding of abstract theories into Lean 4
  - Deep embedding: Syntax as a type with constructor for each kind of term (propositional logic)
  - Shallow embedding: Syntax as collection of types, one for each kind of term (predicate logic)

  - Empty and False
  - Unit and True
  - Prod and And
  - Sum and Or
  -


@@@ -/


inductive nothing : Prop where

def neg (a : Prop) : Prop := a → False

example myFalse : neg nothing
| f => nomatch f


inductive KevinIsFromCville : Prop where
  | driversLicense

example : KevinIsFromCville := KevinIsFromCville.driversLicense


inductive JorgIsFromRonto : Prop where
| driversLicense
| utilityBill
| healthCard

example : And KevinIsFromCville JorgIsFromRonto :=
And.intro KevinIsFromCville.driversLicense JorgIsFromRonto.driversLicense

inductive Cat : Type where
| siamese
| tabby

example : ¬(Cat.siamese = Cat.tabby)
| m => nomatch m


/- @@@
# De Morgan's Laws (for negation)

Only three of the four classical De Morgan's laws hold constructively
(without the law of excluded middle). The fourth, ¬(P ∧ Q) → ¬P ∨ ¬Q,
requires classical logic and is not provable here.
@@@ -/

-- ¬(P ∨ Q) → ¬P ∧ ¬Q
example (P Q : Prop) : ¬(P ∨ Q) → ¬P ∧ ¬Q :=
  fun npq =>
    And.intro
      (fun p => npq (Or.inl p))
      (fun q => npq (Or.inr q))

-- ¬P ∧ ¬Q → ¬(P ∨ Q)
example (P Q : Prop) : ¬P ∧ ¬Q → ¬(P ∨ Q)
| And.intro np nq, Or.inl p => np p
| And.intro np nq, Or.inr q => nq q

-- ¬P ∨ ¬Q → ¬(P ∧ Q)
example (P Q : Prop) : ¬P ∨ ¬Q → ¬(P ∧ Q)
| Or.inl np, And.intro p _q => np p
| Or.inr nq, And.intro _p q => nq q

-- Note: ¬(P ∧ Q) → ¬P ∨ ¬Q is NOT provable constructively (needs excluded middle)
