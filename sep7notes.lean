#check Empty -- no values computational
#check False -- no proofs logical

#check Unit --one value, like void in java? computational
#check True -- logical, one value = proof

example : Nat := 2
example : True := True.intro
example: Unit := Unit.unit

namespace hidden

inductive Bool : Type where
| true : Bool
| false : Bool


def b2s (b : Bool) : String :=
  match b with -- must enumarate all cases
  | Bool.true => "true"
  | Bool.false => "false"

end hidden


#check Bool -- two values

#check Option Bool --

#check Nat -- natural numbers


namespace hidden

inductive Nat : Type where
| Zero : Nat
| Succ (n: Nat) : Nat




open hidden.Nat

def zero : Nat := Nat.Zero
def one : Nat := Nat.Succ zero
def two : Nat := Nat.Succ one

def funk (n : Nat) : String :=
  match n with
  | Nat.Zero => ""
  | Nat.Succ n' => "!" ++ funk n'


#eval funk two

end hidden

#check Prod
#check Sum


def id_Empty : Empty → Empty :=
  fun x => x
def id_ListNat : List Nat → List Nat :=
  fun x => x

def swap'' :
∀
  (α : Type u)
  (β : Type u),
  a × b → b × a
  :=
  fun α β (a, b) => (b, a)
