


inductive Dog: Type where
| Iris
| Fido
| Sargent

open Dog

inductive Friendly : Dog → Prop where
| irisFriendly : Friendly Iris
| fidoFriendly : Friendly Fido

inductive Furry : Dog → Prop where
| irisFurry : Furry Iris
| sargentFurry : Furry Sargent

example : Friendly Iris ∧ Furry Iris := _

def Suitable'' : (d : Dog) → Prop := fun d => (Friendly d ∧ Furry d)
def Suitable' (d : Dog) : Prop := (Friendly d ∧ Furry d)
def Suitable (d : Dog) : Prop := (Friendly d ∧ Furry d)


example : Suitable Iris :=
 And.intro Friendly.irisFriendly Furry.irisFurry


#check (Suitable)
#check (Friendly)
#check (Furry)


#check (∀ (d : Dog), Friendly d)

example : (∀ (d : Dog), Friendly d) :=
  fun d => match d with
  | Iris => Friendly.irisFriendly
  | Fido => Friendly.fidoFriendly
  | Sargent => by sorry


example : ¬(∀ (d : Dog), Friendly d) :=
  fun allDogsFriendly =>
    let sf := allDogsFriendly Sargent
    nomatch sf


example : ∃ (d : Dog), Friendly d :=
  ⟨Iris, Friendly.irisFriendly⟩

/-if theres a dog thats suitable there is a dog that is friendly-/

def suitable_implies_friendly : (∃ (d : Dog), Suitable d) → (∃ (d : Dog), Friendly d) :=
  fun h =>
    let ⟨d, hd⟩ := h
    ⟨d, hd.1⟩
