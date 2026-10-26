inductive myOption (α : Type) where
| none
| some (a : α)

def dec : Nat → myOption Nat
| 0 => myOption.none
| n + 1 => myOption.some n


inductive myList (α : Type) where
| nil
| cons (h : α) (t : myList α)

def head {α : Type} : myList α → myOption α
| myList.nil => myOption.none
| myList.cons h _ => myOption.some h

def head' {α : Type} : List α → myOption α
| [] => myOption.none
| h :: _ => myOption.some h

def myFold
{α : Type}
(f : α → α → α)
(f_assoc : ∀ a b c : α, f a (f b c) = f (f a b) c)
(id : α)
(fid: ∀ a : α, f id a = a ∧ f a id = a)
: List α →  α
| [] => id
| h::t => f h (myFold f f_assoc id fid t)
