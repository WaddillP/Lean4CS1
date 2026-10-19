namespace Arith

-- syntax for arithmetic expressions
inductive ArithExpr where
| lit (n : Nat) : ArithExpr
| plus (a1 a2 : ArithExpr) : ArithExpr

open ArithExpr
-- expressions using our syntax
def a1 : ArithExpr := lit 1
def a7 : ArithExpr := lit 7
def a8 : ArithExpr := plus a1 a7


-- opertaional semantics

def arithEval (t:ArithExpr) : Nat :=
  match t with
  | lit n => n
  | plus a1 a2 => arithEval a1 + arithEval a2
end Arith
