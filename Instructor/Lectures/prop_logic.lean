/-!
An infinite set of terms we'll use to 
represent proposition names. We'll call
them variables.
-/
inductive var' : Type
| mk (n : Nat)

/-!
A new Lean syntactic feature: When you
defining a datatype with just a single
constructor, one
-/
structure var : Type := 
(n: Nat)

open pl_variable 

def v₀ := pl_var 0
def v₁ := pl_var 1
def v₂ := pl_var 2
def v₃ := pl_var 3

inductive pl_connective : Type
| and
