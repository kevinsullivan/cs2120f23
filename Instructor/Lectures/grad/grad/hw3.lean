/-!
#1

Define a function, dec' : Nat → Nat, that takes any Nat, n, and that
returns 0 if n is 0 and that otherwise returns one less than n. Hint:
case analysis on n. When you've succeeded the following test cases
should run and return the expected values.
-/

#eval dec' 2    -- expect 1
#eval dec' 1    -- expect 0
#eval dec' 0    -- expect 0

def dec' : Nat → Nat
| Nat.zero => 0
| (Nat.succ n') => n'

def dec2 : Nat → Nat
| Nat.zero => 0
| 1 => 0
| (Nat.succ (Nat.succ n'')) => n''

#eval dec2 0
#eval dec2 2
#eval dec2 5

/-
#2

Define a function, l2l, polymorphic in two type parameters, α and β, that
also takes a function, f, from α to β and a list of α values and that returns
a  list of corresponding β values. As an example, (l2l Nat.succ [0, 1, 2]) is
expected to return [1, 2, 3]. Write a few test cases where α is String, β is
Nat, and f is String.length. Hint: Use case analysis on the incoming list: it
will be either List.nil or (List.cons h t), the latter of which can also be
written as (h::t).
-/

def l2l {α β : Type} : (α → β) → (List α) → List β
| _, List.nil => List.nil
| f, (List.cons h t) => List.cons (f h) (l2l f t)

#eval l2l Nat.succ [0,2,4]

/-!
#3

Define a data type, called PRFV (short for "partial function return value"),
polymorphic in one type, α, where a value of this type is either "undefined"
or "defined α". If α is Nat, for example, then you would have (undefined) and
(defined 3) as values of this type. In the case of undefined,, you will have
to disable implicit arguments, as there's no value provided to this constructor
from which Lean can infer α.
-/

inductive PFRV (α : Type)
| undefined
| defined (a : α)

def p1 : PFRV Nat := PFRV.undefined
def p2 := PFRV.defined 1


/-!
#4

Define a variant of dec', called dec, that takes a natural number, n, as an
argument and that returns a (PRFV Nat). This value must be "PFRV.undefined"
if n = 0, reflecting the idea that dec is a partial function, one that is not
defined for the argument value, 0; and that returns one less than n otherwise.
You will thus represent a partial function from Nat to Nat as a total function
from Nat to PRFV Nat.
-/

def dec : Nat → PFRV Nat
| 0 => PFRV.undefined
| n' + 1 => PFRV.defined n'

#reduce dec 2

/-!
#5

Define a function, isZero from Nat to Bool that returns true if its argument
is zero and false otherwise. Write a few test cases to show that it works.
-/

def isZero : Nat → Bool
| 0 => true
| _ => false

/-!
#6

Define a function, isDef, from PFRV α to Bool, that returns false if the given
PFRV α is "undefined" and true otherwise. The following test cases should then
return the expected values.
-/

#eval isDef (dec 0)   -- expect false
#eval isDef (dec 1)   -- expect true


def isDef : PFRV Nat → Bool
| PFRV.undefined => false
| _ => true

/-!
***
New material
***
-/


/-!
The fold right function.
-/

/- version 1 : add up numbers in list -/

def foldr''' : (Nat → Nat → Nat) → Nat → List Nat → Nat
| _, id, [] => id
| op, id, h::t => op h (foldr''' op id t)

def foldr'' : (String → String → String) → String → List String → String
| _, id, [] => id
| op, id, h::t => op h (foldr'' op id t)

def foldr' { α : Type }: (α → α → α) → α → List α → α
| _, id, [] => id
| op, id, h::t => op h (foldr' op id t)

def foldr {α β : Type} : (α → β → β) → β → List α → β
| _, id, List.nil => id
| op, id, (h::t) => op h (foldr op id t)

-- Test cases
#reduce foldr''' Nat.add 0 [1,2,3,4,5]
#reduce foldr''' Nat.mul 1 [1,2,3,4,5]
#reduce foldr''' Nat.sub 0 [5,3,1]
#eval foldr' String.append "" ["Hello, ", "Lean!"]

/-! HOMEWORK #4
-/

def isEvenLen : String → Bool := λ s => s.length % 2 == 0

def combine : String → Bool → Bool
| s, b => and (isEvenLen s) b

/-!
def foldr {α β : Type} : (α → β → β) → β → List α → β
| _, id, List.nil => id
| op, id, (h::t) => _
-/

#eval foldr combine true []
#eval foldr combine true ["Hello,", "Lean"]
#eval foldr combine true ["Hello,", "Lean!"]

def foldr_ {α : Type} : (α → α → α) → α → List α → α
| _, id, List.nil => id
| op, id, (h::t) => op h (foldr_ op id t)

#eval foldr_ (Nat.add) 0 [1,2,3]
#eval foldr_ (Nat.add) 1 [1,2,3]

/-
What can go wrong?

You can pass a non-identity element.
-/

/-!
What's rules must be enforced?

- id is the identity element for op
- op must be associative
-/

/-!
How can we express these rules?
-/

/-!
How can we be assured the rules are enforced?
-/

/-!
Type universe levels. Example of identity function.
-/


/-!
Type Universes-/

inductive higher
| mk
    (α : Type)      -- Type 0
    (a : α)

#check higher       -- Type 1

def h : higher :=
  higher.mk
    Nat             -- a type
    1               -- a value of this type

inductive even_higher
| mk
    (α : Type 1)    -- a type whose values contain a Type value
    (a : α)         -- a value of that type

#check even_higher  -- a field of type Type 1 puts this type in Type 2

def h2 : even_higher :=
  even_higher.mk
    higher          -- a Type value of (in) the type, Type 1
    h               -- a value of such a type

universe u
inductive any_higher : Type (u+1) where
| mk
  (α : Type u)
  (a : α)

-- example

def way_high :=
  any_higher.mk
    even_higher -- Lean infers u
    h2

#check way_high
