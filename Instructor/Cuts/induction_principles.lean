/-!
## Induction Principles

VERY MUCH UNDER CONSTRUCTION. BEST TO IGNORE.

In the last class, we saw what it meant for a 
type to be inductively defined. In a nutshell,
an inductive definition gives us constructors
to create one or more base (non-nested) objects 
along with constructors for creating new objects
from smaller ones of the same type.

We saw two examples. First, given a solid doll
and a constructor, shell, for creating a larger
doll from a smaller one, we can construct a doll
of any depth. We start with solid and then apply
*shell* as many times as needed to build a doll 
of any size. Second, given *zero* and the *succ*
contructor for building a next larger Nat from any
smaller one, we can build a Nat of any magnitude.
We again do it by starting with zero and applying
*succ* as many times as needed.

Is there a general principle here? Yes there is.
To get at it, let's try to formalize the idea for
the doll type. What we want to say is that given
solid and a constructor function
-/



inductive Doll : Type
| solid
| shell (d : Doll)

open Doll

def mk_doll : Nat → Doll 
| 0 => solid
| (n' + 1) => shell (mk_doll n')

#reduce mk_doll 5   -- this function works to build a doll of *any* depth

-- Nat.induction {C : Nat → Prop} (n : Nat) (h₁ : C 0) (h₂ : ∀ (n : Nat), C n → C (n + 1)) : C n

#check @Nat.rec

/-!
@Nat.rec : 
  {motive : Nat → Sort u_1} → motive Nat.zero → ((n : Nat) → motive n → motive (Nat.succ n)) → (t : Nat) → motive t
-/

def nat_ind : 
  {motive : Nat → Sort u_1} → 
   motive Nat.zero → 
   ((n : Nat) → motive n → motive (Nat.succ n)) 
   → (t : Nat) → motive t

/-!

## The Polymorphic List Data Type 

A small extension to the types we've defined so far 
will let us represent mathematical *lists* of objects
as terms of an inductive type. Given any type of list
elements, α, we can define a list of elements of that
type as either the empty list (which we'll call *nil*)
of as being constructed from two parts: an object of
type α (we'll call it the *head* of the list) and a
one-smaller *list* of objects of the same type. 
-/

/-!
### Constructors
-/

namespace cs2120

inductive List (α : Type) : Type 
| nil
| cons (head : α) (tail : List α) 

open List

end cs2120

def l0 := @List.nil Nat   -- [] : List Nat
def l1 := List.cons 0 l0  -- [0, []]
def l2 := List.cons 1 l1  -- [1, [0]]
def l3 := List.cons 2 l2  -- [2, [1, [0, []]]]

/-!
Lean provides convenient notations.

- [] is notation for the empty list
- :: is infix notation for List.cons
- [a1, a2, a3, ...] is for a1::a2::a3::...::nil
-/

#eval ([] : List Nat)
#eval 0::[]
#eval 3::2::1::0::[]
#eval [3,2,1,0]

/-!

### Elimination

Elimination is just like with the Doll and Nat 
types, by pattern matching, but now you have to
account for the additional element of each non-nil
term of type List α.
-/

def len {α : Type} : List α → Nat
| [] => 0
| _::t => 1 + len t

#reduce len []
#reduce len [3,2,1,0]
#reduce len (3::2::1::0::[] : List Nat) 

/-!
Exercise. Write a function polymorphic in one type,
α, that takes two arguments of type List α and returns
the result of appending the second list after the first.
Hint: try case analysis on the first list argument.   
-/

