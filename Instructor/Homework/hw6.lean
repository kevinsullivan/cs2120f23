/-!
# Homework 6

The established rules apply. Do this work on your own.

This homework will test and strengthen your understanding
of inductive data types, including Nat and List α, and the
use of recursive functions to process and construct values
of such types.

The second part will test and develop your knowledge and
understanding of formal languages, and propositional logic,
(PL) in particular, including the syntax and semantics of
PL, and translations between formal statements in PL and
corresponding concrete English-language examples.
-/

/-! 
## Part 1: Inductive Types and Recursive Functions
-/

/-! 
### #1: Iterated Function Application 

Here are two functions, each of which takes a function,
*f*, as an argument, and an argument, *a*, to that function, 
and returns the result of applying *f* to *a* one or more
times. The first function just applies *f* to *a* once. The
second function applies *f* to *a* twice. Be sure you fully
understand these definitions before proceeding. 
-/

def apply {a : α} : (α → α) → α → α 
| f, a => f a

def apply_twice {a : α} : (α → α) → α → α 
| f, a => f (f a)

/-!
Your job now is to define a function, *apply_n*, that takes
a function, *f*, a natural number,  *n*, and an argument, 
*a*, and that returns the result of applying *f* to *a n* 
times. Define the result of applying *f* to *a* zero times
as just *a*. Hint: recursion on *n*. That is, you will have
two cases: where *n* is *0*; and where *n* is greater than 
*0*, and can thus be written as *(1 + n')* for some smaller
natural number, *n'*.
-/

-- Answer here

def apply_n {α : Type} : (α → α) → α → Nat → α  
| f, a, 0 => _
| f, a, (n' + 1) => _

-- Test cases: confirm that expectations are correct

-- apply Nat.succ to zero four times
#eval apply_n Nat.succ 0 4        -- expect 4

-- apply "double" to 2 four times
#eval apply_n (λ n => 2*n) 2 4    -- expect 32

-- apply "square" to 2 four times
#eval apply_n (λ n => n^2) 2 4    -- expect 65536


/-!
# A Short Introduction to Lists 

The polymorphic data type, List α, is used to
represent lists of values of any type, α. The 
List type builder provides two constructors: 
one to create and empty list of α values, and 
one to construct a new non-empty list from a
new element (head, of type α) and a one smaller
list (tail, of type List α). Here's how the List
type builder is defined (simplied just a tad).
-/

namespace cs2120

inductive List (α : Type): Type
| nil : List α
| cons (h : α) (t : List α) : List α

end cs2120

/-!
Lean defines three useful notations for creating
and destructuring lists.

- [] means List.nil
- h::t means cons h t
- [1, 2, 3] means the list, 1::[2,3]
  - which means 1::2::[3]
  - which means 1::2::3::[]
  - which means cons 1 (cons 2 (cons 3 nil))
-/

#check ([] : List Nat)
#check 1::[2,3]
#check [1,2,3]

/-!
You can use these notations when pattern 
matching to analyze arguments. Here we show
how this work by defining a function that
takes a list and returns *either* (using a
sum type) *unit* to represent the case where
there is no first element, or the value at
the head of the list.
-/

def first_elt : List Nat → Unit ⊕ Nat
| [] => Sum.inl Unit.unit
| h::_ => Sum.inr h

#reduce first_elt []    -- expect Sum.inl unit
#reduce first_elt [1,2] -- expect 1 (left)


/-! 
### #2: List length function

Lists are defined inductively in Lean. A list of
values of some type α is either the empty list of
α values, denoted [], or an α value followed by a
shorter list of α values, denoted *h::t*, where 
*h* (the *head* of the list) is a single value of
type α, and *t* is a shorter list of α values. 
The base case is of course the empty list. Define 
a function called *len* that takes a list of 
values of any type, α, and that returns the length
of the list.
-/

def len {α : Type} : List α → Nat
| _ => _
| h::t => _

#eval @len Nat []                   -- expect 0
#eval len [0,1,2]                   -- expect 3
#eval len ["I", "Love", "Logic!"]   -- expect 3


/-! 
### #3: Reduce a List of Bool to a Bool

Define a function that takes a list of Boolean 
values and that "reduces" it to a single Boolean
value, which it returns, where the return value
is true if all elements are true and otherwise
is false. Call your function *reduce_and*. 

Hint: the answer is the result of applying *and* 
to two arguments: (1) the first element, and (2) 
the result of recursively reducing the rest of the 
list. You will have to figure out what the return
value for the base case of an empty list needs to
be for your function to work in all cases. 
-/

def reduce_and : List Bool → Bool
| _ => _
| _ => and _ _

-- Test cases

#eval reduce_and [true]           -- expect true
#eval reduce_and [false]          -- expect false
#eval reduce_and [true, true]     -- expect true
#eval reduce_and [false, true]    -- expect false


/-! 
### #4 Negate a List of Booleans 

Define a function, call it (map_not) that takes a 
list of Boolean values and returns a list of Boolean
values, where each entry in the returned list is the
negation of the corresonding element in the given
list of Booleans. For example, *map_not [true, false]*
should return [false, true].
-/

def map_not : List Bool → List Bool 
| [] => []
| h::t => _   -- hint: use :: to construct answer

-- test cases
#eval map_not []              -- exect []
#eval map_not [true, false]   -- expect [false, true]

/-! 
### #5 List the First n Natural Numbers

Define a function called *countdown* that takes a 
natural number argument, *n*, and that returns a list 
of all the natural numbers from *n* to *0*, inclusive. 
-/

-- Your answer here



-- test cases
#eval countdown 0            -- expect [0]
#eval countdown 5            -- expect [5,4,3,2,1,0]


/-! 
### #6: List concatenation 

Suppose Lean didn't provide the List.append function,
denoted *++*. Write your own list append function. Call
it *concat*. For any type *α*, it takes two arguments of 
type *List α* and returns a result of type *List α,* the
result of appending the second list to the first. Hint:
do case analysis on the first argument, and think about
this function as an analog of natural number addition.
-/

-- Here

def concat {α : Type} : _
| [], m => _
| _, _ =>  _

-- Test cases

#eval concat [1,2,3] []   -- expect [1,2,3]
#eval concat [] [1,2,3]   -- expect [1,2,3]
#eval concat [1,2] [3,4]  -- expect [1,2,3,4]

/-!
### #7: Lift Element to List

Write a function, *pure'*, that takes a value, *a*, of any
type α, and that returns a value of type List α containing
just that one element.
-/

-- Here

#eval pure' "Hi"       -- expect ["Hi"]

/-!
### Challenge: List Reverse

Define a function, list_rev, that takes a list of values
of any type and that returns it in reverse order. Hint: you 
can't use :: with a single value on the right; it needs a
list on the right. Instead, consider using *concat*.
-/

-- Answer here:


/-!
## Part 2: Propositional Logic: Syntax and Semantics

Forthcoming as an update to this file.
-/
