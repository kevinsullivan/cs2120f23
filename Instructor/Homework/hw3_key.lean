/-!
# Homework #3

Near final DRAFT. 

## Overview and Rules

The purpose of this homework is to strengthen your
understanding of function composition and of enumerated
and product data types. 

The collaboration rule for this homework is that
you may *not* collaborate. You can ask friends and
colleagues to help you understand material in the
class notes, but you may not discuss any aspect
of this homework itself with anyone other than one
of the instructors or TAs. Why? Because *you* need
to learn this material to pass the exam to come.
-/

/-!
## Problem #1

Define a function of the following polymorphic type:
{α β γ : Type} → (β → γ) → (α → β) → (α → γ). Call it
*funkom*. After the implicit type arguments it should
take two function arguments and return a function as
a result. 
-/

-- Answer below

def funkom : {α β γ : Type} → (β → γ) → (α → β) → (α → γ)
| α, β, γ, g, f => fun (a : α) => (g (f a))

/-!
We'll implement a function of this type using what
we call top-down type-guided structured programming.
-/

/-!
Here's the procedure we followed when going over the HW.
- introduce the name of the function with def
- specify the *type* of the function after a :
- use pattern matching bind names to unnamed arguments
- "stub out" the entire return value using _
- see the *context* for what you have and what you need
  - some arbitrary (unspecified) type value, α, β, and γ
  - an arbitrary function value, *g : β → γ*
  - an arbitrary function value, *f : α → β*
  - an arbitrary value, *a* of type *α*
- the challenge: construct a *γ* given what you've assumed you have 
- incrementally expand the implementation, from the outside to in
  - I need a γ value; I can get it by applying *g* to a β value
  - I need a β value; I can get that by applying *f* to an α
  - I have an α in 
-/

/-! 
## Problem #2

Define a function of the following polymorphic type:
{α β : Type} → (a : α) → (b : β) → α × β. Call it mkop.
-/

-- Answer below

def mkop : {α β : Type} → (a : α) → (b : β) → α × β
| α, β, a, b => (a,b) -- Prod.mk a b

/-!
We recommend the same top-down, type-guided structured
programming approach. Some people would simply call it
top-down refinement, or top-down programming. It's an
essential strategy that every great programmer knows. 
-/

/-! 
## Problem #3

Define a function of the following polymorphic type:
{α β : Type} → α × β → α. Call it op_left.
-/

-- Answer below

def op_left : {α β : Type} → α × β → α
| α, β, p => Prod.fst p

-- Hint: Use top-down structured programming!


/-! 
## Problem #4

Define a function of the following polymorphic type:
{α β : Type} → α × β → β. Call it op_right.
-/

-- Answer below

-- Hint: Use top-down structured programming

def op_right {α β : Type} : α × β → β 
| p => match p with | (_, b) => b


/-! 
## Problem #5

Define a data type called *Day*, the values of which
are the names of the seven days of the week: *sunday,
monday,* etc. 
-/

inductive Day : Type
|sunday
|monday
|tuesday
|wednesday
|thursday
|friday
|saturday

open Day

#check sunday

/-!
Some days are work days and some days are play
days. Define a data type, *kind*, with two values,
*work* and *play*.
-/

inductive kind : Type
| work
| play

open kind

/-!
Now define a function, *day2kind*, that takes a *day*
as an argument and returns the *kind* of day it is as
a result. Specify *day2kind* so that weekdays (monday
through friday) are *work* days and weekend days are
*play* days.
-/

def day2kind : Day → kind 
| sunday => play
| saturday => play
| _ => work

#reduce day2kind thursday

/-!
Next, define a data type, *reward*, with two values,
*money* and *health*.
-/

inductive reward : Type
| money
| health

open reward

/-!
Now define a function, *kind2reward*, from *kind* to 
*reward* where *reward work* is *money* and *reward play* 
is *health*.
-/

def kind2reward : kind → reward
| work => money
| play => health

/-!
Finally, use your *funkom* function to produce a new
function that takes a day and returns the corresponding
reward. Call it *day2reward*.
-/

def day2reward := funkom kind2reward day2kind 

#reduce day2reward tuesday
#reduce day2reward saturday

/-!
Include test cases using #reduce to show that the reward
from each weekday is *money* and the reward from a weekend
day is *health*.
-/

/-!
## Problem #6

### A. 
Consider the outputs of the following #check commands. 
-/

#check Nat × Nat × Nat
#check Nat × (Nat × Nat)
#check (Nat × Nat) × Nat

#check (1,(2,3))
#check ((1,2),3)

/-!
Is × left associative or right associative? Briefly explain
how you reached your answer.

Answer here: 

### B.
Define a function, *triple*, of the following type:
{ α β γ : Type } → α → β → γ → (α × β × γ)  
-/

-- Here:

def triple : { α β γ : Type } → α → β → γ → (α × β × γ)
| α, β, γ, a, b , y => (a,(b,y)) -- Prod.mk a (Prod.mk b y)

-- Hints: (1) put in parens for clarity; (2) use TDSP.

/-!
### C.
Define three functions, call them *first*, *second*, 
and *third*, each of which takes any such triple as
an argument and that returns, respectively, its first,
second, or third elements.
-/

-- Here

def second { α β γ : Type } :  α × β × γ → β
| (_,b,_) => b

-- Ok, this one takes a small leap of imagination

/-!
### D.
Write three test cases using #eval to show that when 
you apply each of these "elimination" functions to a
triple (that you can make up) it returns the correct
element of that triple.  
-/

-- Here:

/-!
### E.
Use #check to check the type of a term. that you make 
up, of type (Nat × String) × Bool. The challenge here
is to write a term of that type. 
-/




