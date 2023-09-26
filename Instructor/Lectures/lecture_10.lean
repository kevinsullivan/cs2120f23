/-! 
# Data Types: Recursive Types

You've seen that we use the keyword, *inductive*, 
to introduce new data types, but what does this word 
really mean?

## A Toy Example

To get to an answer, let's have a look at a traditional
child's toy: the nesting doll.

### Recursive Data

Such a *doll* comes in two forms: either it's a *solid*
(very inner) doll, or an outer *shell* with another *doll* 
inside it. In the second case, the doll inside can in turn be
either a solid doll or another shell with another doll inside
it. And that doll can be either a solid doll or a shell with
another doll inside. This kind of nesting can go on for any
finite number of shells. We can represent the structure of
such a doll as an inductive data type. We'll call it *doll*.
-/

inductive Doll : Type
| solid
| shell (d : Doll)

open Doll

/-!
We can now construct dolls of arbitrary depth, always starting 
with a solid doll and then iterating the application of shell
as many times as desired. It's important to understand that
there's no way to apply the *shell* constructor without first
having started with a *solid* value. On the other hand, once
you start with the *solid* doll, in principle you can apply
the *shell* constructor as many (finite number of) times as
you care to to build ever larger dolls.
-/
def d0 := solid
def d1 := shell d0
def d2 := shell d1
def d3 := shell d2

/-!
We could have written these definitions out showing
each application of shell, all the way down to the
solid doll.
-/

def d0' := solid
def d1' := shell solid
def d2' := shell (shell solid)
def d3' := shell (shell (shell solid))

/-!
To drive the point home, we can expand the definition
of d3 to see what term it really defines. We'll just keep
expanding the "inner" dolls until we reach the final
solid doll at the "bottom." That doll has no smaller one
as an argument and so can be expanded no further.

- d3 =
- shell d2 =
- shell (shell d1) =
- shell (shell (shell d0)) =
- shell (shell (shell solid))

The final term is the actual value of d3.
-/

/-!
### The Meaning of *Inductive*

Now you're seeing the meaning of the term, *inductive*.
It's a central idea in computer science: that we will often
want to be able to construct objects of some type, α from smaller
objects *of the same type*, ultimately bottoming out at a
*least* element of that type. We can also say that objects
of such a type have a recursive structure.
-/

/-!
### Exercise

Define a function, *inner : Doll → Doll.* When applied to any 
doll, *d*, if *d* is the *solid* doll then *inner* must return 
*solid*, otherwise, if *d* is a nested doll, then it must be 
of the form (shell d') for some doll, d', and in this case the
function should return d' 
-/

def inner: Doll → Doll
| solid => solid
| (shell d') => d'

#reduce inner d3    -- expect (shell (shell solid))
#reduce inner solid 

/-!
You would be correct to call *inner* an elimination rule for the
*Doll* type. If a function has to *use* a Doll given as an argument 
this is the basic pattern for *analyzing* it to determine what to 
do next. 
-/

/-!
### Recursive Functions

Now suppose we're given an arbitrary object of type *Doll*
and that we want to count how many layers deep it goes and
return that result as a natural number. For example, a solid
doll has zero levels of further nesting, so we'll define its
depth to be zero. To compute the depth of an arbitrary doll,
we'll function, *depth : Doll → Nat*. How can we implement
it?

Well, given any *(d : Doll)*, we have to analyze *d* to see
which case we're dealing with: *solid* or *shell d'* with *d'*
being the doll that figuratively *inside* the shell. If we 
find that *d* is *Doll.solid*, we return zero. In the other
case, if *d* is of the form (shell d'), then the answer is
clearly *1 + depth d'*. That is, it's 1 (for the outer shell)
plus whatever is the depth of the doll inside the shell. We
will call *solid* the base case and *shell d'* the recursive
case. 
-/

def depth : Doll → Nat 
| solid => 0                      -- *base case*
| shell d' => 1 + depth d'        -- recursive case

/-!
The *depth* function is *recursive* in the sense that it is
defined in terms of an application of itself to a smaller
value, *d'*, with knowledge that it cannot *loop* forever.
We can easily check to see that it seems to works.
-/
#eval depth d0
#eval depth d1
#eval depth d2
#eval depth d3

/-!
Now, it is worthwhile to convince yourself that the
evaluation of a recursve function application really
works, so here's how it works when to evaluate *depth 
d3*.

- depth (shell       (shell      (shell       solid)))
-          1 + depth (shell      (shell       solid))
-          1 +         1 + depth (shell       solid)
-          1 +         1 +          1 + depth solid
-          1 +         1 +          1 +         0
-          1 +         1 +          1
-          1 +         2
-          3
-/


/-!
### Recursive Thinking

Now that you see that it works, it's best to forget
about this kind of *unrolling* of the recursion! The 
key to really grasping the concept is to understand
that when writing you're writing the implementatation 
of a recusive function, such as *depth (shell d')*, you
can just *assume* that you already have the value of 
the answer for the next smaller argument. Here you 
can assume you already have the value of *(depth d').*
Once you really grasp this idea, it's easy to define 
the result: in this case it's just *1 + depth d'*. 

### There Must Be a Least Value

The one thing that must be true is that a recursive 
function will eventually reach a non-recursive, least,
or smallest, "base case" (here *solid*) after a finite
number of steps. 

In our doll example, that's assured by the nature of an 
inductive data definition. By the very definition of an
inductive data type, the set of values it defines is the
set of values that *generated* by any *finite* number of 
applications of the available constructors. To build a
doll you can only start from *solid* and then apply the
*shell* constructor a *finite* number of times. When you
compute *(depth d)* by recursion, you apply *depth* to a
one-smaller inner doll, *d'*, and you can only do this as 
many times as *shell* was applied to construct *d* before
you read the *solid* doll, at which point the computation
returns a final result. The recursion always terminates
after a finite number of steps. 

### Structural Recursion
We call such recursion "structural recursion." Lean
knows that *depth* is structurally recursive because
it can detect that you're calling *depth* recursively 
on a proper *sub-structure* of a given doll. And, as 
any doll can exist only because of a finite number
of applications of the shell constructor to a solid
doll, the depth function will eventually reach that
*solid* doll. At that point, the function will return
0 and the overall sum of all the 1's plus that final
0 will be returned.

### Lean Verifies Structural Recursions

Indeed, Lean insists that recursions terminate after
a finite number of steps. Because structural recursions
terminate by definition, Lean doesn't complain as long
as it can determine that a recursion is structural. If
it can't prove this fact it will reject a definition. 

Suppose, for example, that you inadvertently applied 
*depth* recursively not to the smaller inner doll, d', 
but to the given argument, *d*, instead. In this case, 
evalating *depth d* would evaluate *depth d* and that
would evaluate *depth d* and so on forever. Lean will
reject such a definition. Read the error message that
Lean produces for the following definition. 
-/

def bad_depth' : Doll → Nat
| d => bad_depth' d       -- not a structural recursion 

/-!
There's a deep reason Lean can't accept such a 
definition. Suppose it could. Then we could write
the following slight variant.
-/

def bad_depth : Doll → Empty    -- Lean rejects def
| d => bad_depth d 

#check (bad_depth d3)           -- Term of type Empty!!!
#reduce (bad_depth d3)          -- Function won't reduce

/-!
If Lean accepted this definition, then the application
term *(bad_depth d)* would be of type Empty, but there
can be no such term! We'd have a logical contradiction
and our logical universe would implode; false would be
true; and sensible reasoning would become impossible. 
-/

/-!
## The Nat Data Type

While the Doll datatype might seem somewhat irrelevant
except as a simple example, it's not. In fact, but for
the names we've used (Doll, solid, and shell), it *is*
identical to the definition of the Nat type. That is,
natural numbers are represented by nested terms, with
*Nat.zero* as the least value, and *Nat.succ (n' Nat)*
as the way to construct the next larger Nat value from
a given one. 
-/

-- Our own version of Lean's Nat data type
namespace cs2120  -- The definition of the Nat type

inductive Nat : Type
| zero 
| succ (n' : Nat)

/-!
We will and Lean does represent mathematical natural
numbers as terms of type Nat in the obvious way. For
example, we will take *Nat.zero* to represent the 
abstract number we write as 0, (Nat.succ Nat.zero) 
to represent 1, (Nat.succ (Nat.succ zero)) for 2, and
so forth.

Exercise: Define n0, n1, n2, and n3 to be the values
of type Nat that we'll take to represent the natural
numbers 0, 1, 2, and 3, respectively. 

Lean does us a favor by having standard Arabic numeral
notations for natural numbers built in. So as long as 
there's no ambiguity, Lean will interpret 0 to mean
Nat.zero, and will output Nat.zero as 0, etc. 
-/

-- Switch back to using Lean's definition of Nat
end cs2120 

/-!
Note: You can use certain Nat notations, such as *0* for 
*Nat.zero* and *n' + 1* for *Nat.succ n'* when pattern 
matching. An annoying detail is that *1 + n'* won't work
in place of *Nat.succ n'*. This is one of the few little
Lean notational details that you just have to remember.
-/

def n0 := Nat.zero
def n1 := Nat.succ n0
def n2 := Nat.succ n1
def n3 := Nat.succ n2

def is_zero'' : Nat → Bool  -- this works but is verbose
| Nat.zero => true
| (Nat.succ n') => false 

def is_zero' : Nat → Bool   
| 0 => true
| (1 + n') => false         -- (1 + n') not a valid pattern     

def is_Zero' : Nat → Bool   -- our preferred notation
| 0 => true                 -- 0 for Nat.zero
| n' + 1 => false           -- n' + 1 is a valid pattern    

/-!
### Exercises

#1: Write a function, pred: Nat → Nat, that takes an any
Nat, n, and, if n is zero, returns zero, otherwise returns
Nat that is one smaller than n. We call it the *predecessor*
of n, in contradistinction to the *successor* of n (n + 1).
Hint: Look at how you wrote *inner* for the *Doll* type. 
-/

def pred : Nat → Nat 
| 0 => 0
| (Nat.succ n') => n'   -- destructures nat>0 to (succ n')

-- Answer here

-- test cases
#reduce pred 3    -- expect 2
#reduce pred 0    -- expect 0

/-!
#2: Write a function, *mk_doll : Nat → Doll*, that takes
any natural number argument, *n*, and that returns a doll 
n shells deep. The verify using #reduce that (mk_doll 3)
returns the same doll as *d3*. 
-/

-- Answer here

def mk_doll : Nat → Doll 
| _ => _
| _ => _

-- test cases
#check mk_doll 3
#reduce mk_doll 3

/-!
#3: Write a function, *nat_eq : Nat → Nat → Bool*, that
takes any two natural numbers and that returns Boolean 
*true* if they're equal, and false otherwise. Hint: How
many cases do you need to consider?
-/

def nat_eq : Nat → Nat → Bool
| 0, 0 => true
| 0, n' + 1 => false
| n' + 1, 0 => false
| (n' + 1), (m' + 1) => nat_eq _ _

#eval nat_eq 6 5

/-!
#3: Write a function, *nat_le : Nat → Nat → Bool*, that
takes any two natural numbers and that returns Boolean 
*true* if the first value is less than or equal to the 
second, and false otherwise. Hint: The key to solving
this problem is to figure out the relevant cases, match 
on them, and then return the right result *in each case*.
-/

-- Here

def nat_le : Nat → Nat → Bool
| 0, _ => true
| (n' + 1), 0 => false
| (_), (_) => _

#eval nat_le 0 0    -- expect true
#eval nat_le 0 2    -- exect true
#eval nat_le 1 0    -- expect false
#eval nat_le 1 1    -- expect true
#eval nat_le 2 1    -- expect false
#eval nat_le 2 3    -- expect true

/-!

#4: Write a function nat_add : Nat → Nat → Nat, that 
takes two Nat values and returns the Nat representing
their sum. Method: You could do case analysis on either
argument, but, to be consistent with Lean's definitions,
do case analysis on the second (Nat) argument, returning
the right result in either case. 

The challenge is to rewrite the inductive case to one
employing structural recursion. Remember, you assume
you have (1) a successor constructor, *succ*, and (2)
a recursive solution for the sum in the case where the 
second argument to the recursive function application
is structurally smaller than that argument to nat_add.  
 -/

def add : Nat → Nat → Nat
| m, 0 => m
| m, (Nat.succ n') => _
