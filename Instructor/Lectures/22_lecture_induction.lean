/-!
# Induction: Recursive Functions, Proofs by Induction

This chapter introduces induction axioms and their uses.
Each inductive type has a corresponding induction axiom.
Such an axiom enables the from of total functions values
of any inductively defined (not function) type, *α,* to
result of some result type, *β*. The arguments to the
induction axiom are computations of β values, one for
each *constructor case* for *a : α*.


By applying an induction axiom for a type, α, to arguments
of the right types (in turn dictated by the definition of α),
one provides one computation to handle each case of argument
constructor for α, thereby defining a result for *every*
value of type α.


## Understanding Induction

They key idea is that an induction function for a
type, α, takes one argument for each α constructor.
These arguments specify how to compute a result for
each case. Induction is really just a functiont that
computes total function on values of any inductive
type *by case analysis* an application of the right
computation for any given case.

Induction can be understood as a higher-order function
that takes one *result-returning* computation (value
or function) for each case and puts them together into
a *total* function that computes an answer for *any*
value of a given type.


There are two major uses of induction. The first is to
define ordinary functions from data to data of types in
*Type u*. The second is to compute functions from data
to proofs of propositions in *Prop*. Induction works
the same either way.

In this chapter we'll start by looking at induction to
construct ordinary data handling functions. In the second
subsection we'll present the construction of proof values
by applying exactly the same induction principle.


## Defining Data-Producing Functions by Induction

In this section, we will focus first and mainly on
using induction to construct functions that take
*Nat*-valued arguments and produce computable data
(rather than proof) values as results. At the end
of this section, we'll see briefly how the idea
generalizes from *Nat* induction to induction on
Lists of values.

As the Nat type has two constructors, the induction
axiom/principle/function for the *Nat* type takes two
arguments. We will call them *base* and *step*. The
first will specify what to return in the case of a
*Nat* argument being *zero*. The second will specify
how to construct a result for any non-zero argument,
*n = (n' + 1)*, from *n'* and the result for *n'*.

We'll start by analyzing the factorial function as
an example of a function defined *by induction*. You
already know Lean syntax for defining functions by
cases. The induction principle explains that syntax
as *notation* for defining functions *by induction*.

### Case Study: The Factorial Function

Suppose we need a function that, given any natural
number as an argument returns a corresponding data
value. In particular, consider as an example the
*factorial* function, *fact,* that takes a natural
number, n, and returns *n factorial (n!).*

You already know how to define such a by cases: by
giving a result-computing rule is for each of two
possible forms of a natural number, corresponding to
the two *Nat* constructors: (1) *if n = zero* then
return 1*, else (2) destructuring *n = n' + 1* then
*n (written as n' + 1) \* fact n'.
-/

def fact : (n : Nat) → Nat
| 0 => 1
| (n' + 1) => (n' + 1) * fact n'

/-!
It's easy to write test cases proved automatically by
Eq.refl.
-/

example : fact 1 = 1    := rfl   -- no failure detected
example : fact 5 = 120  := rfl   -- no failure detected

/-!
The rule for the case where *n = Nat.zero* is easy: the
answer is 1. The answer for *n = 0* is the starting point
for constructing an answer for any value of n.

With an answer for *n = 0* we now turn to what we will
call the *step function*. The key idea is that if, from
the value of n' and the answer for n' we can compute the
answer for *n' + 1*, then we can construct an answer for
any value of *n* by starting with *fact 0 = 1* and then
applying the step function *n* times.

As an example, if we have that n' = 4 and fact n' = 24 we
can compute *fact 5* as *(n' + 1) * fact 4 = 5 * 24 = 120.*

From *n'* and *fact n'* the rule for the non-zero argument
case computes the answer for *(n' + 1)* by *stepping up*
from *n'* and an answer for *n'* Note that both of these
values are needed to compute the value for *n = (n' + 1)*.
-/

-- Base case is starting point for inductive construction
def fact_0 := 1                 -- base case, n = 0
-- Inductive case iterated n times to compute result for n
def fact_1 := (0 + 1) * fact_0  -- n = 1, n' = 0, fact 0 = 1
def fact_2 := (1 + 1) * fact_1  -- n = 2, n' = 1, fact 1 = 1
def fact_3 := (2 + 1) * fact_2  -- n = 3, n' = 2, fact 2 = 2
def fact_4 := (3 + 1) * fact_3  -- n = 4, n' = 3, fact 3 = 6
def fact_5 := (4 + 1) * fact_4  -- n = 5, n' = 4, fact 4 = 24


-- test cases all pass
example : fact 0 = 1 := rfl
example : fact 1 = 1 := rfl
example : fact 2 = 2 := rfl
example : fact 3 = 6 := rfl
example : fact 4 = 24 := rfl
example : fact 5 = 120 := rfl

/-!
### Separate Result Computations For Each Case For *n*

It's now just a small jump to implementing separate result
computations for the cases for *n*. We need a computation
to return the result when *n = 0*, and we need a computation
to return a result for positive *n, *destructured as *n' + 1,
given *n'* and the result for *n'*.

#### Base Case (Nat.zero)

The first computation is just a constant, *fact_base*,
representing the return value for the case where n = 0*,
namely, 1. We formalize the answer in this case as a simple
constant definition.
-/

def fact_base := 1

/-!

#### Inductive Case (Nat.succ n')

The second computation, a function, takes two natural
numbers, (1) a natural number value for *n'*, and (2)
the return result for *n' (fact n')*, and returns the
result for *n*. Here, the step function applied to *n'*
and *fact n'*, returns *fact n = (n' + 1) * fact n'*.
-/

def fact_step (n' fact_n' : Nat) := (n' + 1) * fact_n'
#check (fact_step)

/-!
The crucial step is to see that with these two functions,
we can compute *fact n* for *any* natural number, *n*, by
computing the answer for *0* and then applying the *step*
function to the values of *n* (e.g., 0) and *fact n* to get
a result for *n + 1*.
-/

def fact_0' := fact_base             -- 0!
def fact_1' := fact_step 0 fact_0    -- computes 1! from 0, 0!
def fact_2' := fact_step 1 fact_1    -- computes 2! from 1 and 1!
def fact_3' := fact_step 2 fact_2    -- computes 3! from 2 and 2!
def fact_4' := fact_step 3 fact_3    -- computes 4! from 3 and 3!
def fact_5' := fact_step 4 fact_4    -- computes 5! from 4 and 4!

-- test cases: it's working
example : fact_0' = 1 := rfl
example : fact_1' = 1 := rfl
example : fact_2' = 2 := rfl
example : fact_3' = 6 := rfl
example : fact_4' = 24 := rfl
example : fact_5' = 120 := rfl

/-!
What we see again here that we can construct
the value of *n* factorial for *any* natural
number, *n*, by starting with the answer for 0,
and then applying the step function *n* times.

The only remaining problem is that we have to
write out all the intermediate steps to get from
an answer for *0* to an answer for any given *n*.

An induction principle gets us out of such a
jam. To the induction *principle* for *Nat*,
you give these two computations as arguments,
*base* and *step*, and you get a function back
that takes *any* Nat *n*, and gives an answer
for *n*.
-/

/-!
To see point more clearly, let's quickly review
the induction axiom for *Nat*. We see it again as
a higher-order function.
-/

#check @Nat.rec
/-
@Nat.rec :
  {motive : Nat → Sort u_1} →
  motive Nat.zero →
  ((n' : Nat) → motive n' → motive (Nat.succ n')) →
  (n : Nat) → motive n
-/


/-!
The first argument, *motive,* is a function that,
for any given *Nat* value, *n*, returns, for that
value of *n*, the return type of the function that
is to be constructed. The motive function is thus
*dependently typed*.

For ordinary functions, from one type of data to
another, the return type will be constant (always
the same). For example, the return type for the
*factorial* function is *Nat* for any value of *n*.

Later in this chapter we'll see that we can also
construct *proofs of propositions* inductively. In
this scenario, each value of *n* will result in a
different proposition to be proved. As propositions
are types in Lean, the type of proof needed for *n*
will depend on *n*.

The second (first explicit) argument to *Nat.rec*
is defined to be of type *motive 0*, which is *Nat*.
This is the argument where one provides a computation
(a constant) that specifies the value of the factorial
function for *n = 0*.

The third (second explicit) argument is where one
provides the step function. *Nat.rec* specifies that
the type of the step function is *Nat → Nat → Nat*,
where the second two *Nat* elements of this type are
derived by applying *motive* to a *Nat* value.

When then function is used, the first *Nat* value
passed to it will be some *n'.* The second will
be the answer for *n'*. And the return result will
be the desired result, *factorial (n' + 1)*. It will
be obtained by applying the step function *(n' + 1)*
times to the base answer for *0*.

The fourth argument, *n*, is the argument to the
constructed (factorial) function. If we provide
only the first three arguments (the first implicit),
we will end up with a function then, when applied to
(n : Nat), returns the value, *n!*.
-/

--     this term is the factorial function      arg
#check (Nat.rec fact_0 fact_step : Nat → Nat)    0
#reduce (Nat.rec fact_0 fact_step : Nat → Nat)   0
example : (Nat.rec fact_0 fact_step 0) = 1 := rfl
#reduce   (Nat.rec fact_0 fact_step : Nat → Nat) 5
example : Nat.rec fact_0 fact_step 5 = 120 := rfl


/-!
In the preceding examples, we showed that induction does
compute these functions and they can then be applied to
arguments to return expected results. A detail regarding
the current state of Lean 4 is that it can't generate the
code needed for partial evaluation of *Nat.rec*, so for
example, you can't yet assign a function computed using
induction to a variable unless you mark the definition
as non-computable. Then you can't apply it.
-/

def bad : Nat → Nat := Nat.rec fact_0 fact_step
noncomputable def ok : Nat → Nat := Nat.rec fact_0 fact_step

/-!
The *types* of *base* and *step* (*Nat* and *Nat →
Nat → Nat* respectively) are of course the same for all
applications of induction. The details of *base* and
*step* (such as whether *base* is 0 or 1) determine the
behavior of function that the induction axiom returns.

For exampe, we just constructed the factorial function
by applying induction to *fact_base* and *fact_step*,
which we defined as *1* and *λ n' f_n' => (n'+1) * f_n'*,
as these are the base and step cases for the factorial
function.
-/

/-!
Exercise: Define the functions, *sum_base* and *sum_step*
so that applying induction to these values returns the
function that computes the *sum* of the natural numbers
from 0 to a given value, *n*.
-/

def sum_base := 0
def sum_step := λ n' sn' => (n'+1) + sn'
example : ((Nat.rec sum_base sum_step) : Nat → Nat) 10 = 55 := rfl
example : ((Nat.rec 0 (λ n' sn' => (n'+1) + sn')) : Nat → Nat) 10 = 55 := rfl
#reduce ((Nat.rec sum_base sum_step) : Nat → Nat) 10


#check ((Nat.rec  sum_base  sum_step) : Nat → Nat)
#check ((Nat.rec fact_base fact_step) : Nat → Nat)

/-!
You now understand how recursive functions are built.
It should also make sense that the notation we learned
earlier for writing recursive functions is really just
that: nice notation for *recursors* (induction axioms)
in Lean. Here's sum_up all dressed up.
-/

def sum_up : Nat → Nat
| 0 => 0                            -- base
| (n' + 1) => (n' + 1) + sum_up n'  -- step


/-!
/-!
## Nat.zero is a left zero for Nat.add

protected def Nat.add : (@& Nat) → (@& Nat) → Nat
  | a, Nat.zero   => a
  | a, Nat.succ b => Nat.succ (Nat.add a b)
-/

#check Nat.add 5 0
#check Nat.add 0 5
#reduce Nat.add 0 5

-- easy
example : ∀ (n : Nat), Nat.add n 0 = n := by
simp [Nat.add]

-- Challenge
example : ∀ (n : Nat), Nat.add 0 n = n := by
simp [Nat.add]
_     -- NOPE


def left_zero (n : Nat) := Nat.add 0 n = n

def goal := ∀ n, left_zero n


-- Let's see if there's an answer by induction

#reduce left_zero 0

-- base machine
def add_base : left_zero 0 := rfl

-- step machine
example (n' : Nat) (pf : left_zero n') : left_zero (Nat.add n' 1) := by
simp [Nat.add]
simp [left_zero]


def factorial_step_function (n' ans_n' : Nat) := (n'+1) * ans_n'
#eval factorial_step_function 5 120
#eval factorial_step_function 3 6


/-!
Clearly if one picks any value (n : Nat), one
can construct an answer for *fact n* by starting
with the answer for 0 then *iterating* the rule
for building the next result n more times.

Of course we don't want to have to write a lot
of iterative code like this, so we use recursion.
For a non-zero argument, (n' + 1), we combine n'
and an answer for n' *computed by recursion*. We
can be sure the recursion will terminate because
there is a minimum value of n' corresponding to
the base case.
-/

/-!
Now suppose that what we want is a proof of
some proposition, *P n*, for any value of n. The
same idea applies. If we have a proof for 0, and
if we have a way to produce a proof for n = n' + 1
whenever we know n' and have an answer for n', then
we can produce a proof for *any* value of n.
-/


/-!
Nat.rec.{u}
  {motive : Nat → Sort u}
  (zero : motive Nat.zero)
  (succ : (n' : Nat) → motive n' → motive (Nat.succ n'))
  (t : Nat) :
  motive t
-/

#check Nat.rec

/-!
Now let's look at what's going on here to see if it
might generalize. The case analysis is central. What
we have are two cases, flowing from the definition of
Nat: it has two constructors, zero and succ n'. What
the cases provide in our definition of fact' are two
machines. The first machine spits out the result for
zero. The second machine takes two inputs, n, and the
answer for n-1, *fact n'*, and it returns the answer
for n. Read that as many times as necessary for it to
make sense.

Does this pattern recur across recursive functions
of this kind? Here's another. It computes the sum of
the numbers from 0 to n for any n.
-/

def sum' : Nat → Nat
| 0 => 0
| (n' + 1) => (n' + 1) + sum' n'

-- auto-checked test cases
example : sum' 5 = 15 := rfl

/-!
Let's evaluate the expresion, *fact 3*, according to
these rules.

- fact 3
- 3 * (fact 2)
- 3 * (2 * (fact 1))
- 3 * (2 * (1 * (fact 0)))
- 3 * (2 * (1 * 1))
- 3 * (2 * 1)
- 3 * 2
- 6
-/

def base_sum := 0
def step_sum (n' ans_n') := (n' + 1) + ans_n'

def foo : Nat → Nat := Nat.rec base_sum step_sum

/-!


@Nat.rec : {motive : Nat → Sort u_1} →
  motive Nat.zero → ((n : Nat) → motive n → motive (Nat.succ n)) → (t : Nat) → motive t
-/
