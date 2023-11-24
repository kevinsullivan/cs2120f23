/-!
# Quantifiers: Universal Generalization (∀)

Quantifiers are part of the syntax of predicate logic.
They allow one to assert that every object (∀) of some
type has some property, or that there exists (∃) (there is)
at least one (some) object of a given type with a specified
property. The syntax of such propositions is as follows:

- ∀ (x : T), P x
- ∃ (x : T), P x

The first proposition can be read as asserting that
every value *x* of type *T* satisfies predicate *P*.
Universal quantification is a generalized form of a
logical *and* operation: it is used to assert that
the first value of a type has some property, *and* so
does the second, *and* so does the third, through all
of them.

In this chapter we address the first case: of propositions
in the form of universal generalizations (using ∀). We will
cover existential quantification in the next chapter.

## Introduction Rule (How to Prove ∀ (x : T), P)

So what does a proof of a universal generalization,
*∀ (x : T), P x*, require? In the logic of Lean, it
requires one to show that a proof can be obtained
for each proposition, *P x,* for each possible value,
*x : T*. Being able to construct a proof of *P x* for
any value *x : T* shows *∀ (x : T), P x.* The way we
show this in Lean, in turn, is by defining a *function*
that, when given *any* *t : T*, returns a proof of *P t*
for that specific *t*. The existence of such a function
demonstrates that we can construct a proof of *P x* for
any *x : T*, showing that *every x : T* has property *P*.

There's another way to say it that you will hear in
less formal presentations. To show *∀ x, P x*, *assume*
you have an *arbitrary* value, *x,* and show that you
can prove *P x.* That will prove that all values of *x*
satisfy *P*.

TLDR: To prove *∀ (x : T), P x* show that there's a proof
of *P x* for every possible value of *x*. Do this in Lean
by defining a function that takes any value, *x : T* and
that returns a proof of *P x* for each such *x* value.
-/

/-!
### Example

Here's a trivial example. We assert that for every
natural number value, *n*, there is a proof of the
corresponding proposition, *True*. In this case the
resulting proposition doesn't depend on the value of
the argument, *n*. The proof of the generalization is
a function that takes any natural number, *n,* ignores
it, and returns a proof of *True*.
-/

example : ∀ (n : ℕ), True := fun n => True.intro

/-!
### Function Types and ∀ Propositions

We now see that the logical proposition, *∀ (n : Nat),
True*, is equivalent to the function type, Nat → True.
Given any natural number, *n*, such a function returns
a proof of (a value of type) True. We just gave such
a function (value/implementation), and *thereby gave
a proof of *∀ (n : ℕ), True*.
-/
#check ∀ (n : Nat), True  -- Literally Nat → True!

/-!
The function arrow, *X → Y* is indeed just a notation
for *∀ (x : X), Y*, the special case of a dependent
function type where the return type, here *Y*, doesn't
depend on (vary with) the argument value.
-/

/-!
### Examples

To further illustrate the equivalence of function
arrow and this special case of ∀, here we define
the natural number squaring function, declaring
its type using ∀ rather than →. But then when we
#check it's type, Lean reports it as *Nat → Nat*,
using its default notation, →, for this type.
-/

def square : ∀ (n : Nat), Nat := λ n => n^2
#check (square)   -- Nat → Nat
#reduce square 5  -- 25


/-!
This next example shows that a proof of *∀ (f :
False), False* is literally a function of type
False → False. Given any proof, *f*, of *False*,
it's ok to "return a value of type False" because
there are *no* cases in which that will ever have
to be done.
-/

def fimpf : ∀ (f : False), False := λ f => nomatch f
#check (fimpf)  -- a value/proof of type False → False

/-!
To drive it home, a proof of a universal generalization,
*∀ (x : T), P x*, is a function that, when given any value,
*x : T*, as an argument, returns a proof (value) of (type)
*P x*. That functions are always *total* in Lean means that
there will then be a proof of *P x* for *every* *x : T*.
-/

variable
  (Dog : Type)
  (Blue : Dog → Prop)

/-!
A formal statement in predicate logic that all
dogs are blue.
-/
#check ∀ (n : Nat), Nat
#check ∀ (d : Dog), Blue d


/-!
## Dependent Function Types

Note that the return *type* of this function, *P x*,
depends on the particular *value, x : T*, to which
the function might be applied in any given instance.
For each value, *x*, *P x* is a different proposition.
Each value of *x* thus gives rise to a different type,
one for each value of *x*.

As we've discussed, a proof of *∀ (x : T), P x* is
formalized as a function, taking any argument, *x : T*,
and returning a formal proof for the proposition, *P x*,
which is to say a *value* of type *P x*.

We see now that in Lean *∀ (x : T), P x* is a function
type; but it's a function type of a very special kind,
in that its return type, *P x*, depends on the value
of the given argument, *x*. We thus say *∀ (x : T), P x*
is a *dependent* function type.


An ordinary function in Lean is a special case where
the return type is independent of the argument value.
For example, the type *Bool* doesn't depend on argument
values. You can see the difference between dependent
and ordinary function values in the following examples.

First, here's an ordinary function type, equivalent to
*Nat → Bool*. Note that the return type, Bool, is fixed
and does not vary with the value of the argument, *n*.
-/

#check ∀ (n : Nat), Bool  -- function type, Nat → Bool

/-!
For the second example, we'll go back to our favorite
simple predicate, *evenness*, for natural numbers. We
will then explain why *∀ (n : Nat), is_even n* is not
an ordinary, but a dependent, function type.

To start, here's our *is_even* predicate again. It
returns a different proposition (logical type) for
each value of *n*.
-/

def is_even : Nat → Prop := fun n => n % 2 = 0

-- Each of these propositions is a different type in Lean
#check is_even 0
#check is_even 1
#check is_even 2
#check is_even 3

/-!
We can now write a dependent function type: for each
value of *n* it promises to return a value of *type,*
*is_even n*. We won't be able to implement it because
it's not true, so there's no proof of it. But that's not
the point here. The point is that this function type has
a different return type for each argument *value*.
-/
#check ∀ (n : Nat), is_even n

/-!
## Totality of Functions

The concept of dependent function types is central to
Lean and related languages. Dependent types are how
the quantifiers of predicate logic are formalized in
Lean.

When you put dependent function types together with
the fact that functions are total in Lean, you end up
with a crucial piece of the Curry Howard bridge between
computation and logic. That a proof of *∀ (x : T), P x*
is a *total* function, from *any* value, *x*, to a proof
of *P x*, is what makes the function a proof that *all*
argument values satisfy the predicate, *P*.
-/

/-!
## A Little Bit of Lean: Declaring variables

The *variable* command in Lean introduces an identifier
and its type without assigning a value. This idea should
be familiar from your programming in languages like Java.
In Java, you can declare the type of a variable without
giving it a value, as in the following example:

```java
String s;
```
-/

/-!
In Lean, one can similarly declare variables without
initial values. Here's how we'd translate that Java
example into Lean.
-/

variable (s : String)

/-!
Having declared such a variable, we can then use it in
all the ways Lean allows, except of course reducing it
to a value, since no value is yet bound to it. Here we
use the #check command to see it's type.
-/
#check s    -- String

/-!
You can declare several variables at a time, as
parenthesized type declarations following the
*variable* keyword in Lean.

The following example shows multiple variables being
declared. The entire example could all be written on one
line but we find it much easier to read when each of
the declarations is on its own line.

In particular, here we we declare the following variables.

- *T* is an arbitrary type
- *P* to be a one-argument predicate on values of type *T*
- fa is a proof of the dependent type, *∀ (x : T), P x*
- *t* is an arbitrary value of type *T*.
-/
namespace decls
variable
  (T : Type)
  (P : T → Prop)
  (fa : ∀ (x : T), P x)
  (t : T)

/-!
## Elimination: Using ∀ Proofs: Universal Specialization
Having declared these variables, we now see how to *use*
a proof of a universal generalization, such as *fa*: you
can *apply* it to any value, *t : T* to get a proof that *t*
in particular satisfies (has property) *P*. Applying *fa*
to *t* yields a proof of *P t*. Logicians call this rule
of inference *universal specialization*.
-/

-- fa proves that all α satisfy P
#check fa   -- ∀ (x : α), P x

-- Therefore *t* in particular satisfies P
-- We obtain a proof by simply applying fa to t
#check fa t -- P t
end decls

/-!
Observe that we're doing logical reasoning having
only specified the types of all of our variables.
-/

/-!
Here's a less symbolic and abstract example. Suppose we
know (have a proof) that *All dogs are blue.* We can
call such a proof, *all_dogs_blue*. Suppose we also know
that that *Iris is a dog.* We can conclude that *Iris*
is blue. We can formalize and analyze such a *logical
scenario* in Lean using variable declarations, as above.

Here's the formal rendition of our blue dog story.
-/

namespace bluedog
variable
  (Dog : Type)                            -- There are dogs
  (Iris : Dog)                            -- Iris is one
  (Blue : Dog → Prop)                     -- The property of being blue
  (all_dogs_blue : ∀ (d : Dog), Blue d)   -- Proof all dogs are blue

/-!
Having set up the example, we can now perform
the operation of universal specialization to show
formally that Iris is blue.
-/
#check all_dogs_blue Iris -- universal specialization
end bluedog

/-!
The blue dog example (if all dogs are blue and Iris is a
dog then Iris is blue) illustrates the application of the
rule  of logical reasoning that the Greek philosopher,
Aristotle, called *modus ponens*. It's oftentaught using
an analogous story about Socrates. It goes like this. (1)
All people are mortal. (2) Socrates is a person. (3) Thus
Socrates is mortal.

The crucial result to understand is the final check, which
produces *everyone_is_mortal Socrates : Mortal Socrates*. In
English, this says that  *everyone_is_mortal Socrates* is a
proof of the proposition, *Mortal Socrates*, that Socrates
is mortal under the given assumptions.
-/

namespace socrates
variable
  (Person : Type)
  (Socrates : Person)
  (Mortal : Person → Prop)
  (everyone_is_mortal : ∀ (p : Person), Mortal p )
#check everyone_is_mortal Socrates
end socrates

/-!
That brings us to the conclusion of this section
on universal generalization and specialization. Key
things to remember are as follows:

- Universal generalizations are dependent function types
- To prove a universal generalization (introduction rule for ∀ propositions), define such a dependently typed function
- To use a proof of a universal generalization (elimination), apply such a function (proof()) to a specific value (universal specialization)
-/
