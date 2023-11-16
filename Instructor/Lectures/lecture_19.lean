/-!
# Quantifiers

Quantifiers are part of the syntax of predicate logic. They allow one
to assert that every object (∀) of some type has some property, or that
there exists (∃) (there is) at least one object of a given type with a
specified property. The syntax of such propositions is as follows:

- ∀ (x : T), P x
- ∃ (x : T), P x

## Universal Quantification

The first proposition can be read as asserting that
every value *x* of type *T* satisfies predicate *P*.
Universal quantification is a generalized form of a
logical *and* operation: it is used to assert that
the first value of a type has some property, *and* so
does the second, *and* so does the third, through all
of them.

### Introduction Rule (How to Prove ∀ (x : T), P)

So what does a proof of a universal generalization,
*∀ (x : T), P x*, require? In the logic of Lean, it
requires one to show that a proof can be obtained
for each proposition, *P x,* for each possible value,
*x : T*. Being able to construct a proof of *P x* for
any value *x : T* shows *∀ (x : T), P x.*

The way we show this in Lean is by defining a *function*
that, when given *any* *t : T*, returns a proof of *P t*
for that specific *t*.

There's another way to say it that you will hear in
less formal presentations. To show *∀ x, P x*, *assume*
you have an *arbitrary* value, *x,* and show that you
can prove *P x.* That proves that all *x* satisfy *P*.
-/

/-!
### Examples: Proving ∀ Propositions

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

### Dependent Function Types

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

We see now that *∀ (x : T), P x* is a function type,
but of a special kind: it's a type of function whose
return type depends on the value of any given argument.

The special case of an ordinary function is one where
the return types does *not* vary with argument values.
For example, the type *Bool* doesn't depend on argument
values. You can see the difference between dependent
and ordinary function values in the following examples.

First, here's an ordinary function type, equivalent to
*Nat → Bool*.
-/

#check ∀ (n : Nat), Bool  -- function type, Nat → Bool

/-!
For the second example, we'll go back to our favorite
simple *evenness* predicate for natural numbers.
-/

def is_even : Nat → Prop := fun n => n % 2 = 0

/-!
Each distinct value of *n* gives rise to a different
propositions, which is to say, to a different *type*.
-/
#check is_even 0
#check is_even 1
#check is_even 2
#check is_even 3

/-!
We can now write a dependent function type: for each
value of *n* it promises to return a value of *type,*
*is_even n*. We won't be able to implement it because
it's not true, so there's no proof of it. This is an
uninhabited *dependent* function type.
-/
#check ∀ (n : Nat), is_even n

/-!
### On Totality of Functions in Dependent Type Theory

The concept of dependent function types is central to
Lean and related languages. When you put it together
with the totality of functions you end up with part
of the Curry Howard bridge between computation and
logic. A proof of a proposition, *∀ (x : T), P x*, is
a *total* (dependent) function from *any* value, *x*,
of type, *T*, to a proof of *P x* (to a value of this
type). The totality of such a function shows there's
a proof of *P x* for *every* value *x : T*.
-/

/-!
### A Little Lean: Declaring variables

The *variable* command in Lean introduces an identifier
and its type without assigning a value. You can then use
the declared objects in further expressions.


In the following example (which could all be written on one
line), we declare *T* to be a type; *P* to be a one-argument
predicate on values of type *T*; fa to be a proof of *∀ (x : T),
P x*; and *t* to be a value of type *T*.
-/
namespace decls
variable
  (T : Type)
  (P : T → Prop)
  (fa : ∀ (x : T), P x)
  (t : T)

/-!
We enclose
-/
/-!
### The Elimination Rule: Universal Specialization
Having declared these variables, we now see in a generalized
setting how to *use* a proof of a universal generalization:
you *apply* it to any value, *t*, of type *T* to obtain a proof
that that *particular* value, *t*, satisfies *P*. Applying *fa*
to *t* yields a proof of *P t*. Logicians call this rule of
inference *universal specialization*.
-/

#check fa   -- ∀ (x : α), P x
#check fa t -- P t
end decls


/-!
Here's a less symbolic and abstract example. Suppose we know
(have a proof) that *All dogs are blue.* Suppose we also know
that that *Iris is a dog.* Then we can conclude that *Iris* is
blue. We can formalize such natural scenarios in the logic of
Lean using simple type and variable declarations in Lean.
-/

namespace bluedog
variable
  (Dog : Type)                            -- There are dogs
  (Iris : Dog)                            -- Iris is one
  (Blue : Dog → Prop)                     -- The property of being blue
  (all_dogs_blue : ∀ (d : Dog), Blue d)   -- Proof all dogs are blue

#check all_dogs_blue Iris -- universal specialization: Iris is Blue
end bluedog

/-!
Aristotle's famous rule of reasoning, *modus ponens*,
is often taught using a story about Socrates. It goes
like this. (1) All people are mortal. (2) Socrates is
a person. (3) Therefore Socrates is mortal.

Homework #1: Formalize that argument here, in the style
of the last two examples.
-/

-- HERE

namespace socrates
variable
  (Person : Type)
  (Socrates : Person)
  (Mortal : Person → Prop)
  (everyone_is_mortal : ∀ (p : Person), Mortal p )
#check everyone_is_mortal Socrates
end socrates

/-!
## Existential Quantification

The existential operator, *∃* is used to construct
propositions of the form, *∃ (x : T), P x*, which we
read as asserting that there is some (at least one)
value of type, *T*, that satisfies predicate, *P*.
-/

/-!
### Introduction Rule

In the *constructive* logic of Lean, a proof of
a proposition, *∃ (x : T), P x*, is an ordered pair.
The first element of such a pair is a specific value,
*w : T* that we claim has property P. We call this value
a *witness*. The second element of the pair is a proof
that *w* actually has property *P* (a proof of *P x*).

The introduction rule is called *Exists.intro* taking
a value, *x*, and a proof of *P x* as its arguments.
Lean provides ⟨ _, _ ⟩ as a notation for Exists.intro.
-/

def four_even' : ∃ (n : Nat), is_even n := Exists.intro 4 rfl
def four_even : ∃ (n : Nat), is_even n := ⟨ 4, rfl ⟩

/-!
Here the witness is *4* and *rfl* in this context yields a
proof of *0 = 0*. We'll learn more about equality shortly.
-/

/-!
### Constructive Logic

The term *constructive* here means that to prove that
something with a particular property exists, you have
to exhibit a particular value along with a proof that
that value has that property. Similarly a constructive
proof of an *or* proposition, *X ∨ ¬X*, requires either
a proof of *X* or a proof of *¬X*, whereas in classical
logic one assumes as an axiom that *X ∨ ¬X* is true and
has a proof.
-/

/-!
### Elimination Rules

Suppose you have a proof of a proposition, *∃ (x : T), P x*.
That is, suppose you have *pf : ∃ (x : T), P x* in your
context. How can you *use* such a proof? Here's the key idea:
if you know that *∃ (x : T), P x*, then you can deduce two
facts: (1) there is some object, *(w : T)* (here we give it
a name, *w*), for which (2) there is a proof, we can give it
a name, *pw*, of *P w*. The elimination rule gives us these
objects to work with.

The easiest way to apply elimination is by pattern matching,
as in the following example. It shows that if there exists a
number that's true and even, then there's a natural number
that's even. Note that after matching, we have *some* number,
*w* and some proof *pf* to work with to construct the proof
that's required.
-/

open bluedog
def ex1 : (∃ (n : Nat), True ∧ is_even n) → (∃ (f : Nat), is_even f)
| Exists.intro w pf => Exists.intro w pf.2


/-!
Exercises:
-/

/-!
Formalize and prove the proposition that if there's
someone everyone loves, then everyone loves someone.
-/

variable
  (Person : Type)
  (Loves : Person → Person → Prop)

-- Here
example : (∃ (i : Person), (∀ (p : Person), Loves p i)) →
          (∀ (p : Person), (∃ (i : Person), Loves p i))
| Exists.intro w elw => fun (p : Person) => Exists.intro w (elw p)
