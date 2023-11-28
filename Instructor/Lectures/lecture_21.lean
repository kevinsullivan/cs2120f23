import Mathlib.Init.Set

/-!

# Set Theory

A set is intuitively understood as a collection of objects.
Such a collection can be finite or infinite. For example, the
set of natural numbers less than five is finite but the set of
all natural numbers is infinite.

For our purposes set theory is best understood as just another
*algebraic structure*, like Boolean algebra or arithmetic. Set
theory has both objects (sets) and operations on them. Your main
task in this chapter is to understand set objects and operations
on them. The first section of this chapter explains how we define
sets in Lean. The second presents the major operations of set
theory.

A major concept running throughout this chapter is that set
theory is defined, at least in Lean, directly in terms of
underlying *logical* concepts. We will start with the idea
that a set is represented by a predicate. Each set operation
is then defined in terms of logic involving such predicates.
What you have to learn are thus (1) the concepts of set theory,
(2) how each one reduces directly to corresponding logic. To
prove propositions in set theory, you will thus simply prove
the corresponding underlying logical propositions.

We now turn to the *objects* of set theory, namely sets.
One we understand how sets are defined by predicates, we
will turn to the logical definitions of the *operations*
of set theory.

## Sets

In Lean, a set is represented by a *predicate*, one that is made
true by every member of the set, and not by any other values. We
call a predicate used to define a set a *membership* predicate.

### Membership Predicates

As examples, here are two *predicates* on natural numbers. The
first is true of a number if that number is even. The second
is true of a number if that number is small, defined as *being
equal to 0, *or* being equal to 1 *or*, ..., *or* being equal
to 4.* The first specifies the set of even numbers; the second,
a set of small natural numbers.
-/

def ev := λ n : Nat => n % 2 = 0
def small := λ n : Nat => n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4

/-!
Self test: What *proposition* is specified by the expression,
*small 1*? You should be able to answer this question without
seeing the following answer.

Answer: Plug in a *1* for each *n* in the definition of *small*
to get the answer. There are 5 places where the substitution has
to be made. Lean can tell you the answer.
-/

#reduce small 1

/-!
The result is *1 = 0 ∨ 1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4*. This
predicate is true, of course, because *1 = 1*, so *1* is seen
to be a member of the set that the predicate specifies. Similarly
applying the predicate to 3 or 4 yields true propositions, but
that doesn't work for 5, so 5 is not in the set that this predicate
specifies.
-/

/-!
To rigorously prove that 1 is in the set you prove the underlying
logical proposition, *1 = 0 ∨ 1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4*. A
proof of *set* membership thus reduces to a proof of an ordinary
logical proposition, in this case a disjunction. You already know
how to do that. Again a key insight to be taken from this chapter
is that set theory in Lean reduces to logic you already understand!

Continuing with our example, and as a reminder, let's prove the
proposition, *1 = 0 ∨ 1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4*. Start by
recalling that ∨ is is right associative, so what we really need
to prove is *(1 = 0) ∨ (1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4)*. It takes
just a little analysis to see that there is no proof of the left
side, *1 = 0*, but there *is* a proof of the right side. The right
side is true because 1 = 1. Our proof is thus by *or introduction*
on the right applied to a proof of the the *right*, applied to a
proof of the right side, (1 = 1) ∨ (1 = 2 ∨ 1 = 3 ∨ 1 = 4). Be
sure to see that using right introduction discards the left side
of the original proposition and requires a proof of the right. A
proof of it in turns is by or introduction on the left applied to
a proof of 1 = 1, which is by the reflexive property of equality.
In Lean, this idea can be expressed by rfl.

Practice: Give a formal proof that 1 satisfies *small*.
We advise you to use top-down, type-guided structured proof
development to complete this simple proof.
-/

example : small 1 := _

/-!
### Set Notation

There are several ways to denote a set of objects. Two that
you must understand because they are so commonly used in
mathematics are *display* and *set comprehension* notation.

#### Display Notation

To represent a finite set of objects, you can simply give
them in a comma-separated list between curly braces. The
set of small numbers from 0 to 4 inclusive is represented
in this way as *{ 0, 1, 2, 3, 4 }*.

Lean supports display notation as a shorthand for writing
a membership predicate. The corresponding predicate in this
case, computed by Lean, is *λ n => n = 0 ∨ n = 1 ∨ n = 2
∨ n = 3 ∨ n = 4*. In the following example, Lean doesn't
infer that the set type is Set Nat, so we have to tell it
so explicitly.
-/

def s1 : Set Nat := { 0, 1, 2, 3, 4 }
#reduce s1   -- sets are predicates in Lean

/-!

#### Set Comprehension Notation

Sets, including infinite sets, can also be specified
using *set comprehension* notation. Here's an example
using it to specify the same small set.
-/

def s2 : Set Nat := { n : Nat | n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4}

/-!
We pronounce the expression as *the set of values n of type Nat such
that n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4. The curly braces indicate
that we're defining a set. The *n : Nat* specifies is the argument to
the membership predicate. The vertical bar is read *such that*. And the
membership predicate is then written after it. We can easily check that
this expression means the same thing as the one using display notation.
Sets in Lean are truly represented by *logical predicates*.

Exercise: Assume there's a type of objects call Ball and a predicate,
Blue, on balls. Use set comprehension notation to specify the set of
blue balls.

Answer: { b : Ball | Blue b }.

Again, you can read this expression in English as *the set of all
balls, b, such that b is blue*.
-/
#reduce s2

/-!
### Type Homogeneity

The preceding example involved a set of natural numbers.
In Lean, such a set, being defined by a predicate on the
natural numbers, cannot contain elements that are not of
the natural number type. Sets in Lean are thus said to be
*homogeneous*. All elements are of the same type. This
makes sense, as sets are defined by predicates that take
arguments of fixed types.

A *heterogeneous* set, by contrast, can have members of
different types. Python supports heterogeneous sets. You
can have a set containing a number, a string, and a person.
The track in Python is that all objects actually have the
same *static* type, which is *Object*. In the end, even in
Python, sets are homogeneous in this sense.

In Lean, and in ordinary mathematics as well, sets are most
often assumed to be homogenous. In mathematical communication,
one will often hear such phrases as, *Let T denote the set of
natural numbers less than 5.* Notice that the element type is
made clear.

In support of all of this, Set, in Lean, is a type builder
polymorphic in the element type. The type of a set of natural
numbers is *Set Nat*, for example, while the type of a set of
strings is *Set String*.

The homogeneity of sets, in turn allows sets to be represented
by *membership predicates*. We represent a set of objects of some
type T as a *predicate, P : T → Prop*, such that *P* is true (has
a proof) for every value in the set and for no others. All of the
elements of such a set are thus necessarily of the same type: in
this case, T.

The following example shows that, in Lean, the even and small
predicates we've already defined can be assigned to variables
of type *Set Nat*. It type-checks! Sets truly are specified by
and equated with their membership predicates in Lean.
-/
def ev_set' : Set Nat := ev         -- ev is a predicate
def small_set' : Set Nat := small   -- small is too

/-!
It'd be unusual in mathematical writing however to define
sets in this style. Better would be to use either display or
set comprehension notation. Here are stylistically improved
definitions of our sets of even and small natural numbers.
We will use these definitions in running examples in the
rest of this chapter.
-/

def ev_set : Set Nat := { n : Nat | ev n }
def small_set : Set Nat := { n | small n }

/-!
The take-away is that, no matter one's choice of notation,
sets are truly represented in Lean by *logical* predicates.
The great news is that you already understand the logic so
learning set theory is largely reduced to learning the set
algebraic concepts (the objects and operations of set theory)
and in particular how each concept reduces to underlying logic.


## Set Theory Operations

We now turn to the operations and corresponding notations of
set theory. Along the way we'll introduce two special sets:
the *universal* set of objects of a given type, and the *empty*
set of objects of a given type. A universal set contains every
value of its member type. The empty set contains no values of
its member type.

### Membership

We've already seen that we can think of a predicate as defining
a set, and that a value is a member of a set if and only if it
satisfies the membership predicate.

That said, set theory comes with its own abstractions and notations.
For example, we usually think of a set as a *collection* of objects,
even when the set is specified by a logical membership *predicate*.
Similarly set theory gives us notation for special sets and all of
the operations of set theory.

As an example, the proposition that 1 is a member of small_set
would be written as *small_set 1* if we're thinking logically;
but in set theory we'd write this as *1 ∈ small_set*. We would
pronounce this proposition as *1 is a member of small_set*.

From now on you should try to interpret such an expression in
two ways. At the abstract level of set theory, it asserts that
1 is a member of the collection of elements making up small_set.
At a concrete, logical, level, it means that *small_set 1*, the
logical proposition that 1 satisfies the small_set predicate, is
true.

This proposition in turn has a proof, as we've seen. The very
same proof proves 1 ∈ small_set. All these notations mean the
same thing logically, but set theory notation encourages us to
think abstractly now in terms of sets, not logic.

Nevertheless, to construct proofs in set theory in Lean, you
must understand how the objects and operations in set theory
are defined in terms of, and reduce, to propositions in pure
logic. What you will have to prove are the underlying logical
propositions.

Here, for example, we *state* a proposition using set theory
notation, but the proof is of the underlying *or* proposition.
-/
example : 1 ∈ small_set' := Or.inr (Or.inl rfl)

/-!
The lesson is that when you look at an expression in set theory
you really must understand its underlying logical meaning, for
that is what you'll need to prove.

So we're now in a position to see the formal definition of the
membership operation on sets in Lean. In the Lean libraries, it
is def Mem (a : α) (s : Set α) : Prop : s a (where α is any type).
The notation ∈) reduces to corresponding logic, namely here to the
proposition obtained by applying the set membership predicate to
the argument, a. If the resulting proposition is true (witnessed
by a proof in Lean) then it's in the set otherwise it's now.
-/

/-!
Exercises.

(1) We expect that by now you can construct a proof
of a disjunction with several disjunctions. But practice is still
great and necessary. Try erasing the given answer and re-creating
it on your own. By *erase* we mean to replace the answer with
*_*. Then use top-down, type-guided refinement to derive a complete
proof in place of the *_*.
-/
example : 3 ∈ small_set := (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-!
(2) Prove that for any (t : T), t ∉ ∅. The proof
is by negation. You'll assume t ∈ ∅ and show that this
leads to a contradiction (a proof of False in this case).
-/

example (T : Type) (t : T) : t ∉ (∅ : Set T) := _


/-!
(3)) Prove the following. Remember t ∈ univ means univ t,
and univ t invariablly reduces to True.
-/

example (T : Type) (t : T) : t ∉ (∅ : Set T) := _

/-!
(4)) Prove 0 ∈ univ.

To start, reduce the set theory notation to logic, then prove
the logical proposition. We saw that *0 ∈ univ* reduces to
*univ 0*, and that *univ 0* in turn reduces to *True*. So all you
need to prove 0 ∈ univ is a proof of True. Go ahead. Note that
Lean infers that the element type is Nat from argument value, 0.
-/
example : 0 ∈ univ := _

/-!
(5) Prove the proposition that 3 is not
in the empty set of natural numbers
-/
example : 3 ∈ (∅ : Set Nat) := _  -- there's no proof

/-!
The proof is *by negation*. That means we assume that
3 ∈ ∅  and then show that that leads to a contradiction
(i.e., to a proof of false). The form of the proof is a
function, here after the :=, that assumes that it has a
proof, *h*, of the hypothesis that 3 is in the set. On
the right of the => a case analysis on the possible forms
of *h* reveals that there is no way h can be true, so by
false elimination the proof is complete.
-/
example : 3 ∉ (∅ : Set Nat) := _

/-!
### Take-Away

The take-away is that the set theory expression, x ∈ X,
simply means, and reduces to the proposition, that x
satisfies the membership predicate of the set X. To
prove x ∈ X, substitute x for the formal parameter in
the membership predicate (apply the predicate to x)
and prove the resulting proposition.
-/

/-!
### Two Special Sets

With membership notation under our belts, we can now better
present the concepts and notations of the universal and the
empty set of elements of a given type.
-/

/-!
#### Universal set

The universal set of a values of a given type is the set
of *all* values of that type. The membership predicate for
the *universal* set is thus true for every element of the
set. *True* is the (degenerate, parameterless) predicate
that satisfies this condition. It is true for any value,
so every value is in a set with True as its membership
predicate.

To be precise, the membership predicate for the universal
set of objects of any type *T*, is *λ (a : T) => True.*
When it is applied to any value, *t*, of type T, the result
is just the proposition, *True*, for which we always have
the proof, *True.intro*.

In Lean, the universal set of objects of a given type is
written as *univ*. The definition of *univ* is in Lean's
*Set* namespace, so you can use *univ* either by first opening
the *Set* namespace, or by writing *Set.univ*.
-/

open Set

#reduce univ        -- fun _a => True
#reduce univ 0      --           True
#reduce univ 123456 --           True

/-!
#### Empty set

The empty set of values of a given type is the set
containing *no* values of that type. It's membership
predicate is thus false for every value of the type.
Formally, the membership predicate for an empty set of
values of type T is *λ (t : T) => False*.

The predicate takes any value, *t*, ignores it, and
always returns the *proposition*, False.* The empty
set of values of a given type is often written as ∅.
It is pronounced as *the empty set (of values of type T)*.

Again we emphasize that set theory in Lean is built on and
corresponds directly with the logic you've been learning all
along. We've now seen that (1) sets are specified by membership
predicates; (2) the universal set is specified by the predicate
that is true for any value; (3) the empty set is specified by
the predicate that is false for any value; (4) the ∈ operation
builds the proposition that a given value satisfies the membership
predicate of a given set; (5) proving propositions in set theory
reduces to proving corresponding underlying logical propositions.
-/

/-!
At an abstract level, Set theory, like arithmetic, is a mathematical
system involving objects and operations on these objects. In arithmetic,
the objects are numbers and the operations are addition, multiplication,
etc.  In Boolean algebra, the objects are true and false and operations
include *and, or,* and *not*. In set theory, the objects are sets and
the operations include membership (∈), intersection (∩), union (∪),
difference (\) and more. We now turn to important operations on sets
beyond membership.
-/


/-!
### Intersection

Given a type, T, and two sets, s1 and s2, of type Set T, the
*intersection* of s1 and s2 is the set whose members are exactly
those values that are in both s1 *and* s2, by virtue of satisfying
both of their membership predicates. The intersection
of s1 and s2 is usually written as *s1 ∩ s2*.

In the Lean library, the intersection operation is defined as you
might expect: def inter (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∧ a ∈ s₂}.
Given two sets, their intersection is defined to be the set of values
(itself represented by a membership predicate satisfy the membership
predicates the first set *and* the second set.

The key take-away is that intersection corresponds to logical *and*
of the membership predicates. The similarity in notations reflects
this fact, with ∧ for logical and and ∩ for set intersection. The
following Lean commands illustrate this point.
-/

variable (T : Type) (s t : Set T)
#check s ∩ t    -- the intersection of sets is a set
#reduce s ∩ t   -- its membership predicate is formed using ∧

/-!
As another example, the intersection of our even (ev) and small sets,
corresponding to the conjunction of their membership predicates,
contains only the elements 0, 2, and 4, as these are the only values
that satisfy both the ev *and* small predicates.
-/

def even_and_small_set := ev_set ∩ small  -- intersection!
#reduce (0 ∈ even_and_small_set)  -- membership proposition

/-!
Exercise: Prove 6 ∈ even_and_small_set.
-/

/-!
Exercise: It's clear that *2 ∈ even_and_small_set*. But what
is a proof of it? A good first step is to determine what is
the underlying *logical* proposition that needs to be proved?
First understand what is the corresponding logical proposition
to be proved, then prove that. Here's the proposition. The left
side corresponds to the proposition that 2 is even, and the right
side that 2 is in the set of small natural numbers.
-/

#reduce 2 ∈ even_and_small_set

-- Use example to assert proposition and give proof here:

/-!
Exercises:

- What values are in the set, {1, 2, 3} ∩ {4, 5, 6}?
- For the following questions, assume that *prime* is a predicate on natural numbers true of a number, n, if and only if n is prime in the arithmetic sense; and that ev is our usual evenness predicate.
  - Define ep1 to be the set that is the intersection of the prime and even numbers. Use set comprehension notation.
  - Define ep2 to be the same set but now using display notation (listing the actual values in the set).
-/

-- Here:

/-!
### A Remark on Set Theory Notation

One place where meanings of predicates and sets differ in
Lean is in the availability of certain notations. Lean gives
us notations appropriate to treating even_and_small as just
a predicate, not a set, so set notation operations are not
provided in this case. For example, the *is member of set*
predicate, ∈, can't be used to with just a predicate. It's
meant for cases where the predicate is meant to represent a
mathematical set. Set operations and notations, such as ∈,
are provided to support the mathematical concepts involved
in *set theory*.
-/

#check 2 ∈ even_and_small     -- set notation doesn't work
#check 2 ∈ even_and_small_set -- set notation is enabled

/-!
### Union

Given two sets, s and t, the union of the sets, denoted as
s ∪ t, is the set of values that are in either s *or* t. The
membership predicate of s ∪ t is the disjunction of those of
the two sets. An object is a member when it satisfies either
the membership predicate of s *or* the membership predicate of
t.

In Lean, the formal definition of the union operation is given
as: def union (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∨ a ∈ s₂}.

As an example, we now define even_or_small_set as the *union* of
the even_set and small_set.
-/

def even_or_small_set := ev_set ∪ small_set

/-!
Now suppose we want to prove that 3 ∈ even_or_small_set. What
we have to do is prove the underlying logical proposition. We
can confirm what that proposition is using reduce.
-/

#reduce 3 ∈ even_or_small_set

/-!
Exercises. Give proofs as indicated. Remember to analyze the
set theoretic notations to determine the logical form of the
underlying membership proposition that you have to prove is
satisfied by a given value.
-/

example : 3 ∈ even_or_small_set := Or.inr _

example : 6 ∈ even_or_small_set := _

example : 7 ∉ ev_set ∪ small_set := _

/-!
### Set Complement
Given a set s of elements of type α, the complement of s,
denoted sᶜ, is *def compl (s : Set α) : Set α := {a | a ∉ s}.*
In other words, sᶜ is the set of elements of type α that are
*not* in s. So whereas intersection reduces to conjunction of
membership predicates, and union reduces to the disjunction of
membership predicates, the complement operation reduces to the
negation of the membership predicate of a set.
-/

variable (s : Set Nat)
#check sᶜ             -- notation not working in Lean4?
#reduce Set.compl s   -- apply Set.compl operation without notation


/-!
### Set Difference
-/

#reduce Set.diff

/-!
### Subset
-/

#reduce @Set.Subset

/-!
### Powerset
-/

#reduce @Set.powerset
