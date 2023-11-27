import Mathlib.Init.Set
/-!

# Set Theory

For our purposes set theory is best understood as just another
mathematical structure, like arithmetic with natural numbers, or
propositional logic with Boolean truth values. Now the objects
are sets of elements of a specified types (akin to numbers) and
operation such as set intersection and set union (analogous to
arithmetic operations).

In turn, for our purposes, we will define and represent any set
by its *membership predicate*. The key idea is that the members,
or elements, of the specified set are exacty all and only those
objects of the given type that satisfy the membership predicate.
In the degenerate case where the predicate has no arguments,
membership of any object depends only on whether the proposition
(degenerate predicate) is true or not independent of the object.

As examples, here are two predicates on natural numbers. The
first is true if its argument is even. The second is true if
its argument is small, defined as "being equal to 0, or equal
to 1 or, ..., or equal to 4."

## Review: Predicates
-/
def ev := λ n : Nat => n % 2 = 0
def small := λ n : Nat => n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4

/-!
Remember, predicates are to be understood here as functions
that take parameters and output propositions that, in general,
are about those parameters.

EXERCISE: What proposition is specified by the expression,
*small 1*? This is the application of the *small* predicate to
*1*. Answer: Just plug in *1* for *n* on the right hand side
of the definition of *small*. There are 5 places where the
substitution will be made. Figure out the answer before you
check your understanding with the following reduction.
-/

#reduce small 1

/-!
The result is *1 = 0 ∨ 1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4*. We
can now ask for a *proof* of such a proposition as usual in
Lean. Here we use *example* to avoid having to give a proof
(that Lean will check for us) a name.

The proposition, *1 = 0 ∨ 1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4*, is
clearly true, namely because 1 = 1. The first step to proving
it formally is to recall that ∨ is right associative. We need
to build a proof of *1 = 0 ∨ (1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4)*.

It takes just a little analysis to see that there is no proof
of the left side, *1 = 0*, but there is a proof of the right
side, because its left side is true, because 1 = 1. Now we just
have to use "the API of constructive predicate logic" to write
the code needed to build it. Try to figure it out yourself
before reading any further.

Our proof is a proof is by or introduction applied to a proof
of the the right hand side of the proposition. That proof is
in turn a proof of the left hand side of the right hand side
of the original proposition: namely the proposition, 1 = 1.
The proof of that is by appeal, using *rfl* in Lean, to the
reflexive property of equality: *anything* is equal to itself.

PRACTICE: Stub out the proof by replacing everything after the
*:=* with an *_*, then derive the answer again yourself. Start
by replacing the *_* with *Or.inr _*. More generally, practice
top-down, type-guided, structured reasoning to complete this
simple proof.
-/

example : small 1 := Or.inr (Or.inl rfl)

/-!
## Sets

Sets are ordinarily understood as collections of objects.
For example, you could talk about the set of people who are
members of UVa's famous (to be) Lean Club. If you pick any
person, they either are or are not Lean Club members.

We can talk similarly about set of naturals numbers: for
example, the set containing all and only the natural numbers
that are less than five. This set is written {0, 1, 2, 3, 4}
using what is called *set display notation.* Display notation
is a comma-separated enumeration of the members of the set all
within a pair of curly braces. The Lean libraraies support set
display notation.
-/

example : Set Nat := { 0, 1, 2, 3, 4 }

/-!
### Homogeneity

The preceding example involved a set of natural numbers.
In Lean, such a set, being defined by a predicate on the
natural numbers, cannot contain elements that are not of
the natural number type. Sets in Lean are *homogeneous*.

In a *homogeneous* set, all members are of a single type.
In a *heterogeneous* set, there can be members of multiple
types. Python supports heterogeneous sets (but only because
the static type of every value is the same: just Object);
so in the end, even in Python, sets are homogeneous in this
sense.

In Lean, and in ordinary mathematics as well, sets are most
often assumed to be homogenous. In mathematical communication,
one will often hear such phrases as, *Let T denote the set of
natural numbers less than 5.* Notice that the element type is
made clear.

In support of all of this, Set, in Lean, is a type builder
polymorphic in the element type. The type of a set of natural
numbers is *Set Nat*, for example, while the type of a set of
strings is *Set String*.

### Membership Predicates
The homogeneity of sets, in turn allows sets to be represented
by their *membership predicates*. We represent a set of objects
of some type T as a *predicate, P* (of type *T → Prop* in Lean),
in such a way that *P* is true (has a proof) for every and only
the values that are in the set.

The following example shows that, in Lean, the two predicates
we've already defined can be assigned to variables of type *Set
Nat*. That type-checks! Sets are specied by and equated with their
membership predicates in Lean. In other words, every predicate on
values of some type, *T*, can be interpreted as specifying the set
of all values that satisfy it, and no other values. The take-away
is that in Lean sets are represented *logically*: by predicates.
-/
def ev_set' : Set Nat := ev         -- ev is a predicate, yet, a Set!
def small_set' : Set Nat := small   -- small is too, and yet, a Set!

/-!
Having made these definitions, we can then use *set theory*
notation to write assertions, such as the claim that 1 is a
member of small_set'. The infix notation for asserting that a
value is in a set is ∈. For example, *1 ∈ small_set'*, asserts
that 1 is in this set.

A crucial idea that you should understand confidently now is
that this expressions means (desugars to) *small_set' 1*. This
is the proposition obtained by applying the small_set' predicate
to 1 to obtain the resulting proposition. This expression in turn
simply means *small 1*. This proposition in turn has a proof, as
we've seen, given here again. The fact that the proofs are all
the same here reflects the fact that all these notations really
mean the same thing.
-/
example : 1 ∈ small_set' := Or.inr (Or.inl rfl)

/-!
### Set Comprehension Notation

*Set comprehension notation* reflects the foregoing analysis.
To specify the set of objects, of some type, T, that satisfy
some predicate *P*, one writes *{ t : T | P t }*. We pronounce
this expression as *the set of values, t, of type T such that
P t*, or *the set of objects of type T that satisfy P*. Lean
supports set comprehension notation. As examples, here are the
two sets of our running example.
-/


def ev_set : Set Nat := { n : Nat | ev n }
def small_set : Set Nat := { n | small n }

/-!
As in display notation, we use curly braces around the expression
of the members. Here, however, instead of listing the members, we
use comprehension notation. The space inside the braces is split by
a vertical bar. To the left, the name of a potential member and its
types are introduced (we leave Lean to infer the type in the second
example). To the right is the predicate that determines whether any
given value is a member of the set or not. It is if it satisfies the
predicate and is not otherwise.
-/

/-!
We can now state interesting propositions in set theory using
standard mathematical notation. Here we give the same example
as above but using standard set theory notation to express both
sets and proposition about 1 being a member of *small_set*.
-/

example : 1 ∈ small_set
  := Or.inr (Or.inl rfl)

example : 1 ∈ { n | small n }
  := Or.inr (Or.inl rfl)



/-!
Practice exercise. We expect that by now you can construct a proof
of a disjunction with several disjunctions. But practice is still
great and necessary. Try erasing the given answers and re-creating
them on your own. By *erase* we mean to replace the answers with
*_*. Then use top-down, type-guided refinement to derive a complete
proof.
-/
example : small 3 := Or.inr (Or.inr ( Or.inr (Or.inl rfl)))
example : small_set 3 := Or.inr (Or.inr ( Or.inr (Or.inl rfl)))
example : 3 ∈ small_set := (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-!
### Special Sets
-/

/-!
#### Universal set

The universal set of a values of a given type is the set
of *all* values of that type. The membership predicate for
this *universal* set is the proposition, *True*. It is true
for any value, so every value is taken to be a member of the
corresponding set.

To be precise, the membership predicate for the universal
set of objects of any type *T*, is *λ (a : T) => True.*
When itis applied to any value, *t*, of type T, the result
is just the proposition, *True*, for which we always have
the proof, *True.intro*.

In Lean, the universal set of objects of a given type is
written as *univ*. It is at bottom just the universal, or
always true, membership predicate.

The definition of *univ* is within the *Set* namespace from
Lean's mathematics library. You can use *univ* either by
first opening the *Set* namespace, or by writing *Set.univ*.
-/

open Set

#reduce univ        -- fun _a => True
#reduce univ 0      --           True
#reduce univ 123456 --           True

/-!
Here's an easy exercise. We just saw that *0 ∈ univ* means
*univ 0* (that zero satisfies the membership predicate), and
that *univ 0* reduces to *True*. So all you need to complete
the following example is to provide a proof of True. Go ahead.
Note that Lean infers that the element type is Nat from argument
value, 0.
-/
example : 0 ∈ univ := _

/-!
#### Empty set

The empty set of values of a given type is the set
containing *no* values of that type. It's membership
predicate is thus false for every value of the type.
Formally, it's *λ a => False*. The predicate takes
argument, *a*, ignores it, and always returns the
*proposition*, False.* The empty set of values of
a given type is often written as ∅. It is pronounced
as *the empty set (of values of type T)*.
-/

#reduce (∅ : Set Nat)             -- fun x => False
#reduce 3 ∈ (∅ : Set Nat)         --          False
example : 3 ∈ (∅ : Set Nat) := _  -- there's no proof

/-!
On the other hand, it *is true* that three is *not in*
the empty set. There's also a standard notation for *not
in*. It's ∉. The expression s ∉ T is pronounced as *the
value, s, is not in the set, T*. So the proposition here
is that 3 ∉ ∅. This expression desugars to ¬(3 ∈ ∅). It
in turn reduces to (3 ∈ ∅) → False.

The proof is *by negation*. That means We show that
assuming that it is in the empty set enables us to draw
a contradiction. That is the key idea: to prove ¬P, show
that assuming a proof of *P* enables the construction of
a proof of false False, and from that, conclude ¬P. A
proof of ¬P *is* a proof of *P → False* in Lean, which
is simply a function that takes an assumed proof of P
and derives a proof of False. As we've seen, existence of
such a function rules out the possibility that there are
any proofs of P, enabling us to conclude ¬P.

The following proof that 3 is not in the empty set shows
an example. To prove it, show that assuming that 3 *is*
in this set enables a derivation of a contradiction. The
form of the proof is a function, here after the :=, that
assumes that it has a proof, *h*, of the hypothesis that
3 is in the set. On the right of the => is the function
definition. It does a case analysis on the possible forms
of *h*, and in fact Lean can tell that there are none, so
the proof is complete.
-/
example : 3 ∉ (∅ : Set Nat) := λ h => nomatch h

/-!
One of the take-away messages of this chapter is that
set theory in Lean is built on and corresponds directly
with the logical theory you've been learning all along.

Sets are specified by membership predicates. The universal
set is specified by the predicate that is true for any value.
The empty set is specified by the predicate that is false for
any value. Sets in between are specified by more complex
membership predicates. Indeed, we can now use the abstract
and highly expressive language of predicate logic, as defined
in Lean, to specify all manner of deeply interesting sets,
-/

/-!
## Set Operations

Set theory, like arithmetic, is a mathematical system involving
objects and operations involving these objects. In arithmetic,
the objects are numbers and the operations include addition and
multiplication. In set theory, the objects are sets and operations
on sets are defined in terms of logical operations, such as *and,
or,* and *not*, on their set membership predicates. We now cover
the most important operations on sets.

### Intersection

Given a type, T, and two sets, s1 and s2, of type Set T, the
*intersection* of s1 and s2 is the set whose members are exactly
those values that are in both s1 and s2, by virtue of satisfying
both of their respective membership predicates. The intersection
of s1 and s2 is usually written as *s1 ∩ s2*.

The power of this style of reasoning is that we can form complex
and meaningful sets, qua membership predicates, inductively, by
composing smaller sets using these operations.

As an example, the intersection of our even (ev) and small (less
than 5) sets, corresponding again to the conjunction of their
membership predicates, contains only the elements 0, 2, and 4,
as these are the only values that are (have the properties of
being) both even *and* small.

Here's an example where we define the even_and_small predicate
as the (predicate logic) conjunction of the even (ev) and small
predicates. Study this example closely enough that you see how
we define more complex predicates in terms of simpler ones that
we already have.

-/
def even_and_small (n : Nat) : Prop := ev n ∧ small n

#check (even_and_small)
-- even_and_small : Nat → Prop

#reduce (even_and_small 0)
-- 0 = 0 ∧ (0 = 0 ∨ 0 = 1 ∨ 0 = 2 ∨ 0 = 3 ∨ 0 = 4)

/-!
Given this more complex membership predicate, it's easy
to define values declared to be of type Set Nat. Here we
do so in two ways, both using *set comprehension* notation.
The first example uses the even_and_small predicate by name,
while in the second example, even_and_small is unfolded to
(its definition), *ev n ∧ small n*.
-/

def even_and_small_set : Set Nat := { n | even_and_small n}
def even_and_small_set' : Set Nat := { n | ev n ∧ small n}

/-!
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

#check 2 ∈ even_and_small     -- set notation no work
#check 2 ∈ even_and_small_set -- yay for set notation

/-!
The concept you will really need to grasp to understand
our presentation of set theory (in the logic of Lean) is
that it directly mirrors underlying logic: predicates are
used to define sets, and operations involving sets reflect
underlying logical operators from predicate logic.

It's important to have a firm understanding of the details
of the correspondence between set and logical objects and
operations, especially when trying to prove propositions
expressed in set theory terms. You have to understand how
set theory notation is defined in terms of logic because
you'll need to use proof techniques to prove the logical
propositions that expressions in set theory desugar to.

Let's consider a concrete example. It's intuitively clear
that *2 ∈ even_and_small_set*. That is to say, that this
proposition is true. But what is a proof of it?

To answer that question, you must understand that we've
defined the set of natural numbers less than 5 in terms
of the predicate, *n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4.*

A proof of *2 ∈ even_and_small_set* is thus a proof of the
proposition obtained by substituting the argument, 2, for
the argument: *2 = 0 ∨ 2 = 1 ∨ 2 = 2 ∨ 2 = 3 ∨ 2 = 4.* A
proof of 2 ∈ even_and_small_set is thus literally a proof
of this disjunction. Of course you already know how to
prove a disjunction: choose which side to give a proof of
(left or right) and then give a proof of it. Also recall
that ∨ is right associative.
-/

example : 2 ∈ even_and_small_set := ⟨rfl , Or.inr (Or.inr (Or.inl rfl))⟩

/-!
Set Theory Notation for Intersection Operation

In set theory, we define the intersection of two sets
as having as its member all and only the values that are
members of both sets. Intersection is thus taken as a
binary operation on sets, taking two set arguments and
yielding a set result. As noted above, the set theory
notation is the binary infix operator, ∩, and it can
now be understood as returning a predicate that defines
the set of objects satisfying the membership predicates
of both of its argument sets.
-/
def even_and_small_set'' := ev_set ∩ small_set

/-!
#### Exercises

- What values are in the set, {1, 2, 3} ∩ {4, 5, 6}?
- For the following questions, assume that *prime* is a predicate on natural numbers true of a number, n, if and only if n is prime in the arithmetic sense; and that ev is our usual evenness predicate.
  - Define ep1 to be the set that is the intersection of the prime and even numbers. Use set comprehension notation.
  - Define ep2 to be the same set but now using display notation (listing the actual values in the set).
-/

/-!
### Union

Given two sets, S and T, the intersection, S ∩ T, is the
set of values that are in both S *and* T. By contrast, the
values in the *union,* S ∪ T, are those that are in either
set. We represent the union of S and T as the predicate that
is true of a value, n, when it satisfies either the membership
predicate of S *or* the membership predicate of T. A value is
in the union of two input sets if it's in either of the sets
to begin with.

We start by defining even_or_small as a *predicate* that is
satisfied by any natural number that satisfies either the *ev*
or the *small* predicate.
-/

def even_or_small := λ (n : Nat) => ev n ∨ small n

/-!
For example, we can compute the proposition that 3 is even or
small by applying the predicate to the particular value, 3.
-/

#reduce even_or_small 3

/-!
We can also now use the predicate to define a *set* (with supporting
set theory notation in Lean) using set comprehension notation. Here
is the set using the even_or_small predicate directly, followed by
the equivalent definition where even_or_small is applied to produce
the underlying disjunctive predicate, *n ∈ ev_set ∨ n ∈ small_set*.
-/

def even_or_small_set' := { n : Nat | even_or_small n}
def even_or_small_set := { n : Nat | n ∈ ev_set ∨ n ∈ small_set}

/-!
With a bonafide set object we can now use set theory notation.
Here for example we analyze the proposition that three is a
member of *even_or_small_set*. It's true not because it's even
but it *is* small, and the union contains all values that satisfy
either of the membership predicates of the input sets. Here's the
logical form of the proposition that three is in even_or_small_set.
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
