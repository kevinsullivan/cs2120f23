import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation


/-!
# Set Theory

A set is intuitively understood as a collection of objects.
Such a collection can be finite or infinite. For example, the
set of natural numbers less than five is finite but the set of
all natural numbers is infinite.

Like Boolean algebra or arithmetic, set theory has both objects
(sets, in the case) and operations on them. Your main aims in this
chapter are to (1) understand the language of sets and operations
on them in the abstract, (2) understand how sets and set operations
are represented in predicate logic (and in Lean), (3) understand
how to prove propositions about sets by proving their underlying
logical propositions.

The first section of introduces sets and how they are defined
as predicates in Lean. The second presents the major operations
of set theory, and along the way explains the logic underpinning
each set theory operation.

We now turn to the *objects* of set theory, namely sets.
One we understand how sets are defined by predicates, we
will turn to the logical definitions of the *operations*
of set theory.

## Sets

In Lean, a set is represented by a *predicate*, one that is made
true by every member of the set, and not by any other values. We
call a predicate used to define a set a *membership* predicate.

You can see the actual definition of *Set* in Lean by going to
its definition. Right click on Set and select *go to definition*.

What you'll find is *def Set (α : Type u) := α → Prop*. In other
words, the type, Set α, in Lean, really is just the type, α → Prop.
A set truly *is* represented directly by a predicate in this sense.

### Membership Predicates

Let's start by building on our understanding of predicates.
Here are two *predicates* on natural numbers. The first is true
of even numbers. The second is true of any number that is small,
where that is defined as the number *being equal to 0, *or* being
equal to 1 *or*, ..., *or* being equal to 4.* The first predicate
can be understood as specifying the set of even numbers; the second
predicate, a set of small numbers.
-/

def ev := λ n : Nat => n % 2 = 0
def small := λ n : Nat => n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4

/-!
Self test: What *proposition* is specified by the expression,
*small 1*? You should be able to answer this question without
seeing the following answer.

Answer: Plug in a *1* for each *n* in the definition of *small*
to get the answer. There are 5 places where the substitution has
to be made. Lean can tell you the answer. Study it until you see
that this predicate is true of all and only the numbers from 0 to
4 (inclusive).
-/

#reduce small 1

/-!
The result is *1 = 0 ∨ 1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4*. This
proposition is true, of course, because *1 = 1*. So *1* is proved
to be a member of the set that the predicate specifies. Similarly
applying the predicate to 3 or 4 will yield true propositions; but
that doesn't work for 5, so 5 is not in the set that this predicate
specifies.
-/

/-!
To formally prove that 1 is in the set, you prove the underlying
logical proposition, *1 = 0 ∨ 1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4*. A
proof of *set* membership thus reduces to a proof of an ordinary
logical proposition, in this case a disjunction. Again an insight
to be taken from this chapter is that set theory in Lean reduces
to correspondinglogic you already understand and know how to deal
with.

As a reminder, let's prove *1 = 0 ∨ 1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4*.

First, recall that ∨ is is right associative, so what we need to
prove is *(1 = 0) ∨ (1 = 1 ∨ 1 = 2 ∨ 1 = 3 ∨ 1 = 4)*. It takes
just a little analysis to see that there is no proof of the left
side, *1 = 0*, but there *is* a proof of the right side. The right
side is true because 1 = 1. Our proof is thus by *or introduction*
on the right applied to a proof of the *right* side, which we can
now slightly rewrite as (1 = 1) ∨ (1 = 2 ∨ 1 = 3 ∨ 1 = 4).

Be sure to see that using right introduction discards the left side
of the original proposition and requires only a proof of the right.
A proof of it, in turn, is by or introduction on the left applied to
a proof of 1 = 1. That proof is by the reflexive property of equality
(it's always true that anything equals itself). This idea is expressed
in Lean using *rfl*.

Exercise: Give a formal proof that 1 satisfies the *small*
predicate. We advise you to use top-down, type-guided structured
proof development to complete this simple proof. We give you the
or introduction on the right to start.
-/

example : small 1 := (Or.inr (_))

/-!
### Set Theory Notation

In the language of set theory, there are two especially
common notations for represeting sets. They are *display*
and *set comprehension* notation.

#### Display Notation

To represent a finite set of objects in mathematical writing,
you can give a comma-separated list of members between curly
braces. The set of small numbers (0 to 4) can be represented
in this way as *{ 0, 1, 2, 3, 4 }*. Sometimes we will want to
give a set a name, as in, *let s = { 0, 1, 2, 3, 4 }*, or
*let s be the set, { 0, 1, 2, 3, 4 }.*

Lean supports display notation as a set theory notation.
One is still just definining a membership predicate, but
it looks like the math you'll see in innumerable books and
articles.

The corresponding predicate in this case, computed by Lean,
is *λ n => n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4*. In the
following example, Lean doesn't infer that the set type is
Set Nat, so we have to tell it so explicitly.
-/

def s1 : Set Nat := { 0, 1, 2, 3, 4 }
#reduce s1   -- the predicate that represents this set

/-!
#### Set Comprehension Notation

Sets can also be specified using what is called *set
comprehension* notation. Here's an example using it to
specify the same small set.
-/

def s2 : Set Nat := { n : Nat | n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 }
/-!
We pronounce the expression (to the right of the := of course) as
*the set of values, n, of type Nat, such that n = 0 ∨ n = 1 ∨ n = 2 ∨
n = 3 ∨ n = 4. The curly braces indicate that we're defining a set. The
*n : Nat* specifies the set of set members. The vertical bar is read
*such that*, or *satisfying the constraint that*. And the membership
predicate is then written out.

You can check that this set, s2, has the same membership predicate as s1.
-/

#reduce s2

/-!
Example: Assume there's a type of objects call Ball and a predicate,
Striped, on balls. Use set comprehension notation to specify the set of
striped balls. Answer: { b : Ball | Striped b }. Read this expression
in English as *the set of all balls, b, such that b is striped*, or
more concisely and naturally simply as *the set of all striped balls*.
-/

/-!
### Aside On Homogeneity

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
true, and that you can construct a proof of that.

The very same proof proves 1 ∈ small_set. All these notations mean
the same thing, but set theory notation encourages us to think more
abstractly: in terms of sets (collections), not predicates, per se.

Nevertheless, to construct proofs in set theory in Lean, you
must understand how the objects and operations in set theory
are defined in terms of, and reduce, to propositions in pure
logic. What you will have to prove are the underlying logical
propositions.

Here, for example, we *state* a proposition using set theory
notation, but the proof is of the underlying *or* proposition.
-/

#check 1 ∈ small_set      -- membership proposition in set theory
#reduce 1 ∈ small_set     -- this proposition in predicate logic
example : 1 ∈ small_set := Or.inr (Or.inl rfl)  -- a proof of it

/-!
The lesson is that when you look at an expression in set theory
you really must understand its underlying logical meaning, for
it's the underlying logical proposition that you'll need to prove.

So we're now in a position to see the formal definition of the
membership operation on sets in Lean. In the Lean libraries, it
is *def Mem (a : α) (s : Set α) : Prop := s a*, where α is a type.
The notation ∈ reduces to corresponding logic. More conretely, the
set theory proposition a ∈ s reduces to applying the set, s, viewed
as a membership predicate, to the argument, a (thus the expression,
*s a*) to yield a proposition, (s a), that is true if and only if
a is in s.
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

#reduce 3 ∈ small_set
example : 3 ∈ small_set := Or.inr (Or.inr (Or.inr (Or.inl rfl)))

/-!
### Take-Away

A take-away is that the set theory expression, x ∈ X,
simply means, that x satisfies the membership predicate
that defines the set X. To prove x ∈ X, substitute x for
the formal parameter in the membership predicate (apply
the predicate to x) and prove the resulting proposition.
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
*Set* namespace, so you can use *univ* either by first
opening the *Set* namespace, or by writing *Set.univ*.
-/

open Set

#reduce univ        -- fun _a => True
#reduce univ 0      --           True
#reduce univ 123456 --           True

/-!
#### Empty set

The empty set of values of a given type, usually
denoted as ∅, is the set
containing *no* values of that (or any) type. It's
membership predicate is thus false for every value of
the type. No value is a member. Formally, the membership
predicate for an empty set of values of type T is
*λ (t : T) => False*.

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
the operations include set membership (∈), intersection (∩), union (∪),
difference (\), complement (ᶜ) and more. We now turn to operations on
sets beyond mere membership.
-/


/-!
### Intersection

Given a type, T, and two sets, s1 and s2 of T-valued elements
(members), the *intersection* of s1 and s2 is the set the members
of which are those values that are in both s1 *and* s2. The intersection
of s1 and s2 is written mathematically as *s1 ∩ s2*.

The intersection operation is defined in Lean as *inter (s₁ s₂ : Set α) :
Set α := {a | a ∈ s₁ ∧ a ∈ s₂}*. Given two sets of alpha values, the result
is the set of values, a, that satisfy both conditions: a ∈ s₁ ∧ a ∈ s₂. Set
intersection (∩) is defined by predicate conjunction (∧).

Intersection of sets corresponds to logical conjunction (using *and*)
of the respective set membership predicates. The similarity in notations
reflects this fact, with ∩ in the language of set theory reducing to ∧ in
the language of predicate logic. The following Lean codeillustrate the point.
-/

variable (α : Type) (s t : Set α)
#check s ∩ t    -- the intersection of sets is a set
#reduce s ∩ t   -- its membership predicate is formed using ∧

/-!
As another example, the intersection of our even (ev) and small sets,
corresponding to the conjunction of their membership predicates,
contains only the elements 0, 2, and 4, as these are the only values
that satisfy both the ev *and* small predicates.
-/

def even_and_small_set := ev_set ∩ small_set  -- intersection!
#reduce (0 ∈ even_and_small_set)  -- membership proposition

/-!
As an example, let's prove 6 ∈ even_and_small_set. We'll first look
at the logical proposition corresponding to the proposition in set
theory assertion, then we'll try to prove tha underlying *logical*
proposition.
-/

#reduce 6 ∈ even_and_small_set

-- to prove: 0 = 0 ∧ (6 = 0 ∨ 6 = 1 ∨ 6 = 2 ∨ 6 = 3 ∨ 6 = 4)
example: 6 ∈ even_and_small_set := _

/-!
The proposition to be proved is a conjunction. A proof of it
will have to use And.intro applied to proofs of the left and
right conjuncts. The notation for this is ⟨ _, _ ⟩, where the
holes are filled in with the respective proofs. We can make a
first step a top-down, type-guided proof by just applying this
proof constructor, leaving the proofs to be filled in later.
The Lean type system will tell us exactly what propositions
then remain to be proved.
-/

example: 6 ∈ even_and_small_set := ⟨ _, _ ⟩

/-!
On the left, we need a proof of *6 ∈ ev_set*. This can also
be written as *ev_set 6*, treating the set as a predicate.
This expression then reduces to 6 % 2 = 0, and further to
*0 = 0*. That's what we need a proof of on the left, and
*rfl* will construct it for us.
-/

example: 6 ∈ even_and_small_set := ⟨ rfl, _ ⟩

/-!
Finally, on the right we need a proof of 6 ∈ small_set.
But ah ha! That's not true. We can't construct a proof
of it, and so we're stuck, with no way to finish our
proof. Why? The proposition is false!

Exercise: Prove that 6 ∉ small_set. Here you have to
recall that 6 ∉ small_set means ¬(6 ∈ small_set), and
that in turn means that a proof (6 ∈ small_set) leads
to a contradiction and so cannot exist. That is, that
6 ∈ small_set → False.

This is again a proof by negation. We'll assume that
we have a proof of the hypothesis of the implication
(h : 6 ∈ even_and_small_set), and from that we will
derive a proof of False (by case analysis on a proof
of an impossibility using nomatch) and we'll be done.
-/

example : 6 ∉ even_and_small_set :=
  fun (h : 6 ∈ even_and_small_set) => nomatch h

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

/-!
### Union

Given two sets, s and t, the union of the sets, denoted as
s ∪ t, is understood as the collection of values that are
in s *or* in t. The membership predicate of s ∪ t is thus
*union (s₁ s₂ : Set α) : Set α := {a | a ∈ s₁ ∨ a ∈ s₂}.
As an example, we now define even_or_small_set as the union
of the even_set and small_set.
-/

def even_or_small_set := ev_set ∪ small_set

/-!
Now suppose we want to prove that 3 ∈ even_or_small_set. What
we have to do is prove the underlying logical proposition. We
can confirm what logical proposition we need to prove using reduce.
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
example : 7 ∈ ev_set := _   -- stuck
example : 7 ∉ ev_set := λ h => _

/-!
### Set Complement
Given a set s of elements of type α, the complement of s,
denoted sᶜ, is the set of all elements of type α that are
*not* in s. Thus *compl (s : Set α) : Set α := {a | a ∉ s}.*

So whereas intersection reduces to the conjunction of membership
predicates, and union reduces to the disjunction of membership
predicates, the complement operation reduces to the negation of
membership predicates.
-/

variable (s : Set Nat)
#check sᶜ     -- Standard notation for complement of set s
#reduce sᶜ    -- fun x => x ∈ s → False means fun x => x ∉ s

/-!
Exercises:

(1) State and prove the proposition that 5 ∈ smallᶜ. Hint:
You have to prove the corresponding negation: ¬5 ∈ small_set.
-/

example : 5 ∈ small_setᶜ := _


/-!
### Set Difference
-/

#reduce Set.diff
-- fun s t a => s a ∧ (a ∈ t → False)
-- fun s t a => a ∈ s ∧ a ∉ t (better abstracted expression of same idea)

example : 6 ∈ ev_set \ small_set := ⟨ rfl, λ h => nomatch h ⟩

#reduce 6 ∈ ev_set \ small_set

/-!
### Subset
-/

#reduce @Set.Subset

/-!
### Powerset
-/

#reduce @Set.powerset

variable (s t : Set Nat)
#reduce s ∩ t
#reduce sᶜ

/-!
## Summary of Set Theory and Logical Underpinnings

| Set Theory  | Set Theory Definitions    | Predicate Logic                   |
|-------------|---------------------------|-----------------------------------|
| set α       | axioms of set theory      | predicate (α → Prop in Lean)      |
| s ∩ t       | { a \| a ∈ s ∧ a ∈ t }     | λ a => s a ∧ t a                  |
| s ∪ t       | { a \| a ∈ s ∨ a ∈ t }     | λ a => s a ∨ t a                  |
| sᶜ          | { a \| a ∉ s }             | λ a => s a → False                |
| s \ t       | { a \| a ∈ s ∧ a ∉ t }     | λ a => s a ∧ (t a → False)        |
| s ⊆ t       | ∀ a, a ∈ s → a ∈ t  ...   | λ a => s a → t a ...              |
| s ⊊ t       | ... ∧ ∃ w, w ∈ t ∧ w ∉ s  | ... ∧ ∃ w, (t w) ∧ (s w → False)  |
| 𝒫 s         | { b : Set s \| b ⊆ univ }  | λ b => b ⊆ univ                   |
-/
