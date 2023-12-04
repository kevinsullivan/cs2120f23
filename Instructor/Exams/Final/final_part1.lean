/-!
# Final #1 : Binary Relations and Equality

This question will test your ability to build on what you have
already learned. You are given a lesson on how *binary relations*
(which you can think of as sets of pairs of values) are specified
by two-place predicates along with rules for forming proofs of such
predicates.

## Representing Relations as Two-Place Predicates

We've seen how to represent sets, in set theory, as logical predicates,
and set operations as logical operations on underlying predicates. For
example set *union* is disjunction of respective membership predicates.
Different sets of objects of some type, α, are specified by different
predicates, all of one argment: of type α → Prop in Lean's type theory.

To represent not a set but a *binary relation*, *r*, on objects of some
type, α, we use predicates with two arguments: *r : α → α → Prop*. You
can think of a relation as specifying a set of pairs of values: those
pairs that satisfy the given predicate. As an example, *r* could be the
*less than* or the *equals* relation on natural numbers.

Now we will often want to define our own types, 2-place predicates
on values of such types, and axioms for constructing membership proofs.

### Example: Defining a Binary *likes* Relation on Dogs

Let's consider a simple example. We'll define a type called Dog;
three dogs of this type (rover, fido, and iris); a binary *likes*
relation on dogs; and, finally, we'll specify what proofs can be
constructed: that rover likes fido, fido likes iris, and iris likes
rover.

### Inductive Families of Propositions and Proofs

In Lean we can write such a specification in the form of what we
call an *inductive family* of propositions and associated proofs,
as follows. The name of the relation (defined next) is *likes*. It
takes two dog arguments and yields a proposition that we read as
asserting that the first dog likes the second.

Here's our dog type for purposes of this example. With this type
in hand, we'll be able to define a binary relation on these dogs.
-/

inductive dog : Type
| rover
| fido
| iris

open dog


/-!
Here's the important new idea: we specify a family of likes
propositions using *inductive*, and the set of associated proofs
are given by the constructors of this type. Namely, we can form
a proposition that any dog likes any other, but the only proofs
we have, and thus the only pairs of dogs that are in the relation
are (rover, fido), (fido, iris), and (iris rover).
-/

inductive likes : dog → dog → Prop
| rlf : likes rover fido
| fli : likes fido iris
| ilr : likes iris rover

open likes

/-!
We can now form any likes proposition using this proposition builder.
-/
#check likes iris fido
#check likes iris rover
#check likes iris iris

/-!
Moreover, we can state and prove propositions about dogs liking each other.
-/

example : likes rover iris := _             -- oops, no proof of this
example : ¬ likes rover iris := λ h => nomatch h  -- ok that's provable
example : likes iris rover := ilr           -- yep, there's a proof
example : likes rover fido ∧ likes iris rover := ⟨ rlf, ilr ⟩ --true!

/-!
### Example: A Relation Associating Each Nat With Its Square

Inductive families can be used to formalize all manner of important
and interesting relations. Here's another example were we define a
relation that associates each natural number with its square.
-/

inductive square : Nat → Nat → Prop
| sqr (a b : Nat) : b = a ^ 2 → square a b

open square

/-!
You can read this definition as saying that square is a binary
relation on natural numbers (first line), and (constructor). It
is applied to any two natural numbers, *a* and *b*, along with
a proof that *b = a ^ 2* to construct a proof of *square a b*.
-/

def sqr11 : square 1 1 := sqr 1 1 rfl
def sqr39 : square 3 9 := sqr 3 9 rfl
example : ¬ square 3 8 := λ h => nomatch h -- proof by negation
example : square 1 1 ∧ square 3 9 := ⟨ sqr11, sqr39 ⟩

/-!
### Exam Question #1

Express the following proposition in English, complete the
formal proof of it, and briefly explain in English how you
proved it.
-/

example : ∃ n, square n 4 := Exists.intro 2 (_) -- fill in _

/-
English language translation of propostion here:
-/

/-!
## The Binary Equality Relation on Objects of a Type α

With these concepts under our belts we can now understand equality
as a binary relation. In fact, in Lean, it's a polymorphic binary
relation. Given any type, α, there is a binary equality relation on
values of type α. Equality is defined as a polymorphic inductive
family, called *Eq* with one type parameter, two value parameters,
and one proof constructor, called *refl*. We'll unpack all of this
in steps.

### The Inductive Family of Propositions and Proofs

First, let's first see how applying Eq to a type, α, yields the type
of binary binary relations, represented as two-argument predicates,
on α: that is, as a function that takes two arguments of type α and
that returns the *proposition* that they're equal. (NB: We're not
yet talking about proofs.)
-/

-- Polymorphic Equality Relation Builder
#check @Eq
-- @Eq : {α : Sort u} → α → α → Prop  -- Sort u means any type

-- The type of binary relations on the natural numbers
#check @Eq Nat
-- Eq : Nat → Nat → Prop

-- The type of binary relation on strings
#check @Eq String
-- Eq : String → String → Prop

/-!
Next Let's see what propositions result when we apply Eq to a
type, α, and two values of that type. We expect a proposition
that the two values are equal, and that's exactly what we get.
-/

#reduce @Eq Nat 1 2     -- The proposition that 1 = 2

-- We can omit the @ and let Lean infer the type argument

#reduce Eq 1 2    -- a false equality proposition
#reduce Eq 0 0    -- a true equality proposition
#reduce Eq "Hi" "Bob"   -- a false equality of strings

/-!
### Infix Notation: = is Eq
Now note: *a = b* is just *infix notation* for Eq a b!
In the first of the following definitions, we use *Eq*
as a prefix notation. In the second, we use = as infix
notation. To see how to prove an equality proposition,
just look at the proof construction rule defined for *Eq.*
-/

example (α : Type): ∀ (a : α), Eq a a := λ a => Eq.refl a
example (α : Type): ∀ (a : α), a = a := λ a => Eq.refl a



/-!
Note that it's a type error in Lean to ask about equality
of objects of different types. In the following example,
Lean complains not that the types are different but that
it tried and failed to convert the first argument, 1, to
a corresponding String value. Lean natively lacks a rule
for performing such *coercions*.
-/

#check Eq 1 "Hi"

/-!
### Formal Definition of Equality Relation(s) in Lean
So we are now finally ready to meet Lean's definition of
the equality relation, Eq, including the means by which one
constructs *proofs* of equality. Here it is, from mathlib
(Lean's library of mathematical definitions). We put a '
on the name so as not to clash with Lean's definition.
-/

inductive Eq' : α → α → Prop where
  | refl (a : α) : Eq' a a

/-!
Let's dissect this definition. We'll use Lean's definition
henceforth. First, we note that the first line uses α without
declaring it. Lean 4 is programmed to assume that α is some
type. The first line is thus equivalent to the following:
*inductive Eq (α : Sort u): α → α → Prop*.
-/

#check Eq' 2 3    -- Using our definition of Eq'
#check Eq 2 3     -- Lean supports infix = notation

/-!
#### The Introduction Rule for Eq

And what about proofs? How can we prove 1 = 1, for example?

Eq provides a single constructor, *refl*, with any value, *a : α*,
as an argument. The term, *Eq.refl a* is defined by this rule to be
a *proof* of *a = a*. *Eq.refl* is thus the introduction rule for
equality: the rule for constructing a proof an equality. Indeed, it
is the only way to create a proof of an equality proposition.

Note that there is no way to form a proof of *a = b* for different
values of *a* and *b*, as *refl* takes only one argument! One thing
to note is that Lean reduces terms, such as *a* and *b*, when *Eq*
is applied, so Eq.refl will prove *a = b* if they are the same term
*when reduced*. This allows us to prove equality propositions such as
*2 = 1 + 1*, because both sides reduce to the same term, *2*. Let's
assert some equalities and see what we can prove.
-/

example : 1 = 1 := Eq.refl 1
example : 1 = 1 := rfl          -- Lean infers α = Nat *and* a = 1
example : 2 = 1 + 1 := rfl      -- Lean reduces 1 + 1 to 2, rfl works
example : "Hi" = "Hi" := Eq.refl "Hi"
example : true = or true false := Eq.refl true


-- Three proofs of the same inequality: "proof by negation"
example : 1 ≠ 2 := λ h => nomatch h
example : ¬1 = 2 := λ h => nomatch h
example : 1 = 2 → False := λ h => nomatch h

/-!
#### What About *rfl*?

Ok, so what about this *rfl* thing we've been using to produce
proofs of equality? It's just function that applies *Eq.refl*
to α and *a*, but now *both values* are inferred from context.
The key difference between *rfl* and *Eq.refl* is that *rfl*
takes both the type and the value argument implicitly, whereas
*refl* requires that the value, *a*, be given explicitly. Both
operations return a proof of *a = a* for any *a* of any type.
The *rfl* function does so by using Eq.refl. If Lean cannot
infer *a* due to lack of context, you have to use *Eq.refl*
and give *a* explicitly.

Here you can see that rfl really just infers *a* and applies
*Eq.refl* to it.
-/

#reduce @rfl                  -- fun {α} {a} => Eq.refl a
example : 1 = 1 := rfl        -- infers α = Nat, a = 1
example : 1 = 1 := Eq.refl 1  -- infers α = Nat, a = 1

/-!
### The Elimination Rule for Equaltiy

We've now seen the introduction rule, *refl*, for constructing
proofs of equality. What is or are the elimination rules? If you
*have* a proof of equality, how can you use it in constructing
other proofs? The answer is if you know (have a proof, h : a = b),
and you have a proof, *pa : P a*, of a proposition, *P a* (formed by
applying a predicate *P* to *a*), then you can use *h : a = b* to
*rewrite* your proof of *P a* into a proof of *P b*.

Here's an example. If you know Mary is Nice, and Mary is also know
as (is equal to) Maire, then you can conclude that Maire is Nice. In
other words, if *a = b*, then you can *substitute b* for *a* in any
proposition without changing its meaning. Again, informally, if P a
(Mary is Nice), and a = b (Mary also known as Maire), then P b (Maire
is nice).

This rule, known as the substitutivity of equals, is the *elimination*
("how to use") rule for proofs of equalities. In Lean it's called
*Eq.subst*, and it's defined as follows. Note that in this definition,
*motive* is just another name for *P* in our previous example.
-/

#check @Eq.subst

/-!
Eq.subst.{u} {α : Sort u} {motive : α → Prop} {a b : α} (h₁ : a = b) (h₂ : motive a) : motive b

In other words, given (1) any type of values, α, (2) any
predicate, *motive*, on values of this type, (3) two values
*a* and *b*, (4) a proof of *a = b*, and (5) a proof of *motive
a* (that *a* satisfies the predicate), then you can by applying
this rule obtain a proof that *b* satisfies it, too. Let's see
some examples. Note that the type, predicate, and two values
are all inferred, so in a practical application of *Eq.subst*
you only provide a proof of equality and a proof of *motive a*
to get a proof of *motive b*. (In our example, again, *motive*
is the *Nice* predicate.)
-/

section
variable
  (Person : Type)
  (Mary Maire : Person)
  (Nice : Person → Prop)
  (h₁ : Mary = Maire)
  (h₂ : Nice Mary)

#check @Eq.subst

example : Nice Maire := Eq.subst h₁ h₂
end

/-!
Understand this example! From *Mary = Maire* and *Mary is
nice* we proved that Maire is nice, and the proof was by
*substitution of equals for equals*, namely Maire for Mary.
That's how you'd explain it in English.

Here's another example. It formalizes just what we've said.
If α is any type; *P* is a predicate on values of this type;
*a* and *b* are values of this type, you have a proof, *h*, of
*a = b*, and you have a proof, *pa : P a*, then you can have
a proof of *P b* by applying Eq.subst.
-/

example  {α : Type} {P : α → Prop} {a b : α} (h : a = b) (pa : P a) : P b :=
Eq.subst h pa

/-!
### Aside on Tactics in Lean

In Lean, applying Eq.subst directly can be tricky and doesn't always produce what
you want. The reasons are beyond the scope of this class. The upshot is that for us
it's better to use a predefined Lean *tactic*, *rw* (short for rewrite), that does
the work of applying Eq.subst for us.

A tactic in Lean is a proof constructing automation. When providing a term of
any type, you cal always switch into *tactic mode* using the keyword, *by*, that
is followed then by a sequence of tactic applications.

Tactics can take arguments. The *rw* tactic is given to us from Lean's library.
Applied with a proof of an equality, *h : a = b*, *rw [h]* rewrites each *a* in
the current goal to *b*. That's logically sound: after all *a = b*. This is very
helpful if you have a proof of *P b*. To do a rewrite in the reverse direction,
rewriting each *b* in the current goal to *a*, justified by the same equality,
proof, *h : a = b*, one writes *rw [←h]*. Here's an example. Study carefully
the starting context, understand how the rewrite should work, and confirm it
does.

Place your cursorat the end of the *by* line, then after each of the tactic lines,
so see how the goal and your context change when you apply the *rw* tactics.
-/

example  {α : Type} {P : α → Prop} {a b : α} (h : a = b) (pa : P a): P b :=
by            -- use tactic mode to construct required term
  rw [←h]     -- rewrite b to a in the goal
  assumption  -- we already have a proof of the goal; done


/-!
### Properties of the Equality Relation

-/

/-!
### Properties of the Equality Relation

From just the introduction rule (reflexivity) and the
elimination rule (substitutability of equals for equals)
we can prove that the equality relation has three critical
additional properties:
- it's symmetric
- it's transitive
- it's an equivalence relation

Here we will focus on symmetry and transitivity. Being an
equivalence relation just means that it reflexive, symmetric,
and transitive. We will explain how to prove that equality
is symmetric. We will then leave it to you to prove that it
is also transitive. That will show that you are conversant
with the ideas from this class and from this problem.
-/

/-!
#### Equality is Reflexive

Equality is reflexive by definition: for *any (a : α)*, the
term, *Eq.refl a*, is accepted as a proof of *a = a*. So if you
need a proof of *a = a*, you can, and indeed must, construct it
by applying the *Eq.refl* *proof constructor to *a*.

Here's another proof of reflexivity. Of course is just boils down
to the *refl* constructor. It makes *Eq* reflexive *by definition*.

See the following code. We hypothesize that α is any type and
*a* is any value of this type. We then prove the proposition that
*a = a*. Be sure to read this example and understand it fully.
-/

example (α : Type): ∀ (a : α), a = a := λ a => Eq.refl a

/-!
### Theorem: Equality is Symmetric

Our second example is a statement and proof of that the binary
equality relation on a type of objects is *symmetric*.
-/

theorem eq_is_symm {α : Type} {a b : α} : a = b → b = a :=
λ h => by     -- Put cursor here to see context
  rw [h]

/-!
It's important to put your see the context after
we assume h but before we do the rewrite. Observe
that the rewrite will write left terms into right
terms in the current goal. That makes the goal into
*b = b*. And that is true with a proof by rfl.
-/


/-!
#### Exam Question #2: State and Prove that Equality is Transitive

Formally state and prove that equality is transitive. Finish the
proposition (fill in the first underscore "hole") so that it asserts
that equality is *transitive*. Avoid using ∧ in your definition; use
→ instead. It simplifies the proofs.

Model your answer on the example of symmetry above. You already know
how to construct proofs of implications. The new element here is
rewriting goals based on known (or assumed) equalities.

Notes: (1) fill in the _ holes. (2) you can and will have to
write separate tactic applications indented on separate lines.
-/

theorem eq_rel_trans {α : Type} {a b c : α} :
_               -- fill with proposition: equality is transitive
| _, _ => by
  _             -- fill in your proof of it here

/-!
## Exam Question #3

You know that the Nat.succ function takes any natural
number and returns its successor. You are to define the
corresponding binary relation, as an inductive family.
It will specify a set of pairs of natural number values,
*(a, sa)*, where *sa = Nat.succ a*. Then prove (1) the
pair, *(2, 3)* is in the relation, and the pair *(2,4)*
is not.
-/

-- Your answer here
