/-!
# Predicate Logic

In this chapter we build a bridge from
representing logical propositions and proofs
using computational types and values, to the
logical type universe in Lean, called Prop.
We'll explain why this can be a good idea as
we go along.

## Empty : Type becomes False : Prop
-/

#check Empty
/-!
inductive Empty : Type
-/

#check False
/-!
inductive False : Prop
-/

/-!
### Computational
-/

-- we model negation as proof of uninhabiteness
def no (α : Type) : Type := α → Empty

-- a sensible proofs_of_false type is uninhabited
inductive something_false : Type

-- proof that proof_of_false is false
def no_falsity : no something_false  :=
  λ a => nomatch a

#check no_falsity

/-!
### Logical
-/

#check Not
/-!
def Not (a : Prop) : Prop := a → False
-/




/-!
We first and mainly in this course introduce
you to predicate logic through its embedding
as a simple special case in the higher-order
logic of the Lean prover. We'll explain what
that means.

You have now understood propositional logic,
including the properties of an expression being
satisfiable, unsatisfiable, or valid.

Whereas SAT and SMT solving is about finding a
solution, validity checking is about qualifying
as a sound principle of deductive reasoning,
independent of any particular interpretation,
world, or domain. A *valid* proposition is a
sound general principle of logical reasoning.

For example, from the truth of the proposition,
*P ∧ Q*, where *P* and *Q* are any propositions
whatsover (generalility), we can infer the truth
of *P*. In other words, *P ∧ Q → P* is a *valid*
deduction under *any* interpretation.

Self-test: How would you test the validity of the
proposition, *P ∧ Q → P*, in propositional logic,
right now? Answer: write out the truth table and
show that all outputs are true.

## Changes from Propositional Logic
Now we shift to predicate logic. Predicate logic
builds on proposition logic but makes several major
additions and changes.

### Conectives
∧, ∨, ¬, →, and ↔, and also their truth-combining
meanings. For example, if P and Q are propositions
in *predicate* logic, then so are *P ∧ Q*, *P ∨ Q*,
*P → Q*, and so forth.

### Theories
The atomic propositions of propositional logic
can now be expanded into expressions written in
terms of rich other theories. For example, one
can write (X ≥ 0) ∧ (Y = X + 1) to specify a
state of affairs that can prevail in a world
represented by an integer pair with the usual
notion of additional. It's true in the world,
X = 5 and Y = 6, but not for X = 5 and Y = 7.

### Functions
Predicate logic adds the notion of functions as
part of the logic. Functions are essentially as
you have already leared them in Lean. Functions
can be applied to argments within propositions.
Here's an example. Incidentially it also uses
equality. *MotherOf Bob = Helga*, Here MotherOf
is a function that takes a person argument and
that returns that person's mother.

### Propositions as Types

Predicate logic adds the notion of a predicate,
which is nothing but a parameterized proposition,
giving rise to a family of propositions, one for
each combination of argument values.

As an example, I could represent the proposition
that Kevin is From Charlottesville as an atomic
thing: in Lean, as a (propositional) type in Prop.
-/

inductive KevinIsFromCharlottesville : Prop

/-!
The question is, is this proposition true? The
answer is no. It's an uninhabited type. Values of
propositional types in Prop are taken as proofs.
A proposition is false if it's shown that there
are no proofs. To show that P is false, we show
P → False.
-/

theorem KNFC : ¬KevinIsFromCharlottesville :=
λ p => nomatch p

/-!
Now suppose Kevin is from Charlottesville. We
have the same proposition, but to judge it to be
true, we need a proof. In Lean, the proofs of a
proposition are the values of the propositional
type (in Prop) that express the proposition.
-/

inductive KevinIsFromCville : Prop  -- proposition
| birthRecord                       -- a proof
| invisible_forhead_tattoo          -- a second one

open KevinIsFromCville

/-!
The proposition, KevinIsFromCville, is thus defined
to have two proofs (proof values, proof objects):
birthRecord and invisible_forehead_tattoo.

Now we can use Lean's type checker to check that a
given proof object is correct for the proposition
to be proved: is it a value of that type?
-/

def     kevin_local': KevinIsFromCville := invisible_forhead_tattoo
theorem kevin_local : KevinIsFromCville := invisible_forhead_tattoo
example             : KevinIsFromCville := invisible_forhead_tattoo

/-!
The first examples bind names to typehecked proofs of the proposition,
KevinIsFromCville. The third typechecks the proof term against the type
but doesn't bind a name to the proof term.
-/


/-!
### Predicates

While the proposition, KevinIsFromCville is fabulous, it's just
one of an infinite family of propositions of the form P is from L
where P ranges over people and L ranges over locations. To help
with an example, we introduce two data types the values of which
represent people and places, respectively.

There are two people in the little world we're modeling now and
two places: harry and martha, and cville and dc.
-/

inductive Person : Type | harry | martha
inductive Location : Type | cville | dc

/-!
Now here's an example of a predicate: one that generalizes our
earlier example. The predicate is a function. When applied to the
right kind of argument values, it returns a proposition that, in
general can be understood as asserting that some state of affairs
holds involving them.

This is a new construct for us. We've seen type builders take
types as arguments; but here, isFrom, takes arbitrary values,
in this case, data values of the Person and Localtion types.

The trick then is to define the set of proofs that can be had
for any such proosition

type to represent mathematical proofs, rooted in axioms, pick
out those propositions that should evaluate to true

-/

inductive IsFrom : Person → Location → Prop

open Person Location IsFrom

#check IsFrom harry dc




/-!
which is a function from values to propositions.
A predicate is a parameterized proposition, with
different parameter values giving rise to a whole
family of propositions.

It adds universal and existential quantifiers,
with notations ∀ and ∃, respectively. We'll talk
about them soon.

Finally, in predicate logic, the notion of an
interpretation, or map from syntactic terms to
semantic meanings, is radically expanded. In
predicate logic a name can be interpreted as
meaning an object, function, or relation in an
arbitrary *domain of discourse* outside of the
logic.

This change is perhaps the most consequential. In
propositional logic, worlds were limited to ordered
n-tuples of Boolean values. Now the associated with
logical identifers can refer to all manner of things:
people, numbers, functions, relationships, whatever.

A proposition in predicate logic can be understood
as characterizing a state of affairs in an abitrary
world, and is true if that state of affairs holds in
that particular world.

Now just as in propositional logic, the truth of a
given proposition depends on the interpretation under
which it's evaluated. The proposition, "The red block
is on the green block," for example, is almost surely
true right now in some particular place (world); but
untrue elsewhere. The truth of a proposition depends
on the things that the logic refers to in a domain of
discourse.

## No Validity Checking by Semantic Evaluation

whether the *state of affairs* it specifies in
that world actually holds there.

Consider the proposition, *Tom passed his test.*
*Tom*, *test*, and *passed* can have as meanings
specific things one or another specific worlds.
For example, *Tom* could refer to "that guy right
there;* *test* could refer to the CS2120F23 midterm,
and *passed* as it pertains to a specific test of
a specific person could mean that that test earned
at least 60 points.

Propositions in predicate logic assert that certain
conditions, or states of affairs, hold in one world
or another. The truth of propositions in predicate
logic, in general, depend on the specific world in
which they are evaluated, on an *interpretation.* A
proposition is true of a world if the situation that
it describes holds in that *domain of discourse*.

One major consequence of the change in the nature
of interpretations from propositional to predicate
logic is that we can no longer check the *validity*
of a proposition *semantically:* by enumerating all
possible interpretations and evaluating the truth of
the expression under each one. How could you possibly
do that when an interpretation can now link names in
the logic to things, functions, properties, relations
in any imaginary, abstract, or real physical world?
You can't.

We need a new approach to validity. And that approach,
not semantic, is instead syntactic. It involves axioms
and theorems, which are proofs of propositions based
on the axioms and reasoning principles of our logic.
-/

/-!
## Propositions as Types and Proofs as their Values

TBD: Introduce Prop
-/

/-!
### × and ∧

#### ×

Recall that if α and β are types, then α × β is also a
type: the type of ordered pairs of α and β values. Here
is how it's defined.
-/

namespace cs2120f23
structure Prod (α : Type u) (β : Type v) where
  fst : α
  snd : β
namespace cs2120f23

/-!
Let's analyze that again. Prod is polymorpnic: it's a
type builder. When applied to any two types, α and β,
it yields the type Prod α β, with notation α × β
-/

#check Prod Nat Bool
#check Nat × Bool

/-!
Such a type has just one constructor, implicitly Prod.mk,
with (_,_) as a standard concrete mathematical notation.
Given *a : α* and *b : β*, the term, *Prod.mk a b*, with
concrete notation, *(a, b)*, represents the ordered pair,
*(a, b)*.
-/

#check @Prod.mk         -- study and understand its type
#check Prod.mk 4 true   -- example
#check (4,true)         -- using provided notation

-- Quiz: what is the type of (4,true)? Ans: Prod Nat Bool.

/-!
In our earlier work, we used ordered pair data types,
such as *Nat × Bool*, to represent conjunctions. For
example, to prove that there is a Nat *and* there is
a Bool, we would apply Prod.mk to a value of type Nat
and a value of type Bool. And to use a value of type
Nat × Bool, we destructure the pair to extract one or
the other of the two values. We can then "prove" such
propositions encoded as types like the following:
-/

def from_and {α β : Type} : α × β → α



/-!
#### ∧

/-!
We now complete our transition into teaching predicate
logic as embedded in Lean. We all by ourselves embedded
propositional logic in Lean, and even built validity and
SAT checkers. Fortunately, others have embedded predicate
logic in Lean. Moreover, it closely resembles our use of
product (×), sum (⊕), types and α → Empty function types
to encode logical propositions.

conjunctive propositions, built using *and*.
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
-/

def from_ab_pair_a' {α β : Type} : α × β → α
| (a,_) => a

def from_ab_true_a_true {α β : Prop} : α ∧ β → α
| ⟨ a, _ ⟩  => a

#check Sum

/-!
inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β
-/
/-!
inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b
-/

def sum_elim {α β γ : Type} : (α ⊕ β) → (α → γ) → (β → γ) → γ
| (Sum.inl a), f, g => f a
| (Sum.inr b), f, g => g b

#check Or.elim

/-!
theorem Or.elim {c : Prop} (h : Or a b) (left : a → c) (right : b → c) : c :=
  match h with
  | Or.inl h => left h
  | Or.inr h => right h
-/

theorem and_comm { P Q : Prop} : (P ∧ Q → Q ∧ P) ∧ (Q ∧ P → P ∧ Q) :=
And.intro
  (λ ⟨ p, q ⟩ => ⟨ q, p ⟩ )
  (λ ⟨ q, p ⟩ => ⟨ p, q ⟩ )

#check Or

def x := (1,2)
#eval x.1
#eval x.2



#check @And


def from_ab_proof_a_proof {α β : Prop} : α ∧ β → α





section foo

variable
  (α : Type)
  (β : Type)
  (γ : Type)

def prod_intro : α → β → α × β
| a, b => (a, b)

def prod_elim_left : α × β → α
| (a, _) => a

def prod_elim_right : α × β → β
| (_, b) => b

end foo

section bar

variable
  (α : Prop)
  (β : Prop)
  (γ : Prop)

-- major forms of proposition, represented as types in Prop
#check False
#check True
#check ¬α
#check α ∧ β
#check α ∨ β
#check α → β
#check α ↔ β

/-!
Here are the basic reasoning principles for *And* (∧).
-/

def and_intro : α → β → α ∧ β
| a, b => ⟨ a, b ⟩  -- that desugars to And.intro a b

def and_elim_left : α ∧ β → α
| ⟨ a, _ ⟩  => a

def and_elim_right : α ∧ β → β
| ⟨ _, b ⟩  => b

theorem and_comm : (α ∧ β → β ∧ α) ∧ (β ∧ α → α ∧ β) :=
And.intro
  (λ ab => And.intro ab.right ab.left)
  (λ ba => And.intro ba.right ba.left)

#check and_comm
#check (α ∧ β → β ∧ α) ∧ (β ∧ α → α ∧ β)
#check Prop   -- haha, etc etc

/-!
In Lean, libraries they are And.intro, And.elim_left,
and And.elim_right, with notations, ⟨ _, _ ⟩, .left, and
.right.
-/

#check @Prod.mk
#check @And.intro

#check @Prod.fst
#check @And.left

#check @Prod.snd
#check @And.right


#check @Sum.inl
#check @Or.inl

#check @Sum.inr
#check @Or.inr

#check @Or.elim
-- compare with  (α ⊕ β) → (α → γ) → (β → γ) → γ




/-!
A conjecture: ∧ is commutative. By commutative we mean
that for arbitrary propositions, P and Q, no matter what
propositions they are, P ∧ Q ↔ Q ∧ P.

 The idea is that
from any proof of A ∧ B we can always derive a proof
of B ∧ A, and vice versa. Let's express the claim as
a proposition encoded as a type (assuming α, β, and
γ are defined): (α ∧ β → β ∧ α) ∧ (β ∧ α → α ∧ β).
-/

 which is to say that
if you have a proof of A ∧ B is equivalent to B ∧ A.
-/

end bar






/-!
You have also now learned about, and how to use, SMT
solvers. They extend propositional logic model finding
to logics in which previously elementary propositions
can now be expanded into propositions written in terms
of backround theories, such as linear arithmetic. As
an example, one might write *X < 3 ∧ Y = 5X *.

Now we shift to predicate logic. A major difference is
that interpretations (denotations) in predicate logic can
associate logical symbols with arbitrary objects. There's
no longer a practical way to enumerate all interpretations,
for purposes of validity checking. To reason about validity
of propositions in predicate logic requires soemthing new:
proofs.

A proof is a mathematical construct that shows that some given
proposition is *valid*. People will often say *true* instead
of valid. That's okay, but if what we want are valid principles
of reasoning, then what's vital is that a proposition be true *no
matter the interpretation*. A proof *validity* in this sense.

In the practice of research and applied mathemtics, proofs are
often just sketched quasi-formally, in mathematics-heavy natural
language. This approach enables fluid communication of essential
proof ideas without the ponderous details of a fully formalized
proof object. In Lean, we build complete proof objects.

The astonishingly good news at this point is that you already know
how to do this. We've already pulled the essential trick: to write
propositions as types and to consider values and functions as proofs
of them.

Just recall one of our numerous examples. For example, if you have
bread and cheese or jam, then you can have bread and cheese or bread
and jam. In abstract notation provided by Lean, we can represent this
proposition as the function type, *B × (J ⊕ C) → (B × J) ⊕ (B × C)*.
If there is an implementation, a function, say *p*, of this type,
then whenever you have a value, *v*, of type *B × (J ⊕ C)*, you can
have a value of type *(B × J) ⊕ (B × C)*, namely by applying *p* to
*v*. We proved an implication by exhibiting a function that implements
the corresponding function type.

As an exercise, go ahead and derive a function implementation again.
-/

def bjc2bjbc' { A B C : Type } : B × (J ⊕ C) → (B × J) ⊕ (B × C)
| Prod.mk b (Sum.inl j) => Sum.inl (b, j) -- destructure prod and sum
| (b, (Sum.inr c)) => Sum.inr (b, c)      -- use ordered pair notation

/-!
That's it. All the essential ideas are here. We represent
propositions as types, here a function type, and we represent
proofs as *values of these types*. Our implementation of the
preceding function proves that if we're given any value of
type , *B × (J ⊕ C)*, where *B, J,* and *C* are themselves
arbitrary types, then we can always derive a value of type,
*(B × J) ⊕ (B × C)*.
-/

/-!
We've thus encountered to famous Curry-Howard Correspondence.
It is just this idea, that propositions are representable as
types, with proofs of these propositions being values of these
types. Of course a proposition represented in this way can be
false, in which case it will be uninhabited when viewed as a
type.

And finally, we observe an important fact. When we want to know
if a proposition *(in predicate logic)* is valid, we need a proof,
but *any proof will do*. We do not care about irrelevant details
of proof structure, strategy, content, or anything else. All we
want and need to know is, is the proposition that we're proving
valid or not.

Two important consequences come from this view that proof details
are irrelevant. First, we should let inessential details of proofs
influence computations. Second, we can treat all proof values of a
proposition represented as a type as being equally good; and indeed,
equal.

Lean and other proof assistants like it provide a special type
universe for types that are intended to represent propositions.
In Lean it's called Prop. Now whereas we used × and ⊕ types to
represent logical ∧ and ∨ in *Type*, when writing in *Prop*, we
will use the logical symbols directly.

Now here's the trick we've pulled. Whereas we used *Prod.mk* to
create pairs of data values, and either *Sum.inl* or *Sum.inr* to
create either this type of data or that type of data, now we just
use *And.intro* or *Or.inl* or *Or.inr*. Now we're constructing
*proof* objects.
-/

def bjc2bjbc { A B C : Prop } : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C)
| And.intro a (Or.inl b) => Or.inl (And.intro a b)
| And.intro a (Or.inr c) => Or.inr (And.intro a c)

/-!
Ok, let's get back to our logic deli and see how things look now.
-/
inductive Bread : Prop | rye | wheat
inductive Cheese : Prop | cheddar | gruyere
inductive Jam : Prop | berry | stonefruit

def rye_and_cheddar : Bread ∧ (Jam ∨ Cheese) :=
  And.intro
    Bread.rye
    (Or.inr Cheese.cheddar)

def wheat_and_stonefruit : Bread ∧ (Jam ∨ Cheese) :=
  And.intro
    Bread.wheat
    (Or.inl Jam.stonefruit)

#reduce bjc2bjbc rye_and_cheddar
#reduce bjc2bjbc wheat_and_stonefruit

/-!



Consider the proposition, "the kitten likes the puppy."
Surely it's true in some real world situations right now,
but not in others. Whether the proposition is true in a
given world depends on whether the actual real kitten to
which it refers really, in the real world, likes the puppy
that the proposition also refers to. But if kitten refers
to a grumpy kitten, with the same puppy, the proposition
will not be true *in that alternative world*, under this
alternative interpretation, or denotation, of the variables.



and even polynomial (as we saw) in Z3. It generally will
not be able to solve constraints involving exponentials.



, as well as
the extension of this framework to include theories
in which elementary expressions are written, to be
solved, if possible, by the finding of a satisfying
assignment of values to variables, now of types that
can come from background theories. Examples of such
types include integer, string, real, and so forth.
-/
