/-!
# Encoding Propositions as Types

Now we turn to the construction of propositions
as types and proofs as values of these types. We
will start with a completely computational view
of things. That is, we'll just use ordinary data
and function types to encode propositions and
proofs. Next we'll make the observation that
*any* proof of a proposition will do to prove
that it's true, so from a purely logical view,
which proof one chooses, if there is one, is
*irrelevant*. That observation will motivate
the introduction of the type universe called
Prop. Types in this universe are understood to
encode logical propositions. What's unique to
this type universe is that all values of a type
are considered to be indistinguishable, which
is to say *equal*. All we really care about is
whether there is or isn't at least one value,
and any one is equally as good as any other.
For now however, we'll just focus on the idea
that we can represent propositions as types
without the added complexity of thinking about
this new type universe.
-/

/-!
## Elementary Propositions and Proofs

The idea that we can represent propositions as
types and values as proofs is not complicated.
First, of course, is that there are propositions.
Second, given a proposition, α, you can always
build another proposition, ¬α (not alpha). Given
two propositions, α and β (they could be the same) 
you can also build the propositions α ∧ β (alpha
and beta), α ∨ β (or), α → β (implies), and α ↔ β
(is equivalent to). 

To help make all this clearer, we'll first work 
through a simplified concrete elementary exercise.
Then we'll generalize from that example.    


### Example: Who's at UVa?

Here we select a type name, *BobStudiesAtUVa*,
to represent a proposition (that Bob studies at
UVa); and we define two values/proofs/evidence:
that Bob attends classes, and that Bob has paid
tuition. The type is the proposition; the proofs
are the values of this type.
-/
inductive BobStudiesAtUVa
| attendsClasses
| paidTuition

--          proposition                 proof
example : BobStudiesAtUVa := BobStudiesAtUVa.paidTuition

/-!
Another example.
-/
inductive MaryStudiesAtUVa
| attendsClasses
| paidTuition

--           proposition                  proof
example : MaryStudiesAtUVa := MaryStudiesAtUVa.attendsClasses


/-!
A third example: another proposition but with no proofs.
-/
inductive MarkoStudiesAtUVa : Type  -- need Type here, to resolve u

example : MarkoStudiesAtUVa := _    -- no can do; no proof

/-!
Now that we have several propositions, some with
proofs, we can learn how to define propositions that
are built from other propositions, and how to construct
proofs of these larger propositions.

In particular, given any two propositions, α and β, we
can form the propositions, α *and* β, α *or* β, and ¬ α.
The crucial move will be to define rules for constructing
proofs of these larger propositions in a way that gives
the intended meanings to *and*, *or*, and *not*. So let's
see how that works.
-/

/-!
#### And

We will stipulate that to construct a proof of *And α β*
we will need both a proof of α and a proof of beta. The
following example illustrates the point. We construct a
proof that Bob studies at UVa *and* Mary studies at UVa
by applying the *and* constructor to proofs of both these
types, and the result is a proof of the proposition that
is the *conjunction* of the given propopsition is true.
-/
inductive BobStudiesAtUVa_And_MaryStudiesAtUVa
| and (b : BobStudiesAtUVa) (m : MaryStudiesAtUVa)

-- named proofs of individual conjuncts
def b : BobStudiesAtUVa := BobStudiesAtUVa.paidTuition
def m : MaryStudiesAtUVa := MaryStudiesAtUVa.paidTuition

-- proof of the conjunction
example : BobStudiesAtUVa_And_MaryStudiesAtUVa :=
  BobStudiesAtUVa_And_MaryStudiesAtUVa.and b m

/-!
Let's generalize a bit.
-/

inductive MyAnd (α β : Type) : Type
| mk (a : α) (b : β)

inductive MyOr (α β : Type) : Type
| inl (a : α)
| inr (b : β)

example : MyAnd BobStudiesAtUVa MaryStudiesAtUVa := 
  MyAnd.mk b m

example : MyOr BobStudiesAtUVa MaryStudiesAtUVa := MyOr.inl b
example : MyOr BobStudiesAtUVa MaryStudiesAtUVa := MyOr.inr m

def MyNot (α : Type) := α → Empty 

example : MyNot BobStudiesAtUVa := λ b => _ -- Nope
example : MyNot MarkoStudiesAtUVa := λ m => nomatch m

/-!
#### OR
We will stipulate that to construct a proof of *Or α β*
we will need either a proof of α or a proof of beta. The
following example illustrates the point. We construct a
proof that Bob studies at UVa *or* Marko studies at UVa
by applying the *or.left* constructor to a proof that Bob
studies at UVa. There is no proof that Marko studies at
UVa, so we couldn't prove the disjunction with a proof
that he does study at UVa.
-/

inductive BobStudiesAtUVa_Or_MarkoStudiesAtUVa : Type
| left (b : BobStudiesAtUVa)
| right (m : MarkoStudiesAtUVa)
open BobStudiesAtUVa_Or_MarkoStudiesAtUVa

#check left b

example : BobStudiesAtUVa_Or_MarkoStudiesAtUVa  :=
  left b

/-!
Note that we had only once choice of proof constructor
in this case, because there's no value we could pass to
the second "proof constructor," *right*.
-/

/-!
#### NOT

A proposition that has no proofs is false. The negation of a
false proposition is true. For example, the proposition that
Marko studies at UVa demonstrably has no proofs, so it should
be clear that the proposition "Marko does *not* study at UVa"
is true as witnessed by an easy proof.

Suppose more generally that we have a proposition, P. To judge
P to be true, we must present a proof of P. Any value of type
P will do. Look to the constructors of the P type to see how
you can construct values. P is false only when this type has
no values/proofs at all.

So how do we prove that *not P* is true? This is the case if
and only if P is uninhabited. So how do we prove that a type,
P, is uninhabited?

The trick is to use a function to the Empty type. We studied
this idea in class earlier. Now we get to use it.

It's easier to see if you first consider a case where P is
inhabited (which for us indicates that it's *true*). Then
there cannot possibly be any function, (f : P → Empty). If
there were such a (p : P), then (f p) would be a value of
a type that has no value. That cannot happen so there must
be no such p. You could say that whenever a proposition P
is true, then P → Empty is false.

Now consider the case where P is uninhabited, which is to say
P is false. In this case, you can implement a function of type
P → Empty! The function *assumes* that it's given an argument
of (p : P). The function is defined by case analysis on forms
of p. But P is uninhabited, so there are no forms to consider
and the function definition is accepted. It boils down to being
like an identity function on impossibilities: if you *give* it
one (proof of P), it'll give you one back (proof of Empty). But
of course one can never use it because we want impossibilities
never arise so as to have a useful logic.

So, when P is inhabited, thus true (in our sense), the type,
P → False, is uninhabited, thus false. On the other hand, if P
is uninhabited, thus false, then P → Empty is inhabited, thus
true. P → Empty is inhabited here because there is a function
of this type. It assumes it's given a value (p : P), it promises
to return Empty, and it never breaks it promise because there
simply are *no cases* for p for which a return value is needed.

In short, when P is true, P → False is false, and when P is
false, then P → True is true. In other words, the function
type (P → False) type expresses the *negation* of P, usually
written as ¬P, and pronounced *not P*.
-/

def neg (P : Type) := P → Empty


/-!
A proof that Marko does *not* study at UVa
-/
example : neg MarkoStudiesAtUVa :=
  -- a proof of  P is a *function* from P to Empty
  -- and here's one
  λ p :  -- a function that assumes a proof of MarkoStudiesAtUVa
  MarkoStudiesAtUVa =>
  -- checks for no constructors to "match" on (no cases to consider)
  nomatch p


-- TODO: Add examples for implies and iff

/-!
***********************
### Generalizing

In the previous example, we worked with specific
propositions expressed as "logic encoding" types.
The types we've used are very ordinary programming
types. The one for and requires two proofs, the one
for or requires one proof, and the one for not is
just a check for the uninhabitedness of a type.

We'll now generalize to arbitrary propositions,
continuing for now to use a new type to encode
each new proposition we want to express. Proofs
will be values of such types, often build from
values including smaller proofs. 

In this section we'll also introduce explicitly
and switch to using standard types: Prod α β to
represent values compring pairs of objects. of 
types α *and* β; and Sum α β to represent a value
type α *or* a value of type β. Finally, we will 
continue to use α → Empty as the type of proof
that α is uninhabited, thus false, for having no
proofs. 
-/

/-!
#### And

We will stipulate that to construct a proof of *And α β*
we will need both a proof of α and a proof of beta. The
following example illustrates the point. We construct a
proof that Bob studies at UVa *and* Mary studies at UVa
by applying the *and* constructor to proofs of both these
types, and the result is a proof of the proposition that
is the *conjunction* of the given propopsition is true.

Now, recall: 
- def b : BobStudiesAtUVa := BobStudiesAtUVa.paidTuition
- def m : MaryStudiesAtUVa := MaryStudiesAtUVa.paidTuition

Finally, we introduce the *Prod* (for product) type in Lean.
It's polymorphic in two types, and has one constructor that
requires a value (proof) of each type. An instance of a Prod
type is essentially a polymorphic *ordered pair*. A proof of
a conjunction is such a pair of proof values. 
-/

-- Polymorphic in *computational* types
#check (@Prod)

/-!
structure Prod (α : Type u) (β : Type v) where
  fst : α
  snd : β

Product type (aka pair). You can use `α × β` as notation for `Prod α β`.

Given `a : α` and `b : β`, `Prod.mk a b : Prod α β`. You can use `(a, b)`
as notation for `Prod.mk a b`. Moreover, `(a, b, c)` is notation for
`Prod.mk a (Prod.mk b c)`.

Given `p : Prod α β`, `p.1 : α` and `p.2 : β`. They are short for `Prod.fst p`
and `Prod.snd p` respectively. You can also write `p.fst` and `p.snd`.
-/

#check (1,"Hello")


-- construct proof of the conjunction (introduction rule)
example : Prod BobStudiesAtUVa MaryStudiesAtUVa := Prod.mk b m
example : BobStudiesAtUVa × MaryStudiesAtUVa := ⟨ b, m ⟩ 
example : BobStudiesAtUVa × MaryStudiesAtUVa := ( b, m ) 

-- *use* a proof of the conjunction (elimination rules)
example : BobStudiesAtUVa × MaryStudiesAtUVa → BobStudiesAtUVa := λ p => p.fst
example : BobStudiesAtUVa × MaryStudiesAtUVa → MaryStudiesAtUVa := λ p => p.2

/-!
#### OR
-/


/-!
We use Sum types, polymorphic in two types, α and β, to define 
values of type Sum α β each of which carries *either* a value of 
the α type or a value of the second, right type, called Sum.inr. 


-/

#check (@Sum)

/-!
inductive Sum (α : Type u) (β : Type v) where
  | inl (val : α) : Sum α β
  | inr (val : β) : Sum α β

`Sum α β`, or `α ⊕ β`, is the disjoint union of types `α` and `β`.
An element of `α ⊕ β` is either of the form `.inl a` where `a : α`,
or `.inr b` where `b : β`.

-/

-- How to construct proof of "or" in our computational style
example : Sum BobStudiesAtUVa MarkoStudiesAtUVa := Sum.inl b    -- b is a proof of left
example : BobStudiesAtUVa ⊕ MarkoStudiesAtUVa := Sum.inr _  -- no proof, uninhabited type

/-!
Note that we had only once choice of proof constructor
in this case. There is no proof of MarkoStudiesAtUVa to pass
to the right constructor. When attempting to prove a disjustion
you have to figure out which disjunct to a construct proof for. 
-/

-- How to use a proof of a disjunction

example : BobStudiesAtUVa ⊕ MarkoStudiesAtUVa → BobStudiesAtUVa
| (Sum.inl l) => l
| (Sum.inr r) => nomatch r



/-!
#### NOT

A proposition that has no proofs is false. The negation of a
false proposition is true. For example, the proposition that
Marko studies at UVa demonstrably has no proofs, so it should
be clear that the proposition "Marko does *not* study at UVa"
is true as witnessed by an easy proof.

Suppose more generally that we have a proposition, P. To judge
P to be true, we must present a proof of P. Any value of type
P will do. Look to the constructors of the P type to see how
you can construct values. P is false only when this type has
no values/proofs at all.

So how do we prove that *not P* is true? This is the case if
and only if P is uninhabited. So how do we prove that a type,
P, is uninhabited?

The trick is to use a function to the Empty type. We studied
this idea in class earlier. Now we get to use it.

It's easier to see if you first consider a case where P is
inhabited (which for us indicates that it's *true*). Then
there cannot possibly be any function, (f : P → Empty). If
there were such a (p : P), then (f p) would be a value of
a type that has no value. That cannot happen so there must
be no such p. You could say that whenever a proposition P
is true, then P → Empty is false.

Now consider the case where P is uninhabited, which is to say
P is false. In this case, you can implement a function of type
P → Empty! The function *assumes* that it's given an argument
of (p : P). The function is defined by case analysis on forms
of p. But P is uninhabited, so there are no forms to consider
and the function definition is accepted. It boils down to being
like an identity function on impossibilities: if you *give* it
one (proof of P), it'll give you one back (proof of Empty). But
of course one can never use it because we want impossibilities
never arise so as to have a useful logic.

So, when P is inhabited, thus true (in our sense), the type,
P → False, is uninhabited, thus false. On the other hand, if P
is uninhabited, thus false, then P → Empty is inhabited, thus
true. P → Empty is inhabited here because there is a function
of this type. It assumes it's given a value (p : P), it promises
to return Empty, and it never breaks it promise because there
simply are *no cases* for p for which a return value is needed.

In short, when P is true, P → False is false, and when P is
false, then P → True is true. In other words, the function
type (P → False) type expresses the *negation* of P, usually
written as ¬P, and pronounced *not P*.
-/

-- reminder
-- def neg (P : Type) := P → Empty


/-!
A proof that Marko does *not* study at UVa
-/
example : neg MarkoStudiesAtUVa :=
  -- a proof of  P is a *function* from P to Empty
  -- and here's one
  λ p :  -- a function that assumes a proof of MarkoStudiesAtUVa
  MarkoStudiesAtUVa =>
  -- checks for no constructors to "match" on (no cases to consider)
  nomatch p

example : neg (MaryStudiesAtUVa × MarkoStudiesAtUVa) :=
λ p => nomatch p.2


/-! Proof Irrelevance 

When working with data types, specific values of 
given types matter, because they can influence 
computational outcomes. 

By contrast, from the perspective of the truth 
value of a given proposition, all mathematically 
correct proofs of it are equally good. The only
real question is is there any proof at all. It
comes down to falsity meaning the demonstrated
non-existence of any possible proof, and truth
following from the construction of any proof of
it.

Furthermore, when we include proofs in code,
we really don't want arbitrary choices among
equally good proofs to affect *computational* 
outcomes.

The constructive logic of Lean and of other 
similar proof assistants formalize the idea
of types that represent propositions, where
choices among specific proofs can't matter,
by defing the type universe called Prop in
which types represent propositions and all
value/proof terms of any such types are now
treated as *equal*.

That contrast sharply with values of types
in Type u (for any type universe level u).
Here, particular values certainly matter,
and the opposite rule applies for equality
of terms: terms constructed by different 
constructors or with different arguments
are *never* equal.
-/

inductive B : Prop
| paid
| classes

inductive M : Prop
| paid
| classes

inductive K : Prop

-- And ∧ 
-- intro: construct a pair of proofs
-- elim: show (P ∨ Q → R) by case analysis on proof of P∨Q

-- intro
example : And B M := And.intro B.paid M.classes
def b_and_m_true : B ∧ M := And.intro B.paid M.classes
theorem b_and_m_true' : B ∧ M := And.intro B.paid M.classes
example : B ∧ M := ⟨ B.paid, M.classes ⟩ 

-- elim
example : B ∧ M → M := λ bm => bm.right
example : B ∧ M → B := λ bm => bm.1

-- example
theorem foo : B ∧ Not K := ⟨ B.paid , λ k => nomatch k ⟩ 
example : B ∧ ¬K := foo

-- Or 
-- intro: construct a proof for one case or the other
-- elim: by case analysis on proof of P ∨ Q

-- intro
example : B ∨ K := Or.inl B.paid

-- elim example
example : B ∨ K → B :=
λ bork => match bork with 
| Or.inl b => b
| Or.inr k => nomatch k   -- can't happen

example : 
  ∀ (Raining Sprinkling Wet : Prop), 
    (Raining ∨ Sprinkling) → 
    (Raining → Wet) → 
    (Sprinkling → Wet) → 
    Wet := 
λ _ _ _ rors rw sp => 
match rors with
| Or.inl r => rw r 
| Or.inr s => sp s


-- Not
-- intro: Prove ¬P by proving P → False
-- elim: as with any function, elimination is by apply!

-- intro example
def notK : ¬K := λ k => nomatch k 

-- elim example (law of no contradiction example)
example (P : Prop) : ¬P → P → False :=
λ np p => np p

example (P : Prop) : ¬¬P → P
| nnp => _ -- stuck

example (P : Prop) : (P ∨ ¬P) → (¬¬P → P)
| pornp => match pornp with
  | Or.inl p => λ _ => p
  | Or.inr np => λ nnp => nomatch (nnp np)


--- ∀ (P : Prop), P ∨ ¬P


-- Implication (P → Q)
-- intro: show that from an *assumed* proof of P, you can derive a proof of Q
-- elim: *apply* that function to a proof of P to get a proof of Q

-- intro example (writing negation as implication)
def notK' : K → False := λ k => nomatch k

-- elim example
def funky (k : K) : False := notK k


-- Predicates!

def isEven : Nat → Prop := λ n => n%2 = 0

-- All

example : ∀ (n : Nat), n = 0 ∨ n ≠ 0 :=
_

-- Exists
example : ∃ (n : Nat), n ≠ 0 := ⟨ 5 , _⟩ 