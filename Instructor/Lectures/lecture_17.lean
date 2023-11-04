/-!
# Examples and Excluded Middle
-/

/-!

## Examples

We begin with examples to review and reinforce lessons so far.

### ¬False is Valid (True Under Any Interpretation)

This example will teach and reinforce the idea that, to prove
¬P, for any proposition P, you show that an assumed proof of
P leads to a contradiction (a proof of False). Formally, you
show P → False (by implementing a function of this type), from
which it follows that P is uninhabited (there is assuredly no
proof).
-/
example : ¬False :=
λ f => False.elim f


/-!
### The *No Contradiction* Rule is Valid

This example teaches and reinforces the idea that a proof,
np, of a proposition, ¬P, works like a function, namely one
that takes a proof of P as an assumed argument, and that in
this context constructs and returns a proof of False. The
upshot is that if you have in your context both a proof, p,
of some proposition, P, and a proof, np, of ¬P, then you
have both a function, np: P → false, and an argument, p : P,
from which you can derive a proof of False by applying np
to p: (np p).
-/
example (P : Prop) : ¬(P ∧ ¬P) :=
λ (⟨ p, np ⟩) =>
  np p


/-!
### Transitivity of Implication is Valid
Prove the transitivity of implication. Note carefully
the relationship of this proof to function composition.
-/
example (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) :=
fun pq qr =>
  fun p =>
    qr (pq p)

-- Here it is in Type, as function composition from HW#3
example (α β γ : Type) : (α → β) → (β → γ) → (α → γ) :=
fun ab bc =>
  fun a =>
    bc (ab a)

/-!
### Or Distributes Over And

This example emphasizes how one reasons when given an
assumption that some disjunction is true: it's by case
analysis. There are two different ways in which that
assumed disjunction could be true, and you need to show
that the conclusion follows *in either case*. So first
you assume the first case holds, and show the conclusion
follows, then you assume the second case and show that
the conclusion still follows. Therefore the conclusion
follows in either case. Of course in general you might
have to do additional complex reasoning for each case.
-/
example (P Q R : Prop) : P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)
| Or.inl p => ⟨ Or.inl p, Or.inl p ⟩
| Or.inr ⟨ q, r ⟩ => ⟨ Or.inr q, Or.inr r⟩

/-!
### At least one of DeMorgan's Laws is Valid

This example reinforces the idea that if you have to
return a proof of a negation, ¬X, what you really have
to return is a function of type X → False. Note that
the return values here are lambda expressions.
-/
example (A B : Prop) : ¬A ∨ ¬B → ¬(A ∧ B)
| Or.inl na =>
  λ ⟨ a, _ ⟩ => na a
| Or.inr nb =>
  λ ⟨ _, b ⟩ => nb b

/-!
## The Law of the Excluded Middle as an Independent Axiom
-/

/-!
Unlike in classical (e.g., propositional) logic, where
the proposition, X ∨ ¬X is *valid*, it's is not valid in
the *constructive* logic of the Lean prover. Before you
go on, remind yourself of why it's valid in propositional
logic. Answer: it's by case analysis on possible values of
X.

In classical (propositional, first-order predicate) logic,
given any *proposition*, P, P is either true or it is false,
and in either case P ∨ ¬P is true, and so it's also *valid*.
This principle of logical reasoning is called *the law of
the excluded middle*.

In the constructive predicate logic of Lean, however, X ∨ ¬X
is not valid. Why? There are only two ways to construct a proof
of a *disjunction*: either giving a proof of *X* or giving a
proof of *¬X*. We don't have either to start with, so there's
no way to proceed.
-/
example : X ∨ ¬X := _   -- no proof; not *constructively valid*

/-!
We can however, add the law of the excluded middle,
as a new *axiom*, to the constructive logic of Lean, as
follows.
-/
axiom em (P : Prop): P ∨ ¬ P
/-!
The axiom keywork instructs Lean to accept a definition
without a proof, or implementation. What we have here is
the definition of *em* (for *excluded middle*) as being a
kind of *proof generator:* you feed it any proposition,
*P*, and it returns a *proof* of the further proposition,
*P ∨ ¬P*.

Once you have such a proof, you can do *case analysis*
on it: in the first case, you'll have a proof of *P*,
and in the second case, you'll have a proof of ¬P.
One has thus excluded the possibility of the "middle"
case, where one doesn't have a proof either way.
-/

/-!
Now proving X ∨ ¬X is trivial. It follows by a simple
application of em to X.

Finally, we've see that if given any proposition, P, and
the axiom of the excluded middle, you can always obtain
a proof of P ∨ ¬P for free. The trick is then to do case
analysis on that proof, with just two cases: Either P is
true, and you can assume you have a proof, p, of P; or P
is false, and you can assume you have a proof, np, of ¬P.
The cases will be either *Or.inl p*, where (p : P), or
*Or.inr np*, where (np : ¬P). The "middle" case, where we
don't have a proof either way, is excluded.
-/
example : X ∨ ¬X := em X

/-!
### One of DeMorgan's Laws is *Not* Valid in Lean

##

Now here's a proposition that seems that it ought to be
true. It is *classically* true. You can check it using our
validity checker, with A and B as propositional variables.
But we struggled to prove it *constructively* (using Lean).
From a proof of ¬(A ∧ B) (A ∧ B → False), it's impossible
to derive a proof of ¬A or a proof of ¬B, and we'd need at
least one of those proofs to prove ¬A ∨ ¬B. This proposition
is *not valid* in the constructive logic of Lean. No wonder
we had trouble proving it.

### Use *em* For Classical Reasoning

Accepting the law of the excluded middle as an axiom puts
us back in classical reasoning space. Using it, you can get
yourself proofs of both A ∨ ¬A and B ∨ ¬B, and now it's just
a matter of showing that the proposition is true in each of
the four resulting cases.

HOMEWORK: Complete this proof.
-/

example (A B : Prop) : ¬(A ∧ B) -> ¬A ∨ ¬B :=
λ nab =>
let aornota := em A
let bornotb := em B
_
