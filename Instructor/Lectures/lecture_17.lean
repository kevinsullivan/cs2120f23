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
### Not All Classical Reasoning is Constructively Valid

Now here's a proposition that seems that it ought to be
true. It is *classically* true. You can check it using our
validity checker, with A and B as propositional variables.
But we struggled to prove it *constructively* in class, and
there's a good reason for that: it's impossible to construct
a proof of either ¬A or ¬B from a proof of ¬(A ∧ B). This one
of the four DeMorgan's laws is clasically valid but it is
*not valid* in constructive logic. No wonder we had trouble
proving it!
-/

example (A B : Prop) :  ¬(A ∧ B) → (¬A ∨ ¬B)
| nab => _    -- nowhere to go, we're stuck

/-!
So are we stuck in Lean with a logic that's actually weaker
that propositional or first-order predicate logic--capable of
proving fewer theorems? What constructive lacks relative to
classical logics is *the law of the excluded middle* an axiom.

-/

/-!
## The Law of the Excluded Middle as an Independent Axiom
-/

/-!
In classical logics, a proposition is either true or false. In
constructive logic, a proposition, P, is true if there's a proof
of it, or it's false if there's a proof of ¬P, but its validity
is indeterminate if there isn't a proof either way. Consequently,
the proposition, P ∨ ¬P, is not necessarily valid. We might not
have either a proof of P or of ¬P, in which case we can't prove
the disjunction.
-/

example : X ∨ ¬X := _   -- no proof; not *constructively valid*

/-!
A key difference between constructive and classical logic is that
the latter takes the *law of the excluded middle (em)* as an axiom.
It lets you to assume that for any proposition, P, *P ∨ ¬P* is true,
and you can therefore do a case analysis, with one case where P is
true (and in Lean has a proof) and one case where ¬P is true (and
has a proof).

Taking the law of the excluded middle turns constructive logic back
into a classical logic. There is no longer a middle, indeterminate,
state to consider. For each proposition, there are only two possible
states: that it's true or that its negation is true. Acccepting this
assumption as an axiom makes it possible once again to prove that
our variant of DeMorgan's law is valid. So let's dive in and see how
this works.
-/

/-!
First, here's the formal statement of the law of the excluded middle.
It says that if you give and proposition, P, it'll return a proof/value
of P ∨ ¬P.
-/
axiom em (P : Prop): P ∨ ¬ P

/-!
The axiom keywork instructs Lean to accept a definition
without a proof, or implementation. What we have here is
the definition of *em* (for *excluded middle*) as being a
kind of *proof generator:* you feed it any proposition,
*P*, and it returns a *proof* of the proposition, *P ∨ ¬P*.

Now here's the crucial trick: Once you have such a proof,
you can do *case analysis* on it. In the first case (Or.inl p),
you'll have a proof *p : P*. In the second case, you'll have a
proof, np, of ¬P. One has thus excluded the possibility of a
"middle" case, where one doesn't have a proof either way.
-/

/-!
Now, of course, proving a proposition, X ∨ ¬X, is trivial,
no matter what proposition X represents. The validity of
*X ∨ ¬X* follows from a simple application of em to X.
-/


def P : Prop := _
#check em P

/-!
So we've now seen that if given any proposition, P, and
the axiom of the excluded middle, you can always obtain
a proof of P ∨ ¬P for free. The trick now, again, is to do
case analysis on that proof, There are just two cases:
Or.inl with a proof (p : P) or Or.inr with a proof(np : ¬P).
The "middle" case, where we don't don't  a proof either
way, no longer needs to be considered.
-/
example : X ∨ ¬X := em X

/-!
### Use *em* For Classical Reasoning

Accepting the law of the excluded middle as an axiom puts
us back in classical reasoning space. Using it, you can get
yourself proofs of both A ∨ ¬A and B ∨ ¬B, and now, to prove
the validity of the DeMorgan's law variant that had us hung up,
it's just a matter of showing that the proposition is true in each
of the four resulting cases.

HOMEWORK: Complete this proof.
-/

#check em

example (A B : Prop) : ¬(A ∧ B) -> ¬A ∨ ¬B :=
λ nab =>
let proof_of_aornota := em A
let proof_of_bornotb := em B
match proof_of_aornota with
| Or.inl a => match proof_of_bornotb with
              | Or.inl b => False.elim (nab (And.intro a b))
              | Or.inr nb => Or.inr nb
| Or.inr na => Or.inl na
