/-!
# Examples and Excluded Middle
-/

/-!

## Examples

We begin with examples to review and reinforce lessons so far.

### ¬False is Valid
To prove ¬P, where P is an proposition, prove *Not P*, which
is to say, prove *P → False*. You can read that logically as
prove the implication, *P* implies *False*. You can also read
it as saying, construct a function of this type, which would
convert any proof of *P* into a proof of *False*. There is no
such proof of False, so in this context there can be no proof
of P.
-/
example : ¬False :=
λ f => False.elim f

/-!
### No Contradiction Rule is Valid
-/
example (P : Prop) : ¬(P ∧ ¬P) := λ (⟨ p, np ⟩) => np p

/-!

### Transitivity of Implication is Valid
Prove the transitivity of implication. Note carefully
the relationship of this proof to function composition.
-/
example (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) :=
fun pq qr => fun p => qr (pq p)

-- Here it is in Type, from Homework #3
example (α β γ : Type) : (α → β) → (β → γ) → (α → γ) :=
fun ab bc => fun a => bc (ab a)

/-!
### Or Distributes Over And
-/
example (P Q R : Prop) : P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)
| Or.inl p => ⟨ Or.inl p, Or.inl p ⟩
| Or.inr ⟨ q, r ⟩ => ⟨ Or.inr q, Or.inr r⟩

/-!
### At least one of DeMorgan's Laws is Valid
-/
example (A B : Prop) : ¬A ∨ ¬B → ¬(A ∧ B)
| Or.inl na => λ ⟨ a, _ ⟩ => na a
| Or.inr nb => λ ⟨ _, b ⟩ => nb b

/-!
## The Axiom of the Excluded Middle
-/

/-!
Unlike in classical (e.g., propositional) logic, where
the proposition, X ∨ ¬X is *valid*, it's is not valid in
the *constructive* logic of the Lean prover.

In classical logic (propositional and first-order predicate
logic, given any *proposition*, P, we can always obtain a
*proof* of the proposition, *P ∨ ¬P. In propositional logic
it comes from the Boolean algebraic values and functions we
use to represent logical operations. In first-order predicate
logic, it's an axiom. It's called the *law of the excluded
middle*, though it'd better be called an axiom, assumed to
be true.

In the constructive predicate logic of Lean, however, and at
first shockingly, the proposition, X ∨ ¬X is not valid. One
need only remember that there are only two ways to construct
a proof of an *Or* proposition (a *disjunction*) in our logic:
with a proof of *X* or a proof of *¬X*. If we don't have either
proof, we can't provei *X ∨ ¬X*.
-/
example : X ∨ ¬X := _   -- no proof; not *constructively valid*

/-!
We can however, add the law of the excluded middle,
as a new *axiom*, to Lean, as follows.
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
