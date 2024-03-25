/-!
## Three Propositions 
Here are three propositions: B, M, and K.
B and M are true because each has at least
one proof. K on the other hand has no proof,
so is false, and ¬K is provably true.
-/

inductive B : Prop
| paid
| classes

inductive M : Prop
| paid
| classes

inductive K : Prop

-- ¬K is provably true  
example : ¬K := λ (k : K) => nomatch k

/-!
## Rules of Logical Reasoning

The next section marches through each of the connectives 
and quantifiers of predicate logic; presents the introduction
(proof construction) and elimination (proof utilization) rules
for each; explains how these rules define their intended logical
meanings; and gives a few examples of proofs using each of the
rules.  
-/


/-! 
### And ∧

Given propositions, B and M, And B M, usually written B ∧ M,
is the proposition that is true if and only if both B and M
are true. This is the case in constructive logic if and only 
if we have a proof, b, of B and a proof, m, of M. In that case
we can apply the introduction rule for and, And.intro in Lean,
to construct the pair of proofs, ⟨ b, m ⟩, which we define to
be a term/proof of B ∧ M. 
-/

/-!
#### Proof construction (introduction)
-/

-- B ∧ M is true. Here's a proof: a term of type (And B M)
example : And B M := And.intro B.paid M.classes

-- We can give names to proofs terms. Here we name our proof b_and_m_true 
def b_and_m_true : B ∧ M := And.intro B.paid M.classes

-- There's infix notation for And, namely ∧ 
theorem b_and_m_true' : B ∧ M := And.intro B.paid M.classes

-- There's notation for And.intro, taking two proofs, namely ⟨ _, _ ⟩ 
example : B ∧ M := ⟨ B.paid, M.classes ⟩ 

-- Elimination examples
example : ∀ (P Q : Prop), P ∧ Q → P := λ _ _ pandq => pandq.left
example : ∀ (P Q : Prop), P ∧ Q → Q := λ _ _ pandq => pandq.right

-- example
theorem foo : B ∧ ¬K := 
  ⟨ B.paid , 
    λ k => nomatch k 
  ⟩

example : B ∧ ¬K := foo

/-!
#### Proof utilization (elimination)

The elimination rules enable you to use a proof,
⟨ b, m ⟩ to obtain a proof of B, or to obtain a
proof of M, namely by destructuring the pair using
pattern matching to obtain either the first or the
second field. 
-/

example (P Q : Prop) : P ∧ Q → Q ∧ P :=
λ (h : P ∧ Q) => ⟨h.2 , h.1⟩ 

example (P Q : Prop) : P ∧ Q → Q ∧ P 
| And.intro p q => And.intro q p

example (P Q : Prop) : P ∧ Q → Q ∧ P 
| ⟨ p, q ⟩  => ⟨ q, p ⟩ 

example (P Q : Prop) : P ∧ Q → P ∨ Q
| ⟨ p, q ⟩ => Or.inl p


/-!
## Or 

Given propositions, B and M, *Or B M*, written B ∨ M, is 
the proposition that is true if and only if at least one 
of B and M is true. In constructive logic that would mean we
can construct a proof, (b : B), or we can construct a proof, 
(m : M). The Or connective provides two proof constructors:
Or.inl b, or Or.inr m. So whereas a proposition, B ∧ M has
only one proof constructor, intro, taking a pair of proofs, 
Or has two proofs constructors, one taking a proof (b : B), 
the other taking a proof (m : M). Consequently, there's only
one form of proof for a conjunction (a pair of proofs), but
an actual or assumed proof of B ∨ M can have one of the two 
forms, each carrying just one proof object. 
-/

/-!
### Introduction 

In general you have to decide which disjunct to prove.
In this example, you have only one choice, as there's no
way to get a proof of K.
-/
example : B ∨ K := Or.inl B.paid

/-!
### Elimination

To *use* a proof of B ∨ M that you already have, or that you
have assumed you have, you have to *analyze* it to determine
whether it's of the form Or.inl b, in which case you then have 
a proof, (b : B) as you wish; or it's of the form Or.inr m, in 
which you have a proof, (m : M). 

In other words, Or elimination rule says that if P and Q are 
propositions, and you want to show that if (P ∨ Q) is true then 
so is some conclusion R, you do it by showing that from a proof
of (P ∨ Q) you can derive a proof of R *in either case*. That 
is, *case analysis* is the way that you use of proof of P ∨ Q.
-/

example : ∀ (P Q R : Prop), (P ∨ Q) → R :=
λ P Q R porq => 
  -- case analysis on the assumed proof of P ∨ Q
  match porq with
  | Or.inl p => _   -- filling this hole proves P → R
  | Or.inr q => _   -- filling this hold proves Q → R

/-
Here's an example. In this case, B ∨ K can be
proved only with a proof of B, as there is no
proof of K. The same case analysis applies, but
in the second case there's an assume proof of K,
which gives rise to a contradiction. You can use
this to dismiss this case as not being possible. 
-/
example : B ∨ K → B :=
λ bork => match bork with 
| Or.inl b => b
| Or.inr k => nomatch k   -- can't happen

/-!
Here's another example that basically 
restates the entire Or elimination rule
but using propositional identifiers that
model some imaginary world in which the
grass is wet if it's either raining or 
the sprinkler is running.
-/
example : 
  -- assume three arbitrary propositions
  ∀ (Raining Sprinkling Wet : Prop), 
    -- if it's raining or sprinkling
    (Raining ∨ Sprinkling) → 
    -- and if when it rains the grass is wet (one case)
    (Raining → Wet) → 
    -- and if when the sprinkler is on the grass is wet (second case)
    (Sprinkling → Wet) → 
    -- then the grass is wet, because it's wet *in either case*
    Wet := 
λ _ _ _ rors rw sp => 
match rors with
| Or.inl r => rw r 
| Or.inr s => sp s

-- Here is the "rule" in a more abstract form

example : 
  ∀ (P Q R : Prop), (P ∨ Q) → (P → R) → (Q → R) → R := 
λ _ _ _ rors rw sp => 
match rors with
| Or.inl r => rw r 
| Or.inr s => sp s

/-!
And soon we'll meet Lean's tactic language. Here's the
same proof expressed in that form!
-/

example : 
  ∀ (P Q R : Prop), 
    (P ∨ Q) → 
    (P → R) → 
    (Q → R) → 
    R := 
by -- by: starts construction of a program or proof using tactics
  -- intros: assume arguments
  intros P Q R rors ptor qtor
  -- cases: case analysis
  cases rors with
  -- case were r is true
  -- exact: takes complete proof term for current goal
  | inl p => exact (ptor p)
  -- case where
  -- apply: like exact
  | inr q => apply (qtor q)

example (P Q : Prop) : P ∨ Q → Q ∨ P 
| Or.inl p => Or.inr p
| Or.inr q => Or.inl q
    
/-!
### Not (¬)

If P is any proposition, then so is ¬P. To prove
that ¬P is true, and equivalently that P is false,
we show that P being true is impossible: that it'd
lead to a contradiction. We show this by assuming
that P is true and showing that in that context we
can derive a proof of False (which can't exist as
False is defined to be an uninhabited type). We do
this in turn by showing that there is a function of 
type P → False. If given *any* (p : P) it'd return 
a proof of False. That cannot happen, so no such 
(p : P) can exist. As P probably has no proofs, it
can be judged to be false.  
-/

/-! 
#### Introduction: Proof by Negation

In everyday pencil and paper logic, the way you prove
¬P is to show that assuming P leads to a contradiction.
This is called *proof by negation*. 

Note that it is not the same as proof by contradiction!
Whereas proof by negation is used to prove a proposition
of the form, ¬P, by showing that assuming P leads to a 
contradiction.

In proof by contradiction, your goal is to prove a 
proposition of the form P (rather than ¬ P). The way
you do it is to assume that P is false, i.e., that ¬P
is true, and you show that that assumption leads to a 
contradiction. That in turn proves ¬(¬P). In classical
logic you then use the law of negation elimination (that
¬¬P → P) to deduce P, which is what you set out to show.

In constructive logic on the other hand, ¬¬P → P is not 
an axiom, as we'll now see, so proof by contradiction is
simply *not a valid reasoning principle* in constructive
logic, as we'll see next.

In the following example we prove that Marko doesn't 
attend UVa--- that the proposition, *K,* is false. That
means that ¬K is true, and that we can prove it. Recall
that ¬K (a proposition, and a type in Lean) is the type
K → False. So to prove ¬K, we need to show that there is
a function of type K → False. The only condition under
which there is such a function is that K has no proofs. 
Here it goes.
-/
def notK : ¬K := λ k => nomatch k 

/-!
#### Elimination

In classical predicate logic, negation elimination is the 
rule that one might call *double negation elimination*:
*∀ (P : Prop), ¬¬P → P*. Example: If it's not not raining
then we can conclude it's raining. This isn't the case in
constructive logic. 

Let's see what happens if we try to prove that the rule 
is valid. First, let's replace the ¬P notation with the
equivalent P → False. Then ¬(¬P) is ¬(P → False), and that
in turn is (P → False) → False. In English you can read
this as saying it's false that P is false. The issue is 
that knowing this in constructive logic is not enough to
derive a proof of P. Let's try.
-/

example : ∀ (P : Prop), ¬¬P → P :=
λ P nnp => _

/-!
There's no way to make any progress here. There's just
not "enough stuff" in a proof of ¬¬P to get an actual,
fully elaborated, proof of P, which is what we need in 
*constructive* logic to judge P to be true. Study the
preceding example using Lean to convince yourself that
there's no way forward. The take-away message is that
this is a *non-constructive* law of classical logic. We
can of course just stipulate it as an extra *axiom*,
but then whenever we deduce *P* from *¬¬P* we don't get
an actual proof of P.

Now in constructive logic there's another "law" of 
ordinary predicate logic that is highly intuitive but
also non-constructive and thus not valid in Lean. It
is called the *law of the excluded middle*. This law
says, in English, that every proposition is either 
true or it's false; there's no indeterminate "middle" 
state.

With this law in hand, negation elimination is again
valid. Suppose we have a proof of ¬¬P and we want a
proof of P. The trick is that with the law of the 
excluded middle, there are only two possibilities: 
P is true, or P is false. In the first case, our goal
of proving P is done! In the second case, ¬P is true,
be we've already assume that ¬¬P is true. This is a
contradiction, which can't happen, so this case can 
be dismissed.

In this first example, we assume P is any proposition,
and further that we have a proof of P ∨ ¬P. We show 
that in that context we *can* complete the proof of 
¬¬P → P; and the trick is by case analysis on that
assumed proof of P ∨ ¬P.
-/

example (P : Prop) : (P ∨ ¬P) → (¬¬P → P)
| pornp => match pornp with
  | Or.inl p => λ _ => p
  | Or.inr np => λ nnp => nomatch (nnp np)


/-!
In Lean, the axiom of choice is given by a function,
called em, defined in the Classical namespace, that
takes any proposition, P, as an argument and returns
a *proof* of P ∨ ¬P. Given any proposition, P, you can
thus have a proof of P ∨ ¬P *for free*, without having
to provide either a proof of P or a proof of ¬P. This
is what makes "excluded middle" a *non-constructive*
reasoning principle. Here's how we could write the
preceding proof using Classical.em. Note that we no
longer provide an assumed proof of P ∨ ¬P explicitly. 
-/

#check Classical.em

example (P : Prop) : (¬¬P → P) :=
match (Classical.em P) with
  | Or.inl p => λ _ => p
  | Or.inr np => λ _ => by contradiction

-- The "contradiction" tactic looks for a contradiction in the context
-- and if there is one, it uses False elimination to finish the proof.
-- Here the contradiction is in the assumption of proofs of ¬P and ¬¬P

/-!
What we've done is to prove the validity of (double) negation
elimination as a reasoning principle from the assumption of the
law of the excluded middle: *∀ (P : Prop), (P ∨ ¬P) → (¬¬P → P)*.
It turns out that the law of the excluded middle can in turn be
proved from (a) assuming (double) negation elimination, the axiom
of choice, and the axiom of "functional extensionality", which
holds that if two functions return the same result on every input
then the two functions are equal. You can see what this looks
like, you're interested, by visiting the definition of *em* in 
Lean's math library. 
-/

/-!
Putting this in terms of an traditional (advanced) course in 
logic, we can say that if negation elimination is valid then
so is proof by contradiction, *and vice versa*. Both of these
reasoning principles are *non* constructive, but can easily 
be added to Lean as axioms.
-/


/-!
### Implication 
-/

/-!
In classical logic, an implication, P → Q, is the assertion,
not necessarily true, that if P is true then you can deduce
that Q is also true. In short, "if P then Q." To prove that
*P → Q* is true in classical logic, you *assume* P is true
and show that in that context Q must be. 

In constructive logic, on the other hand, assuming that P is 
true is tantamount to assuming that there is a proof, p of P: 
that we have our hands on a value/proof, (p : P). So to prove
P → Q in constructive logic, we need to show that *if we have 
any proof of P, then we can always derive some proof of Q. 

#### Introduction 

In other words, to show that P → Q is true, we show that we 
can define a function (any function) of type P → Q. What does
such a function definition look like? It assumes it's given an
argument, p, of type P, and in any possible case for the shape 
of p, that we can construct and return a proof of Q. 
-/

-- Example

def one_not_eq_zero (n : Nat): n = 1 → n ≠ 0 :=
λ (neq1 : n = 1) => λ neq0 => by 
  rw [neq1] at neq0
  cases neq0

/-!
#### Elimination

Remember that the elimination rule for a logical connective
tells you how to *use/consume* rather than *construct/produce*
a proof. How do you *use* a proof of an implication? Well, it's
a function, and the way you use it is to apply it to arguments
of the right type.

The theorem we just proved, for example, says that if some
natural number, n, is equal to zero, then it can't be equal
to one. The proof is a function that converts and proof of 
n = 1 into a proof of n ≠ 0. Let's see this in action.  
-/

#check one_not_eq_zero 1 (Eq.refl 1)

/-!
In addition to illustrating the elimination rule, we
also see here for the first time how we can impose a
*pre-condition* on the value of an argument passed to
a function. Here the precondition is n = 1, *enforced*
by the need for a proof of n = 1. If n = 5, you cannot
construct such a proof, so you can't apply the function!
-/

/-!
### Predicates

A predicate is a parameterized proposition. Applying
a predicate to argument (of the right type) yields a
proposition. 

Here's an example: a predicate that takes any natural 
number, n, as an argument, and returns the proposition
that that *particular* value, n, is even. Applied to
(1 : Nat), for example the return value will be the 
proposition that 1 is even. 

So in our terms, a predicate is a function from given
values to propositions (that can be) about those values.
Consider an isEven predicate, taking a natural number,
n, and returning the proposition that n % 2 = 0. 
-/ 
def isEven (n : Nat): Prop := n % 2 = 0

-- isEven predicate applied to argument is a proposition
#check isEven 0
#check isEven 1


#reduce isEven 0
#reduce isEven 1

/-!
We can compute the propositions that these
predicate/function applications expressions
reduce to using #eval or #reduce.
-/
#reduce isEven 0
#reduce isEven 1

/-!
Ok, so what propositions do these predicate
applications return?

Take the expression (isEven 1). Evaluating it
starts with the definition of isEven n (namely 
n % 2 = 0) and replaces the formal parameter, 
n, with the actual parameter, 1, yielding the
expression, 1 % 2 = 0. But the reduction then
goes further, reducing 1 % 2 to 1. Now there
are no further reductions to perform, and the
final result is the proposition, 1 = 0.

Similarly, (isEven 0) reduces to 0 = 0. But
what about (isEven 2)? Well, that first becomes
2 % 2 = 0, but then 2 % 2 is further reduced to
0, ending with the proposition 0 = 0. Now you
will see when you get propositions alternating
between 
-/

#reduce isEven 2
#reduce isEven 3
#reduce isEven 4
#reduce isEven 5



/-!
### For All (∀)

In classical logic, the form of a universally
quantified proposition is ∀ (p : P), Q. This
says that for *any* (p : P) you can pick, Q is 
true. 

That said, the more usual form of a *forall* in
practiceis ∀ (p : P), Q p, with Q now being a 
predicate with argument, p. The (Q p) is a
proposition *about p*. The overall proposition
is true if (Q p) is true for every value of P. 

For example, given our isEven predicate, of type
Nat → Prop, we can for a proposition that states
that *every natural number is even*: ∀ (n : Nat), 
isEven n. It's not true, of course, but it is as
good a proposition as any other. 
-/

example : ∀ (n : Nat), isEven n := _  -- not true

/-!
#### Introduction

In constructive logic, the introduction, or proof 
construction, rule for this form of ∀ proposition 
(a "universal generalization) is to *assume* you 
are given an *arbitrary* argument of the right type, 
and in that context show that you can produce a 
proof/value of the concluding proposition/type.

If that sounds a lot like a function, that is 
exactly what you need to prove such a proposition:
define a function that takes *any* natural number, 
n, for example, that returns a proof of isEven n. 

There's no proof of that, but here's another one
that is true.
-/

def zornz : ∀ (n : Nat), n = 0 ∨ n ≠ 0 :=
λ n => match n with
| 0 => (Or.inl (Eq.refl 0))
| (_ + 1) => Or.inr (λ h => nomatch h)
/-!
In sum, a proof of ∀ (p : P), Q p is a function:
one that assumed it's given an arbitrary value of
type p and that in that context constructs a proof
of Q p. Such a function turns *any* value of type 
P into a proof of Q p, so Q must be true of *all*
P. 
-/

/-!
#### Elimination

How do you use a proof of a universal generalization,
∀ (p : P), Q p? Well it's a function of type P → Q p,
taking any value (p : P) to a proof of (Q p): that p
satisfies the predicate Q. To use such a function, you
apply it to a specific, actual parameter value, p, to
obtain a proof of (Q p) for that particular p. This
operation of reducing a proof that everything of a 
certain type has some property (Q) to a proof that one
particular value of that type has that property is
called universal specialiation. 
-/

#reduce isEven 0
#reduce isEven 1

/-!
Now there's something interesting going on in the
type of function we're talking about here: from any
value, p: P, to any proof of the proposition, (Q p). 
Remember again that Q is a predicate, and so (Q p) 
is a proposition, and in practice usually about p.
-/

-- In Lean "variable" introduces assumed objects into the environment

variable
  (P : Type)
  (Q : P → Prop)
  (R : Prop)
  (t : P)

#check P
#check Q

#check Q t
#check ∀ (p : P), Q p

/-!
#### Function types as special case of ∀ types

So, what if the proposition after the comma doesn't depend 
on the formal argument, (p : P), to the predicate, Q? This 
is just the special case where "Q" has already ignored its
argument and so has been reduced to a constant proposition.
-/

#check ∀ (x : P), R

/-!
What's remarkable now, is that Lean reports back to us that
this proposition, ∀ (_ : P), R, is the type, P → R : Prop!
-/



/-!
### Exists (∃)
-/  := _

-- general form
example : ∃ (p : P), Q p := _

-- introduction
def exists_even_nat : ∃ (n : Nat), isEven n := ⟨ 2 , rfl ⟩ 

-- elimination rule

def foo : (∃ (n : Nat), isEven n) → True
| ⟨ n', pf ⟩ => _

example : ∃ (n : Nat), n ≠ 0 := ⟨ 5 , _⟩ 


/-!
### Equality: A preview
-/

/-!
Equality in Lean is defined by a parameterized type,
Eq. The type is parameterized by *two* values of any
type, yielding a proposition. For example, *Eq 3 4* 
can be read as

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a
-/



#check 1 = 0
#check Eq 1 0

#check Eq.refl 1

-- Lean reduces expressions 
example: 1 + 1 = 2 := rfl

-- can't be proved
example : 1 = 2 := Eq.refl 2

/-!
## Inductive Families

The definition of Eq is different from anythiing we've seen 
so far: a type parameterized (or "indexed") not by other types
but by values of other types. What this construct does is to
give rise to a different type, or here *proposition*, for each 
value of the arguments. The constructors then tell you what to
do to construct proofs for each such proposition. 

As an example, let's reformulate our definition of evenness
using this structure. We want a parameterized type, each
specialized instance of which we can read as a proposition
asserting that its argument is even.
-/

inductive IsEven : Nat → Prop
| zero_is_even : IsEven 0
| even_plus_2_even : ∀ (n : Nat), IsEven n → IsEven (n + 2)

open IsEven 

example : IsEven 0 := zero_is_even

example : IsEven 4 := 
  even_plus_2_even
    2 
    (even_plus_2_even 
      _     -- Lean infers this value
      _     -- But you need to give a proof
    )

/-!
We've now seen *two* "inductive families" of propositions
with corresponding proof constructors applicable to any
proposition in this family. The first was Eq. Now we've 
also seen a *logical* definition of *evenness*, in the 
form of the IsEven parameterized "proposition builder".  
-/