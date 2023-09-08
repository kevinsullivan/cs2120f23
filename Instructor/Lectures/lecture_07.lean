/-!
# Data Types: Sum, Unit, and Empty Types

Whereas a product type contains *both* a value of
some type, α, *and* a value of some type β, a sum type
contains *either* a value of some type, α, *or* a value
of some type, β. A sum type thus has two constructors, 
each taking a single argument, one taking an α value,
the other taking a β value. We'll use asd constructor 
names *inl* and *inr*, where *inl* takes an argument 
of type α and *inr* takes an argument of type β. So, 
if *(a : α)*, then *inl a* will be an object of a 
sum type; and if *(b : β)* then *inr b* will also 
be a value of a sum type. 

The bulk of this chapter will deal with sum types, 
but then we'll address two very simple types, one
with a single constant constructor, and one with no
constuctors, and thus no values, at all. We will 
call these the *unit* and *empty* types. 
-/

/-!
## Sum Types

We can call such a type a *sum* type. We will again 
give a slightly simplified definition and then explain
how to use the concept with Lean's build-in definitions.
Here are the key ideas:
- Sum will be polymorphic with two type arguments
- It will have two constructors 
  - The first (inl) takes *(a : α)* to construct a value with an α value
  - The second (inr) take *(b : β)* to construct a value with a β value
- To use a value of a sum type we have to be able to handle *either case*
-/
namespace cs2120

inductive Sum (α β : Type) : Type
| inl (a : α)
| inr (b : β)

/-!
### Constructors
-/

def a_sum1 : Sum Nat Bool := Sum.inl 1
def b_sum1 : Sum Nat Bool := Sum.inr true

/-
These definitions assign (1) to *a_sum1* a 
Sum object capable of holding a Nat OR
a Bool, and that contains the Nat value, 1;
and (2) to *b_sum1*, the same type of object 
but now holding the Bool value, true.

By contrast, the following definition assigns
to a_sum2 an object capable of holding a Nat
or a String, and holding the Nat value, 1. 
The value, 1, is the same as in the earlier
example, but it's held in a different type
of object: one of type Sum Nat String rather
than of type Sum Nat Bool. 
-/

def a_sum2 : Sum Nat String := Sum.inl 1

/-!
### Eliminator

A value of type Prod α β always contains both
an α AND a β value, so given an object of this
type we can always return an α value and we can
always return a β value. The *fst* and *snd*
functions serve these purposes.

By contrast, if all we're given an arbitrary
value of type *Sum α β*, while we can be assured 
that it contains a value of type α OR a value of 
type β, but we can't be assured that we'll always
have a value of type α to return or a value of
type β. So we aren't able to define elimination
functions like those for *Prod α β*. 

To make good use of an arbitrary value of type *Sum 
α β* we need to have a little more machinery lying
around. In particular, suppose we have two functions,
one to convert any value of type α into, a String
(or more generally into any type γ), and that we 
also have a funtion to convert any value of type
β into a String (or more generally a value of that
same type γ). The key is is that when given any
value of type Sum α β, we can return a String (or
more generally a value of some type γ) *in either
case*.  

Here's a concrete example. 
-/

def elim_sum1 : Sum Nat Bool → String
| (Sum.inl _) => "It's a Nat" 
| (Sum.inr _) => "It's a Bool"

/-!
We can make this elimination function more
general by passing in and using two functions,
one that converts any Nat to a String and one
that converts and Bool to a string. Here's what
that looks like. 
-/

def elim_sum2 : 
  (Sum Nat Bool) → 
  (Nat → String) → 
  (Bool → String) → 
  String
| (Sum.inl n), n2s, _ => n2s n
| (Sum.inr b), _, b2s => b2s b

/-!
Let's analyze that. It takes arguments as expected,
including Nat-to-String and Bool-to-String conversion
functions. It then uses pattern matching to match the
two possible forms of the given (Sum Nat Bool) value.
If it was constructed using inl with a Nat, then it
applies the Nat to String converter to the Nat to get
the String to return. 

Let's see it in action. We'll define two very simple
functions to convert Nats and Bools to strings: each
will take an argument and just return the same string
we used in the example above.
-/

def nat_to_string (n : Nat) := "It's a Nat" -- argument unused
def bool_to_string (b : Bool) := "It's a Bool" 

/-!
Now we can apply the elimination function we defined.
-/

#eval elim_sum2 a_sum1 nat_to_string bool_to_string
#eval elim_sum2 b_sum1 nat_to_string bool_to_string

/-!
We're now in a position to define a general-purpose
elimination function for Sum type values. Given three
arbitrary types, α, β, and γ, it will take a value,
*s*, of type (Sum α β), a function *α2γ : α → γ*, and
a function, *β2γ : β → γ*, and will return a value of
type γ.  The function doesn't can't know ahead of time
whether a given *s* will contain an *α* or a *β* value,
but it can handle *either case*. 
-/

def elim_sum {α β γ : Type} : (Sum α β) → (α → γ) → (β → γ) → γ
| (Sum.inl a), α2γ, _ => α2γ a  
| (Sum.inr b), _, β2γ => β2γ b 

#eval elim_sum a_sum1 nat_to_string bool_to_string
#eval elim_sum b_sum1 nat_to_string bool_to_string

/-!
### Sum Types in Everyday Programming

Understanding what it takes, and how, to deal with objects of
sum types is another big achievement in this class. It will make
you a better programmer, and it's deeply related to logic, and
in particular to reasoning from proofs of OR propositions. 

Take programming. First, classes in Java and Python are basically
product types: an object of a given type has values for *all* of 
the fields defined by it class. These languages simply don't have 
sum types. You can fake them, but it's complicated. Think about
it. How would you define a Java class whose objects have either
a cat field or a dog field? You can't.

On the other hand, industrial languages such as Rust and Swift, as 
well as functional languages such as Haskell and OCaml, do support 
sum types directly. You now have the basic pattern for programming
with sum-type values: you have to have a way to handle each case.
-/

end cs2120

/-!
### The Sum Type in Lean

Given any two types, α and β, you can form the type, *Sum α β*,
with notation *α ⊕ β*. You create values of this type using the
*Sum.inl* and *Sum.inr* constructors. Note that if all you give
to, say, *inl*, is a value of type α, Lean won't be able to infer
the missing type β. You will have to give an explicit sum type
to the value you're defining.
-/

def s := Sum.inl 1 -- don't know how to synthesize implicit argument
def s1 : Sum Nat Bool := Sum.inl 1
def s2 : Sum Nat Bool := Sum.inr true
#check s1
#check s2

def which : Sum Nat Bool → String
| (Sum.inl _) => "Left"
| (Sum.inr _) => "Right"

#eval which s1
#eval which s2

/-! 
## Wrap-up

It's worth taking stock of the key ideas you've now learned
in this class, which we have formalized in the higher-order
logic of the Lean Prover.
-/

#check {α β γ : Type} → (β → γ) → (α → β) → (α → γ)
#check {α β : Type} → (a : α) → (b : β) → α × β 
#check {α β : Type} → α × β → α   -- α × β is Prod α β 
#check {α β : Type} → α × β  → β
#check {α β : Type} → α → α ⊕ β   -- α ⊕ β is Sum α β 
#check {α β : Type} → β → α ⊕ β 
#check {α β γ : Type} → α ⊕ β → (α → γ) → (β → γ) → γ

#check Function.comp
#check Prod.mk
#check Prod.fst
#check Prod.snd
#check Sum.inl
#check Sum.inr
-- Lean does not have a built-in version of the elimination rule for Sum types

/-!
## Unit Type

Coming soon.
-/

/-!
## Empty Type

Coming soon.
-/
