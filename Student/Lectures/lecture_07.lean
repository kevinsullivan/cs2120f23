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

/-!
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
## Unit Type

The type, Bool, defines a set of two possible values.
A variable of this type carries one bit of information,
and thus distinguishes between two possibiities.

What about a type with just one value? We can certainly
define such a type, and we'll call it the Unit type.
-/

namespace cs2120

/-!
We'll present an only slightly simplified version of
Lean's Unit type here. This will be all you'll need
to use the built-in type.

The type definition is exactly what you'd expect. Unit
is a type with one constant (parameterless) constructor,
*unit*. Thus *unit* is the only value of the Unit type.
-/

inductive Unit : Type
| unit

open Unit 

/-!
The Lean libraries define *()* as a notation for *unit*.
We can do the same with our own types, by the way.
-/

notation "()" => unit

#check ()


/-!
So how much information does a value of this type carry?
Imagine a function that takes some parameter and returns 
a value of this type. Here's one. It takes a Nat value 
and returns a Unit value.
-/

def useless (n : Nat) : Unit := ()
#reduce useless 0

/-!
How much do you learn about *n* from the return value of
this operation? How much information does it give you?
The answer is, nothing at all. You can of course also
pass a value of the Unit type to a function, but it gives
the function no useful additional information and so you
might just as well leave it out. 
-/

def silly : Unit → Nat
| () => 5

/-!
This silly function can't use the value of its argument
to decide even between two possible return values, so it
only has one possible course of action, here it returns
5. In pratice you'd never write code like this because 
it's unnecessarily complex and without harm simplifies 
to just dropping the argument and "returning" the 5.
-/
def silly' := 5

/-!
Now you might think that Unit is a type you've never 
seen before, but it practice it's omnipresent in code
written in such languages as C, C++, Java, etc. It's 
the type of value returned by a function that "doesn't
return anything useful." You know it as *void*.

``` java public class HelloWorld {
    public static void main(String[] args) {
        System.out.println("Hello, World!");
    }
}
```

Here, the *main* method returns *void*. The function
really doesn't return nothing, it returns a value but
one that's useless, and so can be ignored (a compiler
can thus optimize it away in compiled code). 

What you see in this example is that this type is used
in cases where a procedure does something useful that
does *not* include returning a useful result. Here the
useful action is printing a message on the console! We
call such actions *side effects*.

Lean4, like other useful functional languages such as
Haskell, is capable of expressing operations that have
side effects, such as sending output to the console.
Here's *Hello World* in Lean4. 
-/

end cs2120

def main : IO Unit := 
  IO.println "Hello, World!"

-- Lean can run this code for us using #eval
#eval main

/-!
The procedure name is main. It "returns" a result
of (built-in) type, IO Unit. IO is a polymorphic
*monadic* type. This code basically says "run the
side-effecting println routine in an isolated monad
that returns Unit (*nothing*) when it's done." 
  
You can actually write this LEAN code in a file,
e.g., HelloWorld.lean, and compile it like a C++ 
or Java program, then run it, just as you would 
a compiled Java program.

So now you understand the Unit type in Lean. It's a
data type with just one value. It communicates no
information, and is useful mainly as a return value
of an operation that computes nothing but rather is
useful for its *side effects,* here input/output. 

-- Here's Lean's version
-/

#check Unit.unit


/-!
## Empty Type

Just as there's a type, Unit, with just one value, we can
define a type, we'll call it *empty*, with no values at all.
It sounds useless. We won't find it useful in programming
but it plays a vital role in constructive logic. For now
we'll see what we can learn by programming with it. 
-/

namespace cs2120

inductive Empty

/-!
That it: no constructors, no values. The Empty type. 
-/

inductive empty

/-!
What kinds of functions can we write with arguments or
return values of the Empty type? Let's look at three
possibilities: 

- A function that takes Nat and returns Empty
- A function that takes Empty and returns Nat
- A function that takes Empty and returns Empty
-/

def nat2empty : Nat → Empty 
| n => _      

/-!
There's no way to construct a value of type Empty,
because there are no such values, so we can't finish
this definition. There are values of type Nat, so we
can call this function, but it cannot finish because
there's no way to write a return result term of type
Empty.  

If you try to call it using #reduce, it'll tell you 
that the function is defined using "sorry", which is 
to say that the definition is incomplete. (Yes, the
error message is confusing. Sorry about that.)
-/

#reduce nat2empty 5 -- sorry (doesn't properly reduce)

/-!
Now let's write a function that takes an argument of
type Empty and returns a result of some other type: we
might as well just use Nat as an example. 
-/

def empty2nat : Empty → Nat 
| e => nomatch e

/-!
There's something very odd about this function. It
type basically says, "if you give me (e : Empty) I 
can give you a Nat." Suppose, then you do give such
an e. The implementation has to give an result (of 
type Nat) *for each possible case for e*. How many 
cases are there? Zero! So you don't have to give an
answer at all! That's the meaning of *nomatch e*.
You don't have to specify an actual natural number
result for even one case. The implementation is of
the specified type nonetheless. Weird but true and 
it really makes sense if you think hard about it. 
-/

-- You can never call it, so it doesn't matter!
def x := (empty2nat _)    -- can't give a value 

/-!
As another example, we can even define a function
defined to return a value of type Empty provided 
it gets on as an argment.
-/

def empty2empty : Empty → Empty 
| e => nomatch e

def x' := (empty2empty _) -- we can never call it 

/-!
Indeed, there's nothing special about Nat or Empty
as return types in these examples. We can write a
function defined to return a value of any type, given 
a value of the Empty type as an argument. Again, the 
reason is that such a function to to return a value 
for each possible constructor/form of e, but there 
are no constructors/forms, so there are no cases to
consider. We can thus define a generalize polymorphic
function defined to return a value of any arbitrary
type, α, if it's given an argument of the Empty type.
-/

def empty2anytype : {α : Type} → Empty → α
| _, e => nomatch e

end cs2120

/-! 
## Summary So Far

It's worth taking stock of the key ideas you've now learned
in this class, which we have formalized in the higher-order
logic of the Lean Prover. We started with the notion of basic
types, such as Empty, Unit, Bool, Nat, and String. Next we 
saw that if we're given any two types, α and β, we can form
the function type α → β. Furthermore, we saw that there are
not always implementations of such types. For example, even
though Nat → Empty is a perfectly fine function type, there
are no implementations of this type (as you can never write
code to return a value of a type that has no values). 

As it turns out, the function types for which we have been
able to construct implementations are very special types, 
indeed, as we will see going forward. 
-/

-- Product constructionr and elimination
#check {α β : Type} → (a : α) → (b : β) → α × β 
#check {α β : Type} → α × β → α   -- α × β is Prod α β 
#check {α β : Type} → α × β  → β

-- Sum construction and elimination
#check {α β : Type} → α → α ⊕ β   -- α ⊕ β is Sum α β 
#check {α β : Type} → β → α ⊕ β 
#check {α β γ : Type} → α ⊕ β → (α → γ) → (β → γ) → γ


-- Unit construction
#check Unit.unit
-- There is no useful way to use a value of this type

-- There is no constructor for Empty
-- Empty elimination
#check {α : Type} → Empty → α

-- Function composition
#check {α β γ : Type} → (β → γ) → (α → β) → (α → γ)

