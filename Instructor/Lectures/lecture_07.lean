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
## Brief Review

Last time we saw defined polymorphic types that we 
called Box α and Prod α β, where α and β are type
parameters. Here are their types.  
-/

namespace cs2120

inductive Box (α : Type) : Type
| put (a : α)

#check (@Box.put)
def foo := (Box.put "Hello")
#check foo 

/-! 
Here we've renamed the constructor from pair to 
mk to be consistent with Lean's built-in definition
of the Prod type builder.
-/
inductive Prod (α : Type) (β : Type)
| mk (a : α) (b : β)  

/-!
Let's focus on the Box α type. It has one constructor,
*put (a : α)*. This constructor takes an implicit type
argument, α, because *Box* is polymorphic, as well as 
an explicit argument *value* of type α. We can see the
full type of *put* using *@*.
-/

#check (@Box.put)
def jack_in_a_box := @Box.put String "Jack!"

/-!
Leaving implicit arguments enabled, we can leave out 
the explicit type argument.
-/ 
def jack_in_a_box' := Box.put "Jack!"

/-!
It's important to understand that the constructor, 
put, doesn't compute anything: it just "wraps" its
arguments into a term, here, *Box.put "Jack!"*. You
can visualize this as a box, with the label Box.put,
and the contents "Jack!". The term *Box.put "Jack!"*
is a value of type Box String.
-/

/-!
Finally, we saw that we can get the (string) value
from inside a term by *eliminating* the surrounding
structure, giving a name to the string it contains,
and returning the string value by that name. The key
idea is that this is done by pattern matching.

Take the term, *Box.put "Jack!", as an example, if 
we *match* this term with the pattern, "Box.put s",
then, (1) it matches, (2) the name *s* is bound to
the string, "Jack!", and we can return that string 
by returning *s*. We'll write a *get* function to 
do this, and we might as well make it polymorphic.
-/

def get {α : Type}: Box α → α 
| (Box.put s) => s 

#eval get (Box.put "Jack!")

def square (n : Nat) : Nat := n*n

/-!
The *Prod* type builder is analogous except it puts
two values, of possibly two different types,into a
box, and so we need two "elimination functions" to 
get those values, called *fst* and *snd* in Lean. In
Lean the constructor is called Prod.mk, but it's best
to use ordered pair notation for that. 
-/

end cs2120

#check (Prod Nat Bool)  -- a type
#check (Prod.mk 3 true) -- a value (term)
#check (3, true)        -- outfix notation

-- aka *projection functions*
#eval Prod.fst (3, true)
#eval Prod.snd (3, true)
#eval (3, true).1       -- postfix notation
#eval (3, true).2       -- postfix notation

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
in this class. We started with the notions of elementary types,
such as Bool, Nat, and String, and of *values* of such types.
Now we've seen that if we're given any two types, α and β, we 
can always form new types, in several ways. In particular, we 
can form *function* types, *α → β*; *product*  types, *α × β*; 
and *sum* types, *α ⊕ β*. 

### Function types
Given any two type, α and β, we can form the function type, 
*α → β*. The → operator can be understood as taking two types 
and returning a new type, *α → β*. Here's a function showing
the idea: it takes types *α* and *β* and returns a new type, 
namely the function type, *α → β*.  
-/

-- This is a function that returns a *type*
def function_type (α β : Type) : Type := α → β 

#reduce (function_type Nat Bool)
#check (function_type Nat Bool)

/-!

A *value* of a function type is a function 
*implementation* that defines a procedure that, 
*if* it's given (applied to) a value of type *α*, 
then it constructs and returns a value of type 
*β*. 
-/

def negate : Bool → Bool
| false => true
| true => false

/-! 
Here's the same function with a little bit of
new syntax. The syntax above is shorthand for
this notation. The new element here is a match
statement.
-/

-- Learn this new syntax please (match expression)
def negate' : Bool → Bool :=  -- type
  fun x : Bool =>             -- assume given Bool x
    match x with              -- case analysis on x
    | true => false           -- result in case true
    | false => true           -- result in case false


-- A *fun* term expresses a function *implementation*
#check (fun x : Bool =>                
    match x with
    | true => false
    | false => true)

-- Sometimes *fun* is written as Greek lambda *λ*
#check (λ x : Bool =>                
    match x with
    | true => false
    | false => true)

/-!
So does any of this matter to you if you're a data
scientist or ML engineering programming everything
in Python? Let's take a little diversion over into
Python to see. Can you express anonymous function
values values in Python, too? Open lecture_07.py.
-/

/-!
Ok, so now we're back in Lean, in which every function
is strongly and statically typed. Given any two types,
α and β, we can construct the *type, α → β*; and then 
to construct a *value* of type α → β, one must produce a 
procedure that, *if* it's given any *value* of type *α,* 
*then* returns some value of type *β*. 

This is exactly the meaning of a function type, *α → β.* 
Note that it's a conditional. It starts with a hypothesis:
an assumption. A value of a function type *assumes* it's
given a value of the specified type, and then having made
that assumption, it needs to construct and return a value
of the specified type. It's for exactly this reason that 
we can even define a function that takes an argument of 
a type that has no arguments, and that returns a result
of a type that has no values. To wit:
-/

def empty2empty : Empty → Empty := λ e => e

/-!
This example shows that function types are similar 
to logical implication statements, of the form *if a
then b*. A value of a function type (an implementation)
proves the truth of the implication, *if* you can give
me a  value of the argument type, *then* I can return
you a value of the result type, *even if you'll never
be able to provide an argument in the first place.* 

Exercise: Which rule (case) for determining the truth 
of an implication in propositional (Boolean) logic is
most analogous to the function type, *Empty → Empty?* 
Is such a statement true? In a sense, the existence of
a function *implementation* shows the "truth" of such
an expression! If you can define an a implementation of
this type, that would *prove* that *Empty → Empty*.  

Exercise: Give a function type involving the Empty type
that can't be proved. What is the corresponding rule for
evaluating implications in Boolean/propositional logic?
-/

/-!
### Product types
-/

/-!
Given any types, α and β, we can form the product
type, *Prod α β*, written as *α × β* in conventional
mathematical notation. 
-/ 

#check {α β : Type} → (a : α) → (b : β) → α × β 

/-!
Given a value *a : α*, and a value, *b : β*, we can
form a value, *(a, b)* of type *α × β*, shorthand for
*Prod.mk a b*. This constructor application term, as
is, represents the ordered pair, *(a, b)*. It's best
to use this conventional mathematical notation.
-/

#check ("Hello", 5)   -- value of type String × Nat

/-!
To *use* a value of this type you apply one of the
two elimination functions. One "projects" the first
element of a pair, and one the second element. These
functions are thus also called *projection* functions
in ordinary mathematical discourse. 
-/

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

