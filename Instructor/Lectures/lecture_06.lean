/-!
# Data Types

In this class so far, we've used a few data types that
Lean provides for us, namely Bool, Nat, and String. We
will often want to reason about or compute with values
of other types. How do we define new data types in Lean?
This chapter will teach you how.
-/

/-!

## Enumerated Types
Suppose we want to represent the objects in the child's
game, Rock Paper Scissors. Let's think of these objects
as being of a single type, let's call it object. There 
are three objects of this type. We can enumerate them.
They are *rock*, *paper*, and *scissors*. A type with a
finite set of objects is called an *enumerated type*. 

We'll define this game-relaeted type as an example. With
this and another data type in hand, we'll then specify 
the rules of the rock paper scissors game.

We'll begin by enclosing our definitions in a namespace, 
RPS, short for *rock paper scissors*. All names within this 
namespace are prefixed implicitly by RPS, avoiding possible
naming conflicts with other names already defined by Lean.
-/

namespace RPS

-- Here's the definition of our RPS object type
inductive Object : Type
| rock
| paper
| scissors

/-!
Let's look at the elements of this definition:
- The inductive keyword indicates that we're going to define the set of objects of a new type by giving rules for how those objects can be constructed. 
- The name we're giving to our new type is *object*. 
- The colon followed by Type specifies that the type of object is Type. It's a type.
- Finally we have three "construction rules," or *constructors* for this type. 
Each constructor in this example just a name and no arguments. In
general, constructors can have arguments, as we'll see. With this
definition, there are only three values of our *object* type: *rock*, *paper*, and *scissors*. 
Check it out.-/

-- To avoid having to write object.rock (etc) we open the namespace
open Object

#check rock       -- type is object
#check paper      -- type is object
#check scissors   -- type is object
#check Object     -- By golly it's a Type!

/-!
Now that we have this new data type, we can think about 
defining functions that operate on values of this type. To 
illustrate this point, let's define a function that takes two 
objects and returns of a game where the first is played against
the second. There are three possible outcomes in this game--win, 
lose, and tie--so we can't use Bool, with only two values. We 
need another type. Let's call it result. 
-/

inductive Result : Type
| wins
| loses
| ties

open Result

/-!
Cool, now we can write the function we want. Let's call it
play. It will take two *objects* and return a *result* that
indicates the outcome when the first object is played against
the second. For example, the first rule, below, specifies 
that scissors ties when it's played against scissors, while 
scissors wins when it's played against paper. 
*-/

def play : Object → Object → Result
| scissors, scissors => ties
| scissors, paper => wins
| scissors, rock => loses
| paper, scissors => loses
| paper, paper => ties
| paper, rock => wins
| rock, scissors => wins
| rock, paper => loses
| rock, rock => ties

end RPS

/-!
## Polymorphic Types

It's often the case that we want a data type that
can contain objects of some arbitrary other type. 
In Java, for example, a HashList can contain objects
of other types. You can have a HashList of Strings,
for example. 

### Example: Box α 

A simple example is a polymorphic type, perhaps called 
Box, each value of which holds some value of some other 
type. We can have a Box that can hold a Nat, for example,
a Box that can hold a string, and a Box that can hold a
Bool. The type of object that a Box can hold is part of 
its type. They're all Boxes, but each one is specialized 
to hold an object of a specific type. 

Compared to our simple enumerated type, we'll need to
use two new (to us) capabilities:
- Be able to specify the type of object a Box can hold
- Define a constructor that takes an object of that type 

### Data Type

Here's a definition that will work for us.
-/

inductive Box (α : Type) : Type
| put (a : α)

/-!
Let's explain it.
- *inductive* is a keyword as explained above
- Box is the name of our now polymorphic data type
- α is a type argument: the type of object that can fit a given Box
- Given (a : α), (Box a) is a type: a type of Box that can fit α's
- put is the sole constructor, taking an argument (a : α)
Let's see how to use this definition to put some things in boxes
-/

/-!
### Constructor

Here are example using the *put a* constructor to put some
values in some Boxes. In the first example, note that the
*type* of boxed_nat is not *Box* but *Box Nat*. *Box* is what
we can call a polymorphic *type builder*. Given a type, α, 
*Box α* is a type: a type of Box cabable of holding a value
of type α.  
-/

def boxed_nat : Box Nat := Box.put 1  -- put 1 in a (Box Nat)
open Box                              -- relief from writing Box...
def boxed_bool := put true            -- put true in a (Box Bool)
def boxed_string := put "Hello!"      -- "Hello" in a (Box String)

/-!
It's important to understand that (put 1) is a term of 
type Box Nat, (put true) is a term of type Box Bool, and
(put "Hello!") is a term of type Box String. Constructors
are like functions in that you can form application terms,
but these terms don't compute anything. They simply *are*
values of their given types. 

It's also important to understand that the constructors of
a polymorphic type are themselves polymorphic. They implicitly
take type arguments. The *put* constructor for example takes
both an *implicit* type argument, α, and an *explicit* value
of that type. In this sense, they behave like the polymorphic
functions we've already seen. Go back and review the work we
did on a polymorphic identity function to remind yourself of
the details. You can see the truth of what we're saying here
by using #check, with an @ sign to make implicit arguments
explicit.
-/

#check (@put)     -- @put : {α : Type} → α → Box α

/-!
### Eliminator

Having *put* some value in a Box, we will often want to
get it back out. To do this, we need to *eliminate* the box
to get at what's inside. The way we eliminate an object to
get at what's inside it is by pattern matching! We define
a (polymorphic) function, let's call it *get*, that takes
an object of type *(Box α)* for some type, α, and that
uses pattern matching to (a) determine which constructor 
was used to construct the box, (2) give a name to the value
that was provided to that constructor when the Box was 
built. Then we just return that now named thing inside
the box. 
-/

def get {α : Type} : Box α → α 
| (put o) => o

/-!
Let's analyze that. The function name is get. It's
polymorphic with implicit type argument α. It takes
a value of type *Box α* and from that argument it
derives and returns a value of type α. The way it
does this is by pattern matching on the argument
of type *Box α*. There's only one way that such an
argument can exist: it *must* have been constructed
by the *put* constructor applied to *some* object of
type α. By pattern matching we give that object the
name, o. That's the key! Now we have a handle on
the object inside the box, and all that's left to
do is to return it. Study this example deeply and
be sure you fully understand what's going on. Here
are examples to show it in operation. Remind yourself
of the definitions of boxed_nat, etc., from above,
as needed to see that the results are as expected.  
-/

#eval get boxed_nat     -- expect 1
#eval get boxed_bool    -- expect true
#eval get boxed_string  -- expect "Hello!"

/-!
## The (Polymorphic) Product Type

From basic algebra you should recall the concept of an
*ordered pair*. For example, in the Cartesian plane, we
can identify a point as an ordered pair of real numbers.
The pair, *(0.5, 1.0)*, for instance, specifies the point
*1/2* unit to the right of the origin and *1* unit up. We 
now want you to think of *ordered pair of real numbers* as 
a type, with (0.5, 1.0) as one of many values of this type.

Now think of an ordered pair as a new kind of box that has
*two* objects inside it. Let's call this new kind of box a
*Prod* box. *Prod* is short for product, as in the *product*
of two numbers. The ordered pair, *(0.5, 1.0)*  would then
be a value of a *Prod* box holding two *real numbers*.

Of course there's no reason not to generalize the concept
to contents of different types. So we could have a Prod box
capable of holding two *Nat* values, two *Strings*, or two
*Bools*. For example.

Moreover, there's no reason not to allow ordered pairs of
different types of values. For example, considered ordered
pairs of String and Nat values. The pair ("Love", 4) is an
example. 

Indeed, given any arbitrary types, α and β, we can define
a type of ordered pairs whose first values are of type α
and whose second values are of type β. We now have the idea
of the polymorphic *product* type. It's a *type builder* with 
*two* type arguments. It still has a single constructor, 
here called *pair* that takes two arguments,
(a : α) and (b : β). The term *(Prod.pair a b)* then represents 
the ordered pair, (a, b) : Prod α β. Lean provides the notation 
*(a, b)* for any such pair.  
-/

namespace cs2120

inductive Prod (α β : Type) : Type
| pair (a : α) (b : β)

open Prod 

/-!
### Constructor
Our pair constructor is polymorphic with two implicit type arguments,
α and β, and two explicit arguments, (a : α) and (b : β). The types
are inferred. The term, *(pair a b)* is then of type *Prod α β*. Take 
some timeto internalize this structure.  
-/

-- Here's the type of the constructor including implicit arguments
#check (@pair)

-- Here we build two ordered pair values
def a_pair_string_nat : Prod String Nat := pair "Love" 4
def a_pair_nat_bool : Prod Nat Bool := pair 5 false

-- These objects are of the "parameterized" types you expect
#check a_pair_string_nat    -- type of ("Love",5) is (Prod String Nat)
#check a_pair_nat_bool      -- type of (5, false) is (Prod Nat Bool)

/-!
### Eliminators

Now suppose we have an ordered pair, *p = (a, b)*, and that we 
want to *get* the first, or respectovely the second, value, "out 
of the box." We'll need two eliminators: one that when given a pair,
*(a, b)*, returns the *first* element, *a*; and one that returns 
the second element, *b*. We take just the same approach as before,
using pattern matching to give names to the element inside a given 
pair. We can then return the right one. 
-/

def first {α β : Type} : Prod α β → α 
| (pair a _) => a

def second {α β : Type} : Prod α β → β 
| (pair _ b) => b

/-!
Study, compare, and contrast the function types here
as well as the implementations. These rules say, first,
if we have both an *a* and a *b*, then we can get an 
*a*; and, second, if we have both an *a* and a *b*, we 
can get a *b*. They're really simple, but they're also 
now stated in a mathematically precise and general way.
This is mathematics as much as it is programming. It's
abstract mathematics that also actually computes. Here
are a few examples of computing with these definitions. 
-/

#eval first a_pair_string_nat     -- "Love"
#eval second a_pair_string_nat    -- 4
#eval first a_pair_nat_bool       -- 5
#eval second a_pair_nat_bool      -- false

/-!
Challenge: What is the type of Prod? Think hard
about it before answering? Hint: It's not Type.
-/

#check (@Prod)

/-!
That right. Prod is essentially a function that
takes two type arguments and returns a Type. We
call it a polymorphic type, or better yet, a type
builder. 
-/

end cs2120

/-!
### Lean's Built-In Prod Type

Lean provide the type builder, Prod. It's just like
what we've defined except that it works not just with
types in Type, but with types in any "Type universe,"
from Type 0 to Type 1 all the way on up. Don't worry
about type universe levels at this point. 

The details of the definition are a little different,
but in ways that aren't important here. The things to
know are: (1) given *(a : α)* and *(b : β)* the term,
*(a, b)* represents that ordered pair, and is of type
*Prod α β*; (2) the two destructors are called *fst* 
and *snd*; and (3) there is a notation for the type,
*Prod α β*, namely *α × β*. 
-/

def pair1 := ("Hello",5)
def pair2 := (17, false)

#check pair1      -- Type is String × Nat
#check pair2      -- Type is Nat × Bool

-- Be sure you understand these function types
#check (@Prod.fst)
#check (@Prod.snd)

#eval Prod.fst pair1    -- expect "Hello"
#eval Prod.snd pair1    -- expect 5
#eval Prod.fst pair2    -- expect 17
#eval Prod.snd pair2    -- expect false

/-!
An object of an ordered pair of type α × β contains
both an object, *a : α*, AND and object *(b : β)*. Do
you see a way to define a new polymorphic type that
contains either a value *(a : α)* OR a *(b : β)?*. The
word OR here means exclusive or.
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
Lean's suport for Sum types.

Coming Soon.
-/

/-!
Understanding what it takes, and how, to deal with objects of
sum types is another big achievement in this class. It will make
you a better programmer, and it's deeply related to logic, and
in particular to reasoning from proofs of OR propositions. 

Take programming. First, classes in Java and Python are basically
product types: an object of a given type has values for *all* of 
the fields defined by it class. These languages simply don't have 
sum types. You can fake them, but it's complicated. On the other
hand, industrial imperative languages such as Rust and Swift, as 
well as functional languages such as Haskell and OCaml, do support 
sum types directly. You now have the basic pattern for programming
with sum-type values: you have to have a way to handle each case.

Finally, take logic. Suppose you have evidence that it is raining 
OR the sprinkler is running. Suppose you also know that IF it is
raining, then the ground is wet, and you know that if the sprinkler 
is running, the ground is wet. What can you conclude. In this little
story, what propositions correspond to α, β, and γ, and to the two
conversion functions? 
-/

end cs2120