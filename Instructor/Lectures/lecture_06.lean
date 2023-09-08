/-!
# Data Types: Enumerated and Product Types

In this class so far, we've used a few data types that
Lean provides for us, namely Bool, Nat, and String. We
will often want to reason about or compute with values
of other types. How do we define new data types in Lean?
This chapter will teach you how to define new types and
how to define functions that take arguments and return
results of your own data types.

## Chapter Overview

This chapter will cover three broad classes of data 
types. They are called *enumerated* types, *product*
types and *sum* types. 

### Enumerated Types
An enumerated type has a (typically small) number of 
*constant* values. By constant we mean that the values 
of a type are produced by what we call *constructors* 
that *don't take any arguments*. 

The *Bool* type is an example. Its constructors are 
called *true* and *false*. They take no arguments, and
so are, in fact, the two (and the only) values of the
*Bool* type.

### Product Types
Whereas the Bool type has two constant constructors, a 
product type has just one constructor, but one that
takes two arguments. You can think of the values of a 
product type as representing an *ordered pair* of 
values, such as *(0, true)*, for example. 

Here you'll learn how to define a *polymorphic*
product type that lets you specify (or that Lean infers
as) arbitrary types, α and β, for the *first* and *second* 
value in any such pair. 

Crucially you will also learn how you can define your
functions that *use* such ordered pair values. To use
a pair value, you will generally need to *get* at the
individual (first and second) values *inside* a pair.
Given a pair, *p = (f,s)*, we'll define two elimination
functions, *fst* and *snd*, where *fst p* returns *f*
and *snd p* returns *s*.
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

#reduce play scissors rock

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
- *inductive* is a keyword, as explained above
- Box is the name of our now polymorphic data type
- α is a type argument: the type of object that can fit a given Box
- Given (a : α), (Box a) is a type: a type of Box that can fit α's
- put is the sole constructor, taking an argument (a : α)
- a value of type *Box α* is simply an application term, *(put a)* 
Let's see how to use this definition to put some things in boxes
-/

/-!
### Constructor

Let's look at how to construct terms of type Box α, 
where α is a type, such as Nat or String.
-/

open Box  -- so we can write put instead of Box.put

-- If α is a type, then Box α is a type
#check Box Nat

-- A put application term is a value of this type
#check (put 1)    -- this term is a value of type Box Nat
#reduce (put 1)   -- constructors don't compute/do anything

-- We can assign values of our type to to variables
def box_containing_zero : Box Nat := put 0

-- Box is a type builder, taking arguments of different types
def box_containing_hello : Box String := put "Hello"

-- Lean can usually infer the type of a constructor term
def box_containing_hello' := put "Hello"

-- What is the type of Box? It takes a type and yields a type
#check (Box)    -- Type → Type (study and understand this)

-- A constructor of a polyorphic type is itself polymorphic
#check (@Box.put)   -- {α : Type} → α → Box α. Understand it!


/-!
It's important to understand that (put 1) is a term of 
type Box Nat, (put true) is a term of type Box Bool, and
(put "Hello!") is a term of type Box String. Constructors
are like functions in that you can form application terms,
but these terms don't compute anything. Rather, constructor
application terms *are* the values of any given type. 

It's also important to understand that the constructors of
a polymorphic type are themselves polymorphic. They implicitly
take type arguments. The *put* constructor for example takes
both an *implicit* type argument, α, and an *explicit* value
of that type. In this sense, they behave like the polymorphic
functions we've already seen. Go back and review the work we
did on a polymorphic identity function to remind yourself of
the details. Then double check your understanding of the type
of the put constructor. Note that it takes a type argument,
but implicitly, and inferred from the following arguments.
-/

#check (@put)     -- @put : {α : Type} → α → Box α

/-!
### Eliminator

Having *put* some value in a Box, we will often want to
get it back out. To do this, we need to *eliminate* the box
to get at what's inside. The way we eliminate an object to
get at what's inside it is by pattern matching! We define
a (polymorphic) function, let's call it *get*, that takes
an object of type *(Box α)* for some type, α. 

There is only one possible form for such a value. It must
be a term, *(put a)*, where *a* is the argument provided
when the term/value was constructed. So what we're going to do
is to use pattern matching to (a) determine which constructor 
was used to construct the box (in this example there's only
one) (2) give a name to the value that was provided to the 
constructor when the term was constructed. Then we return 
that now named value from "inside" the box. 
-/

def get {α : Type} : Box α → α 
| put o => o

/-!
Let's analyze that. The function name is get. It's
polymorphic with implicit type argument α. It takes
a value of type *Box α* and from that argument it
derives and returns a value of type α. The way it
does this is by pattern matching on the argument
of type *Box α*. There's only one way that such an
argument can exist: it *must* have been constructed
by the *put* constructor applied to *some* object, 
*a*, of type α. That is, the value must look like
*put a*. By pattern matching we give the value, *a* 
the name, *o*. That's the key! Now we have a name
for the object, *a*, inside the box, all that's left
is to return it. Study this example deeply and be 
sure you fully understand what's going on. 

Here are examples to show it in operation. Remind 
yourself of the definitions of boxed_nat, etc., from 
above, as needed to see that the results are as expected.  
-/

#eval get (put 1)         -- o matches with 11
#eval get (put true)      -- o matches with true
#eval get (put "Hello!")  -- o matches with "Hello!"

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
#eval first (pair 2 "Hi")         -- 2
#eval second (pair 2 "Hi")        -- "Hi"

/-!
Challenge: What is the type of Prod? Think hard
about it before answering? Hint: It's not Type.
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

-- The name of the single Prod constructor is mk
def pair0 := Prod.mk true 10
#check pair0  -- Bool × Nat

-- Use standard notation instead of Prod.mk
def pair1 := ("Hello",5)
def pair2 := (17, false)

#check pair1      -- Type is String × Nat
#check pair2      -- Type is Nat × Bool

-- Be sure you understand these function types
-- The u_1 and u_2 generalize to Type, Type 1, ...
#check (@Prod.fst)
#check (@Prod.snd)

-- How to eliminate to get the first or second element
#eval Prod.fst pair1    -- expect "Hello"
#eval Prod.snd pair1    -- expect 5
#eval Prod.fst pair2    -- expect 17
#eval Prod.snd pair2    -- expect false

-- We call these "projection" functions

-- Lean provides notations for "projection"
#eval pair1.1           -- expect "Hello"
#eval pair1.2           -- expect 5
#eval pair2.1           -- expect 17
#eval pair2.2           -- expect false

/-!
An object of an ordered pair of type α × β contains
both an object, *a : α*, AND and object *(b : β)*. Do
you see a way to define a new polymorphic type that
contains either a value *(a : α)* OR a *(b : β)?*. The
word OR here means exclusive or.
-/

