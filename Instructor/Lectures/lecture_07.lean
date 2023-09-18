/-!
# Data Types: Sum Types

Whereas a product type contains *both* a value of
some type, α, *and* a value of some type β, a sum type
contains *either* a value of some type, α, *or* a value
of some type, β. A sum type thus has two constructors, 
each taking a single argument, one taking an α value,
the other taking a β value. 

We'll use as constructor names *inl* and *inr*, where 
*inl* takes an argument of type α and *inr* takes an 
` 12q3argument of type β. So, 
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
#check (@Box.put Nat 8)
#check (Box.put 8)

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

def a_sum1' := @Sum.inl Nat String 1
def b_sum1' : Sum Nat Bool := Sum.inr true

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

def s := Sum.inl 1 -- can infer α = Nat but can't infer β
def s1 : Sum Nat Bool := Sum.inl 1      -- specify α and β 
def s2 : Sum Nat Bool := Sum.inr true   -- same thing here
def s3 := @Sum.inl Nat Bool 1 -- give α and β to constructor 
#check s1
#check s2
#check s3

/-!
Here's an Example of a sum-eliminating function 
that takes a value of any sum type and returns 
the String "Left" if it was constructed using the
inl constructor, and that returns "Right" if it 
was constructed using the inr constructor. As 
those are the only possibilities, this function 
will work for any value of type *Sum α β* where 
*α* and *β* are arbitrary (any) types.   
-/
def which { α β : Type } : Sum α β → String
| (Sum.inl _) => "Left"
| (Sum.inr _) => "Right"

#eval which s1  -- expect "Left"
#eval which s2  -- expect "Right"
#eval which s3  -- expect "Left"


/-!
### Sum Types in Everyday Programming

Understanding what it takes, and how, to deal with objects of
sum types is another big achievement in this class. It will make
you a better programmer, and it's also deeply related to logic. 

Take programming. First, try to see that classes in Java and Python 
are basically product types: an object of a given type has values 
for *all* of the fields defined by it class. On the other hand,
these don't support sum types natively. C++ does but it's approach
is complex and not very well received among programmers. 

On the other hand, industrial languages such as Rust and Swift, as 
well as functional languages such as Haskell and OCaml, do support 
sum types directly. You now have the basic pattern for programming
with sum-type values: you have to have a way to handle each case.

## Simulating Sum Types in Python
To show you that these ideas are worth understanding, here's some 
code that uses a Python library to program with limited sum types,
including a definition of a general purpose sum elimination function
straight from the lesson of this chapter.

```python
from dataclasses import dataclass

@dataclass
class Alpha:
    a: float


@dataclass
class Beta:
    b: int

@dataclass
class Gamma:
    c: bool

Either = Alpha | Beta

def sum_elim (one_of : Either, a2c, b2c) : 
    match one_of :
        case Alpha(a): 
            return a2c(a)
        case Beta(b): 
            return b2c(b)

# DEMO

## functions to "handle either case"
# f : float -> bool: (f >= 5.0)
# i : int -> bool:(i < 5)
def fge5(f) : return (f >=5.0)
def ilt5(i) : return (i < 5)

# Create four objects of our Alpha | Beta sum type
six_oh_ge_five_oh = Alpha(6.0)
four_oh_ge_five_oh = Alpha(4.0)
four_lt_five = Beta(4)
five_lt_five = Beta(5)

print(sum_elim(six_oh_ge_five_oh,  fge5, ilt5))  # expect True
print(sum_elim(four_oh_ge_five_oh, fge5, ilt5))  # expect False
print(sum_elim(four_lt_five,       fge5, ilt5))  # expect True
print(sum_elim(five_lt_five,       fge5, ilt5))  # expect False
```
-/

