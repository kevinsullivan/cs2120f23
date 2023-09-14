/-!
# The Unit and Empty Types

In this lecture we explore the simplest of all
data types. Whereas the *Bool* type has two values,
the *Unit* type has only one--defined by the single 
constant constructor, *unit*. The Empty type has no 
values, and no constructors, at all. It is said to
be an *uninhabited* type. The *Unit* type is likely
familiar to you as the *void* return type in Java.
The *Empty* type doesn't play very much of a role 
in programming, but it plays a vital role in the
logic you'll learn about going forward. So let's
dig in.

## Unit Type

The type, Bool, defines a set of two possible 
values, namely *true* and *false*. The Bool type
definition represents them as the two constant
(argument-free) constructors, *true* and *false*. 
A variable of this type carries one of these two
values, and thus carries one *bit* of information,
capable of distinguishing between two possibiities.

So what about a type with just one value? We can 
certainly define such a type. We'll call it the 
*Unit* type. We'll present an only slightly simplified 
version of Lean's *Unit* type here. This will be all 
you'll need to use the built-in type.

The type definition is just what you'd expect. *Unit*
is a type with one constant (parameterless) constructor,
*unit*. Thus *unit* is the only value of the Unit type.
-/

namespace cs2120

inductive Unit : Type
| unit

open Unit 

/-!
The Lean libraries define *()* as a notation for *unit*.
We can do the same with our own types, by the way. Here's
how you can define a notational shorthand for Unit.unit.
-/

notation "()" => Unit.unit

#check ()


/-!
So how much information does a value of this type carry?
Imagine a function that takes some parameter and returns 
a value of this type. How much can you learn about the
argument by looking at a return value of type *Unit?*
The answer is that it doesn't tell you anything at all.
A value of this type carries *no* information: zero bits. 
Such a value is *devoid* of information. 

As an example, here's a function that takes any *Nat*
as an argument and that always returns *(unit : Unit)*.
You always get the same answer no matter what value of
type *Nat* you give as an argument. The return value 
tells you *nothing* (other than that the function ran). 
-/

def useless : Nat → Unit := fun _ => ()
#reduce useless 0   -- returns (), void

/-!
You can of course also pass a value of the Unit type 
to a function, but it gives the function no useful 
additional information to work with, so you might as 
well leave it out. 
-/

def silly : Unit → Nat
| () => 5

/-!
This silly function can't use the value of its argument
to decide even between two possible return values, so it
only has one possible course of action, here it returns
5. In pratice you'd never write code like this because 
it's unnecessarily complex. Without harm you can remove 
the argument from the definition and just return the 5.
-/
def silly' := 5

/-!
Now you might think that Unit is a type you've never 
seen before, but it practice it's omnipresent in code
written in such languages as C, C++, Java, etc. It's 
the type of value returned by a function that "doesn't
return anything useful." You know it as *void*.

``` java 
public class HelloWorld {
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

-- Here's Lean's version of the *unit* value of the
*Unit* type. 
-/

#check Unit.unit


/-!
## Empty Type

Just as there's a type, *Unit*, with just one value, 
we can also define a type, we'll call it *Empty*, with =
no values at all. It sounds useless. We won't find it 
useful for programming but it plays an essential role
in logic. For now we'll see what we can learn by seeing
what kinds of functions we can define involving values 
of this type (a type with no values at all). 
-/

namespace cs2120

inductive Empty

/-!
That it: no constructors, no values. The Empty type. 

So what kinds of functions can we write with arguments
or return values of the Empty type? Let's look at three
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
Empty. So not only is there no value of type *Empty*
but there is no function of type *Nat → Empty*. It,
too, is an uninhabited type!

If you try to call it using #reduce, it'll tell you 
that the function is defined using "sorry", which is 
to say that the definition is incomplete. (Yes, the
error message is confusing. Sorry about that.)
-/

#reduce nat2empty 5 -- sorry (doesn't properly reduce)

/-!
Next let's write a function that takes an argument of
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
in this class. 

### Types

A central idea of course is the notion of a *type*. A type
can be understood as defining and giving a name to a set 
of terms. The set of terms of a type are defined entirely 
by its constructors. A constructor applied to zero or more
arguments (of the right types) is the a value of the given
type. We can say that it belongs to, or has, that type. 

We use terms, in turn, to *represent* meaningful things,
often things in the real world, such as the days of the 
week, possible moves in a game, or possible game outcomes.
The art of programming is largely in making great choices
about how to represent meaningful things in the world as 
terms with specific types in the computing machine.

For example, the terms, *true* and *false* of type *Bool*
in Lean represent the two values in Boolean algebra, also
generally called true and false. A term, *5* of type *Nat*
in Lean represents the abstract natural number, five. A
term, "Hello," of type String, represents the word, Hello.

### Bigger Types from Smaller Types

A second key idea in our work so far is that we can make
bigger types out of smaller types. In particular, if we
have any two types, *α* and *β*, we can form several new
types, and then we can (usually) for values of these new
types. We've seen three major examples. Given the types, 
*α* and *β*, here are three news types we can form.

- (α → β) : the type of a function with α input and β output  
- (α × β) : the produt type, of ordered pairs of α and β values  
- (α ⊕ β) : the sum type, of either an α value or a β value

### Introduction and Elimination Operations

We use the phrase, introduction operation, or sometimes
introduction rule, for constructors that *create* values
of a given type. Conversely, we use the phrase, elimination
operation, or elimination rule, for operations that *use* 
values of a given type. 

As an example, the constructor, *Prod.mk (a : α) (b : β)* 
is an introduction operation. If you apply *Prod.mk* to a
pair of values, as in *(Prod.mk 1 true)* it introduces this 
term as a value of type *Prod Nat Bool*. Please do recall
that the expression *(1, true)* is just standard notation 
for this aconstructor application. 

Conversely, if you want to *use* a term, (Prod.mk 1 true)
will likely want to get at the values, *1* and *true* that
it encapsulates. This is done by pattern matching. As an
example, the following expression matches the *pattern*,
*(Prod.mk f s)* with the term, *(Prod.mk 1 true)*, with
the result that the identifier, *f* is temporarily bound
to the *1* inside the term, and *s* is bound to *true*; 
and it then returns *f*, thereby providing access to the 
first element of the term. (Lean gives a warning that *s*
is not used, which tells you you can replace it with _).
-/

#eval match (Prod.mk 1 true) with -- expect 1
          | (Prod.mk f s) => f    -- pattern matches term

#eval match (Prod.mk 1 true) with -- expect true
          | (Prod.mk _ s) => s    -- no need to name 1

/-!
The types, *α → β, α × β,* and *α ⊕ β* are all formed
from two types, *α* and *β*, but they have very different
meanings: 

- a type of function that *if* it's given a value of type *α* then it returns a value of type *β* 
- a type of ordered pairs each of which contains a value of type *α and* a value of type *β*
- a type of sums, each of which contains *either* a value of type *α* or a value of type *β* 

What fundamentally distinguishes these types are their introduction (construction)
and elimination (usage) operations. For example, a product type has *one* constructor
(introduction operation) that takes an *α* value *and* and *β* value, while a sum type
has two constructors, one of which takes an *α* value and the other a *β* value. In turn
the product type has two elimination operations, one returning the first and the other
the second component of a pair, while there's just one sum elimination rule, that takes
a sum along with functions enabling either case to be reduced to a value of a single 
output type. 

What remains is to explain the introduction and elimination operations for
function types. Recall that a *value* of a function type is essentially a 
function *implementation* that for converting a given argument value (of a
type *α*) into a value of an output type, *β*. That's the introduction rule:
give such a procedure.
-/

def negate : Bool → Bool :=   -- function type
λ b => match b with           -- function value
| false => true
| true => false

/-!
So what's the elimination procedure for a value of a function type? In
other words how do you *use* a function? You *apply* it to an argument!
-/

#eval (negate true)

/-!
### What You'll Need to Know By Heart

Understand the following types and their introduction 
and elimination operations. You should understand exactly
which introduction (constructor) and elimination operations
correspond to these types, and how to define the types and
these operations, and how to use them, without looking at
notes. 

- {α β : Type} → (a : α) → (b : β) → α × β 
- {α β : Type} → α × β → α
- {α β : Type} → α × β → β 
- {α β : Type} → α → α ⊕ β
- {α β : Type} → β → α ⊕ β
- {α β γ : Type} → α ⊕ β → (α → γ) → (β → γ) → γ
- {α β : Type} → (α → β) → α → β 
- {α β : Type} → [procedure yielding some β given any α] → (α → β) 
- (unit : Unit)
- There's no useful elimination operation for Unit
- There is no introduction operation for *Empty*
- { α : Type } → Empty → α 
-/