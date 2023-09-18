/-!
Note: This lecture started with an in depth review
of the answer key for Homework #3. That took upwards
of 40 minutes, then we only had enough time to cover
the Unit type.  

# Data Types: The Unit Type

In this lecture we explore the simplest of all
data types. Whereas the *Bool* type has two values,
the *Unit* type has only one--defined by the single 
constant constructor, *unit*. The Empty type has no 
values, and no constructors, at all. It is said to
be an *uninhabited* type. This chapter presents the
Unit type and its related constructors and patterns
of usage.  

To best understand the Unit type, start with the
familiar type, Bool. It has a set of two possible 
values, namely *true* and *false*. A variable of 
this type carries one of these two values, and thus 
carries one *bit* of information, just enough to 
distinguish between two possible worlds.

So what about a type with just one value? Indeed
we can define such a type, and it's usually called
the *Unit* type. We'll present a slightly simplified 
version of Lean's *Unit* type here. This will be all 
you'll need to use the built-in Unit type for now.

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
*monad* type that (a) runs a computation that, in
general, isn't purely functional (such as sending
output to the terminal), and (b) returns a result
of some type. In this example, that type is *Unit*. 

You can actually write this LEAN code in a file,
e.g., HelloWorld.lean, and compile and run it just
like a Java or C++ program. Try it in the terminal.

```sh
lean --run lecture_08_hello.lean
```
-/


/-!
So now you understand the Unit type in Lean. It's a
data type with just one value. It communicates no
information, and is useful mainly as a return value
of an operation that computes nothing of interest but 
is instead useful for its *side effects.*  

-- Here's Lean's version of the *unit* value of the
*Unit* type. 
-/

#check Unit.unit


/-!
## The Unit Type in Python

Python has a Unit type, called NoneType, with a single value, None.
This value is returned by functions that don't have explicit return
values, and can be used explicitly to reflect the absence of a value. 

```python
# This file introduces the NoneType type and its single value, None

# None is a (and is the only) value of class NoneType
print(type(None))               # expect NoneType

# Functions without explicit returns implicitly return None
def return_nothing (x : str) :
    print(x)                    # no return statement here
print(return_nothing("Hi!"))    # expect "Hi!" then None

# You can use None to represent an error value
# For example, here's a natural number predecessor function
# that returns None to signal error if its argument is <= 0
def nat_pred (n : int) :
    if (n <= 0) :
        return None
    else :
        return (n - 1)
print(nat_pred(2))              # expect 1
print(nat_pred(1))              # expect 0
print(nat_pred(0))              # expect None (undefined)
```
-/