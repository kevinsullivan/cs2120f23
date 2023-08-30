/-!
Note: These notes are not yet complete. They
current extend the material presented at the
end of lecture 3, August 29, 2023. This section
will be extended as we go forward.

# Polymorphic functions

Consider the following three functions. 
Each one simply returns the single value 
given as its single argument. We call these 
function *identity functions*, for arguments
of types Nat, String, and Bool respectively.
`-/

def id_nat : Nat → Nat
| n => n

def id_string : String → String
| n => n

def id_bool : Bool → Bool
| n => n

/-!
## Functions varying in argument types

Beyond having different names, these
functions *vary* only in the types of
their argument and return values. 

We wouldn't want to have to write one
such function for each of hundreds of
types. We can avoid such repetition by
"factoring out" the varying part of the
definition into a parameter (argument). 
`-/

/-!
## Factor out variability into a type parameter

If we bind a name, such as *T* or *α* ,to
a first *type* argument, then we can define
the type of the rest of this function to be
T → T, or α → α. In Lean it's conventional 
to use greek letter names for type values, 
so we will do that from now on.

Let's see how to write a single *polymorphic*
identity function that covers in one definition
an infinitude of identity functions, varying in
the types of their argument and return values. 
Then we'll analyze the definition to understand 
it in detail.
`-/

def id_poly (α : Type) : α → α 
| v => v

/-!
Here are the elements of this definition:

- def is the keyword for giving a definition
- id_poly is the name of the function being defined
- (α : Type) binds the name α to the first argument to id_poly: a type value
- the : separates the named arguments from ones as yet not named
- the | is the one and only pattern matching rule for this function
- v matches the second argument *of type α* for whatever value α has
- => separates a pattern on the left from the return value on the righ
- v, bound to the second argument, is the return value of this function 

Now we can see that our single definition provides an identity
function for any type of value.
`-/

#eval id_poly String "Hello!"
#eval id_poly Nat 7
#eval id_poly Bool true

/-!
## Parametric Polymorphism

What we're seeing here is called parametric polymorphism! We have 
one function definition that can take arguments of many different 
types. Here the *type* of it's second argument is given by the type
*value* (such as Bool or Nat or String) of its first argument. 

Lean easily detects type errors in such expressions. For example,
if we pass Bool as the first argument but 7 as the second, Lean 
will report an error. Let's try. 
`-/

#check id_poly Bool 7   -- Lean says it can't convert 7 into a Bool

/-!
# Implicit Arguments

You might have noticed that in principle Lean can always infer
the *type value* of the first argument to the id_poly function
from the *data value* passed as the second argument. For example,
if the second argument is "Hello!", the first argument just *has
to be* String. If the second argument is 7, the first has to be 
Nat. If the second is true, the first has to be Bool.

In these cases, you can ask Lean to silently fill in argument
values when it knows what they must be, so that you don't have 
to write them explicitly. To tell Lean you want it to infer the
value of the first *type* argument to id_poly, you specify it as 
an argument when defining the function not using (α : Type) but 
using curly braces instead: {α : Type}. Let's define the function 
again (with the name id_poly') to see this idea in action.
`-/

def id_poly' {α : Type} : α → α   -- α is now an implicit argument 
| v => v

/-!
Now we can write applications of id_poly' without giving the
first (*type*) argument explicitly. It's there, but we don't
have to write it. Instead, Lean infers what it's value must
be from context: specifically from the type of the value we
pass as the second argument. The resulting code is beautifully
simple and evidently polymorphic. It also eliminates possible
type mismatches between the first and second arguments, as the
type in question is inferred automatically from the value to 
be returned. 
`-/

#eval id_poly' 7
#eval id_poly' "Hello!"
#eval id_poly' true


