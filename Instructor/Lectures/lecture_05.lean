/-!
# Function Composition

We can now highlight first great generalization 
of this course: a function, we call it *compose*,
that combines any two *compatible* functions, *g*
and *f*, into a new function, denoted (g ∘ f), and
pronounced *g after f*, where for any *compatible* 
argument, *a*, *(g ∘ f) a* is defined as *g (f a)*. 
By *compatible* we mean that (1) *a* is the input
type of *f*, and (2) the *output* type of *f* is
the *input* type of *g*. When this is the case, 
we can provide *a* as an input to *f* and *(f a)* 
as an input to *g* to compute *g (f a)* as a final
result. In this chapter we build up from where we 
left off in the last chapter to a precise and general 
mathematical definition of function composition.   
-/ 

/-!
## Given f : α → α, apply2 returns (f ∘ f)
We start by further analyzing our polymorphic apply2 
function from the last chapter. Here it is again. 
-/

def apply2 {α : Type} : (α → α) → α → α
| f, a => f (f a)

/-!
Given any type, α (implicitly), *apply2* takes a 
function, *f : α → α*, and a value *a : α*, as its
arguments and returns the value of *f (f a)*. 

But given our definition of function composition, 
we can see that this result can also be written as
*(f ∘ f) a*: as we just defined (f ∘ f) a* to be 
nothing other than *(f (f a))*. Revisit the first
paragraph of this chapter to be sure that's clear.
-/

/-!
As an aside, here, again, are a few simple functions
from the last chapter, again, for use in examples to
follow.
-/

def double (n : Nat) := 2 * n 
def square (n : Nat) := n ^ 2
def exclaim (s : String) := s ++ "!"
def is_even (n : Nat) := n % 2 == 0

/-!
Now consider a simple application of apply2. 
Before reading any further, be sure that you
fully understand what it computes and how.
-/

#eval apply2 double 5   -- (double (double 5) 
                        -- (double ∘ double) 5
                        -- expect 20
/-!
Now consider how this expression is evaluated.
Remember: function application is left associative.
The expression, *apply2 double 5*, is thus evaluated 
as *(apply2 double) 5*. The expression *(apply2 double)* 
returns a *function* that then takes a next argument, 
such as 5, which it then doubles twice. Be sure you
see that *(apply2 double)* is a function. 
-/

#eval apply2 double 5     -- expect 20
#eval (apply2 double) 5   -- exactly the same 

/-!
Now a key question: what function is *(apply2 double)*?
Well, it's the function that, when applied to an argument,
*a,* applies double to it and then applies double to that
result. It's thus exactly the function, *(double ∘ double)*. 
Let's bind the name *double_after_double* to this function.
-/

def double_after_double := (apply2 double)

-- Sure enough it's a function from Nat to Nat
#check (double_after_double)

-- And it *behaves* just as expected
#eval double_after_double 0 -- expect 0  (double (double 0))
#eval double_after_double 1 -- expect 4  (double (double 1))
#eval double_after_double 5 -- expect 20 (double (double 5))

/-!
Leaving the final argument to be provided later,
we see that (apply2 double) is (double ∘ double).
More generally, given any type, α, apply2 applied 
to any function, *f : α → α*, returns the function,
*f ∘ f:* *f* composed with itself. 
-/

def square_after_square := apply2 square  -- square ∘ square
#eval square_after_square 5               -- expect 625

def exclaim_after_exclaim := apply2 exclaim -- exclaim ∘ exclaim
#eval exclaim_after_exclaim "Love math"     -- "Love math!!"

/-!
## Generalizing to Functions of Different Types

Of course, apply2 is a pretty limited mechanism for
composing functions: it can only compose a function,
f : α → α, with itself, to return *(f ∘ f)*. As you 
saw on the homework, we can also glue functions with
different types together, as long as the output type
of one is the same as the input type of the second. 

On the homework, we worked up to defining *glue_funs*
as a polymorphic function that, given any three types,
α, β, and γ, takes two functions, *g : β → γ* and *f :
α → β* along with any argument *a : α* and that returns 
*(g (f a))*, which we now understand to be *(g ∘ f) a*.
-/

def glue_funs {α β γ : Type} :
  (β → γ) →   -- type of g
  (α → β) →   -- type of f
   α →        -- type of a
   γ          -- result type
| g, f, a => g (f a)

/-!
Let's see an easy example. In this example,
- α is String
- β is Nat
- γ is Bool
-/

-- We need a function f : String → Nat
def len : String → Nat := String.length
#check (len)           -- String → Nat

-- We need a function of type Nat → Bool 
def ev (n : Nat) : Bool := n%2=0
#check (ev)             -- Nat → Bool

-- glue_funs composes ev and len into a String → Bool function! 
#eval glue_funs ev len "Hello"    -- expect false
-- Remember application is left associative
#eval (glue_funs ev len) "Hello" -- expect false
-- (glue_funs ev len) is the function we want!
#check (glue_funs ev len)     -- String → Bool
-- Applied to a String it gives back a Bool!
#eval (glue_funs ev len) "Hello!" -- expect true
 
-- We can even name this function then use it.
def ev_string := (glue_funs ev len)
#eval ev_string "Hi!"   -- expect false
#eval ev_string "Hello" -- expect false
#eval ev_string ""      -- expect true
#eval ev_string "I Love Logic"  -- true

/-!
Wow. So glue_funs is in essence a function
for *gluing together* two functions into a 
new function, where the input of one is the
output of the other, given a value to which
the whole thing is applied.  
-/


/-!
Recall that just as with *apply2*, leaving off the third
argument, *a*, to *glue_funs*, we will return exactly the
function, *(g ∘ f)*. That is, we'll get the function that, 
when applied to an argument, *(a : α),* return *(g (f a)).* 
What function does that? It's just *(g ∘ f)*. Pronounce 
this function as *g after f*. The idea is that it applies
*g* after (to the result of) applying *f* to *a*.  
-/
#eval glue_funs square double 4   -- expect 64

-- Apply glue_funs to first two arguments
def square_after_double := glue_funs square double

-- Apply the resulting function to 4
#eval square_after_double 4       -- (square ∘ double) 4
                                  -- square (double 4)
                                  -- square 8
                                  -- 64

/-!
The square_after_double function *is* (square ∘ double).
Indeed, you even pronounce (square ∘ double) as *square
after double*. That makes sense because when you apply
(square ∘ double) to an argument *a* you apply *square*
after you apply *double* to *a*.
-/


/-!
Self-test: What is the type of the function returned 
by *glue_funs* when applied to two function arguments,
g : β → γ and f : α → β?
-/

/-!
Insight: glue_funs is a general function composition
operation! A better name for it is compose! We'll start
by calling it compose' and then make some improvements.

In this firt definition we've added explicit parentheses 
around *(α → γ)*. As → is right associative, doing this
leaves the meaning unchanged from above. This is just an
exact repeat of *glue_funs*. But with parentheses, the type 
of compose' reads better: it takes two functions, of types 
(β → γ) and (α → β), and returns a function of type (α → γ). 
That's it!
-/

def compose' {α β γ : Type} :
  (β → γ) →
  (α → β) → 
  (α → γ) 
| g, f, a => g (f a)


/-! 
Self-test: Using *compose'*, define a function,
is_even_len : String → Bool, that takes a string
and returns true if it's of even length and false 
otherwise.
-/

-- Answer here.

def is_even_len := _  -- Be sure you can solve it

#eval is_even_len "Love"    -- Expect true
#eval is_even_len "Love!"   -- Expect false
#eval is_even_len "Love!!"  -- Expect true

/-!
## Function (Also Known As Lambda) Expressions

Our code for *compose'* is a little more complex than
it needs to be. If all we're going to do is use it to
return functions, then (1) we don't expect to have to
give a third argument, *a*; and (2) we expect the type
of the return value to be a function type. Here's our
final definition of compose. It introduces a new idea:
that of anonymous function expressions. 
-/

def compose {α β γ : Type} :
  (β → γ) → 
  (α → β) → 
  (α → γ)       
| g, f => (fun a => g (f a)) 


/-!
Note that we've again written the type of compose
to emphasize that it takes two functions and returns
a function. We then match on the first two function
arguments, calling them *g* and *f*. Finally, what
we return is the value of a new kind of expression: 
(fun a => g (f a)). It specifies an unnamed function,
taking an argument, *a*, and returning the value of 
*g (f a)*. 

Such a function expression, often called a *lambda 
expression*, is defined in Lean by the keyword, *fun*
(you can also use a Greek lower case lambda, λ), then
arguments, then =>, then the expression that defines
the return value.  It's essential to understand that
such an expression defines a function: one that is
*waiting* for an argument *a* and that computes a
final result only then.

You can use a function expression anywhere you need
a function value. Here are some examples. 
-/

-- Here we give new names to old function friends
def fun_double := fun (n : Nat) => 2 * n
def fun_square := fun (n : Nat) => n ^ 2 

-- Here we pass an unnamed function to composee
#eval compose (fun (n : Nat) => n%2 == 0) String.length "Love!"


/-!
In Lean4, the *compose* function is *Function.compose*
and the infix notation, ∘, is a convenient way to apply
it.
-/

-- Composing functions with Lean infix notation for compose
def double_after_square := (double ∘ square)
def is_even_len'' := (is_even ∘ String.length)

#eval double_after_square 5       -- expect 50
#eval String.length "Hello Higher Mathematics!" -- 25
#eval is_even_len'' "Hello Higher Mathematics!" -- false


/-!
## Welcome to Higher Mathematics

We now have the first really big idea in this course. 
In elementary mathematics you've always had numbers
and ways to combine numbers into new numbers: using 
operators such as + and *. That is, you've always had 
an *algebra* with numbers as basic objects and + and * 
as *operators* that you can use to combine them. Now 
you have a *higher* algebra with functions as basic 
objects and composition (∘) an an operator, akin to 
addition or multiplication, to combine *functions* 
into new functions. 

Being able to understand, define, and apply the general
concept of function composition is a milestone in learning. 
You will use the concepts embedded in this chapter for the
rest of the semester. You should take some time to savor 
the beautifully concise and powerful concept developed here. 
Here it is again, expressed even more cleanly.

def compose {α β γ : Type} (g : β → γ) (f : α → β) := λ a => g (f a)

This definition gives names to all of the arguments
(before the colon); leaves the return type implicit, which 
Lean infers; and uses λ instead of fun (for the "fun" of it)
to write the function that this compose function is to return.
-/

/-!
## Extra, extra!
Did you know that Java and Python support lambda expressions?
In this section, we'll show you, and present implementations of
our apply2 and compose functions in Python. You will now see how 
to program with higher-order functions in Python. You will also
know what we mean when we say that you can expect to be able to 
do so in many other capable languages, as well. You can run the
following code in the VSCode container for this class.

```Python
# Here's an ordinary definition of a squaring function
def square(x) : return(x**2)
print(square(5))                # expect 25

# Here's square defined with a Python lambda expression
square = lambda x : x**2
print(square(5))                # Expect: 25

# Here we apply an unnamed lambda to 6; expect 36 
print((lambda x : x**2)(6))

# Here's apply2 in Python, where f is a function argument
def apply2(f) :
    return lambda x : f(f(x))

# Here we use apply2 to apply a cubing function twice to 2
print(apply2(lambda x: x**3)(2))  # Expect (2^3)^3 = 512

# Here is a general compose in Python; g and f are functions 
def compose(g,f) :
    return (lambda a : g(f(a)))

# Here's an example of its use; understand this code
cube_after_square = compose((lambda x : x**3),(lambda x : x**2))
print(square_after_cube(3))         # Expect (3^2)^3 = 729
```
The programming and reasoning principles you learn in 
Discrete Math and Theory will prove exceptionally valuable 
to you no matter what languages you are ultimately asked 
to use for everyday programming. 
-/