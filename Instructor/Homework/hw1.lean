/-!
# Homework #2

## Procedure

Here's how to do this homework.

### Collaboration

The collaboration rule for this homework is that
you may *not* collaborate. You can ask friends and
colleagues to help you understand material in the
class notes, but you may not discuss any aspect
of this homework itself with anyone other than one
of the instructors or TAs. 

### Purpose
It is vitally important for your ability to do
well for the rest of the semester that you now 
master all of the material we've covered so far in
class. The purpose of this homework assignment is
to guide you to such mastery. 

### Questions?

We will provide a means for you to ask questions
in case you get terribly stuck. Before you ask, be
sure you've read, worked in VSCode through, and 
done your best to understand all of the materials 
covered so far in class. You may, and we encourage
you to, work with your in-class friends to this end.
We'll announce a question-asking forum shortly. 

### What To Do

Do a *git pull upstream main* to pull this homework
file into your Instructor/Homework directory. Copy
it to your Students directory. Complete the work by
editing that file. Save it to your Local downloads
folder. Upload the completed homework file to Canvas.

### Due Date
This assignment is due before class, by 3PM, next 
Tuesday, September, 5. 
-/

/-! 
## Problem 1: A type question 

The String.length function takes any string
as an argument and returns the natural number that
is length of the given string. What is the type of
the String.length function?

Answer here:
-/


/-!
## 2: Define a Boolean operation
The *implies* function from Boolean algebra takes 
two Boolean values as its arguments and returns a 
Boolean value as a result. It's one of the standard
Boolean operations, along with *and*, *or*, etc. It
behaves as follows: If the first argument is true 
and the second is false, then it returns false and
otherwise it returns *true*. 

Define the implies function here, calling it imp.
Hint: Review the notes to see how we define several
similar Boolean operators, such as *xor* and *nor*. 
-/

-- Write your code here

/-!
## Problem 3: Prove correctness by exhaustive testing
Prove that your implementation of imp is corret
by writing test cases, using #eval, for all possible
combinations of input arguments. Document the corret
(expected) answer for each case in a comment at the
end of each #eval line, as we've done in class.
-/

-- Write your answers here:
#eval _   -- etc

/-!
## 4. Glue together two compatible functions
Write a function, *glue_funs'*, that takes 
three arguments and returns a Boolean result. 
The first argument is any function, *g*, that 
takes a Nat and returns a Bool. The second argument,
is any function, *f*, that takes a String and returns 
a Nat. The third argument is a String, *s*. The 
*glue_funs'* function computes its result value by 
applying *g* to the result of applying *f* to *s*.

As an example, suppose *f* is the *String.length*
function. It takes a String and returns the Nat
that is its length. Now suppose that *g* is the 
*isEven* function, as we define below, that takes a
natural number and returns *true* if it's even and
*false* otherwise. Finally, suppose that *s* is the 
string, "Hello." Then we expect the application, 
*(glue_funs' g f s)* to return false, because (1) 
applying f to s returns 5, then (2) applying g to 
5 returns false (because it's not even), and that
is the final Bool result that glue_funs' is meant
to return.  

Define (implement) your glue_funs' function below,
then test it using String.length as *f*, the *isEven* 
function (we define it for you) as *g*, and at least
the two String values, "Hello" and "Hello!" as test
inputs for *s*.

Hint: Be sure you really understand how we defined
the apply2 functions in class. See the class notes.
That function is a special case where we apply a
function *f* to the result of applying that same
function, *f*, to an argument. The function you're
asked to implement here "glues" together different
functions, *g* and *f*. First we sure that you've
written the *type* of glue_funs' correctly, then 
the implementation code should be straightforward.
Note that the *g* argument comes first, then the *f*
argument, and finally *s*. 
-/

-- Here's an implementation of isEven 
def isEven : Nat → Bool
| n => if (n%2 = 0) then true else false

#check (isEven)           -- Nat → Bool
#eval isEven 2            -- expect true
#eval isEven 3            -- expect false

/-!
Define your function here. When you've got it
right, the following test cases should pass.
-/

-- Now complete the implementation of glue_funs'
def glue_funs' : _
| _ => _

#eval glue_funs' isEven String.length "Hello"  -- false
#eval glue_funs' isEven String.length "Hello!" -- true

/-!
## 5. Generalize to arbitrary compatible function types
Note that glue_funs' works only for functions
of types (Nat → Bool) and (String → Nat). It works
because the output type of any (String → Nat) function
is the input type of any (Nat → Bool) function. So in
a sense we can always *glue together* any two such
functions. 

It should be evident at this point that this concept
generalizes. Suppose we have *any* three types, α, β, 
and γ; that we have *any* two functions, *g : β → γ*, 
and *f : α → β*; and that we have *any* value, *a : α*. 
Then we can always compute and return *g (f a)*. We
can say that our new function returns the value gotten
by applying *g after f* (to *a*).

Your task now is to show that you have mastered and
that you can apply the concepts we've covered to far 
in class (and in the class notes) by now implementing 
a *polymorphic* version of glue_funs', with implicit
type arguments. Call your new function *glue_funs*.
When you succeed, the test cases below should pass.

Lean hint: you can declare multiple arguments of the
same type within a single set of parentheses. For
example, if you want to declare x, y, and z to be of 
type Nat, you could write (x y z : Nat). It's not 
necessary to do this but it yields cleaner "code."

Another hint: You might find it useful to write 
your *glue_funs* definition first without implicit 
type arguments then make them implicit. That's up 
to you. If you do that, you'll have to give the type 
argument values explicitly in the test cases below.
They are currently written assuming that the values
of the type arguments are implicit and inferred.
-/

-- Implement glue_funs here
def glue_funs : _
| _ => _

-- test cases
#eval glue_funs isEven String.length "Hello"  -- false
#eval glue_funs isEven String.length "Hello!" -- true

/-!
## 6. Show that apply2 is a special case

Write a test case for glue_funs using the double and 
square functions from the class notes as function 
arguments. (You can copy those function definitions
into this file.) What do you expect the result 
to be for (glue_funs double square 5)? Do you expect 
to get the same answer for (glue_funs square double 5)?
In other words is applying double after square the same
as applying square after double? 
-/

-- Copy the double and square functions here

-- Write your tests here; include expected results

#eval _
#eval _
