/-! 
INCOMPLETE AND UNDER CONSTRUCTION

# Inductive Type Definitions

You've seen that we use the keyword, *inductive*, 
to introduce new data types, but what does this word 
really mean?

To get to an answer, let's have a look at a familiar,
traditional child's toy: the nesting doll.

Such a *doll* comes in two forms: either it's a *solid*
doll, or a *shell* with another *doll* inside it. 
-/

inductive doll : Type
| solid
| shell (d : doll)

open doll

def d0 := solid
def d1 := shell d0
def d2 := shell d1
def d3 := shell d2

/-!
Let's see what d3 really looks like. Let's keep
expanding the "inner" dolls until we reach the final
solid doll at the "bottom."

- d3
- shell d2
- shell (shell d1)
- shell (shell (shell d0))
- shell (shell (shell solid))

The final terms is the actual value of d3.
-/

/-!
Now suppose we're given an arbitrary object of type *doll*
and that we want to count how many layers deep it goes. We
have to analyze its form. If it's solid, the answer is zero.
If it's of the form (shell inner), where inner is the doll 
inside an outer shell, then the answer is one (for the shell) 
plus the depth of the inner doll.
-/

def depth (d : doll) : Nat :=
match d with
  | solid => 0
  | shell inner => 1 + depth inner

#eval depth d0
#eval depth d1
#eval depth d2
#eval depth d3

/-!
Let's see how the term, depth d3, get's evaluated

- depth d3                  (d3 is shell d2), so ..
- 1 + depth d2              (d2 is shell d1), so ,,
- 1 + (1 + (depth d1))      (d1 is shell d0)
- 1 + (1 + (1 + depth d0))  (d0 is solid)
- 1 + (1 + (1 + 0))         1 + (1 + (1 + depth d0))
- 1 + (1 + 1)               1 + (1 + depth d1)
- 1 + 2                     1 + depth d2
- 3                         depth d3
-/