/-! 
INCOMPLETE AND UNDER CONSTRUCTION

# Inductive Type Definitions

You've seen that we use the keyword, *inductive*, 
to introduce new data types, but what does this word 
really mean?

## A Toy Example

To get to an answer, let's have a look at a traditional
child's toy: the nesting doll.

### Recursive Data

Such a *doll* comes in two forms: either it's a *solid*
(very inner) doll, or a *shell* with another *doll* inside 
it. We can represent this concept formally as an inductive
data type. We'll call it *doll*.
-/

inductive doll : Type
| solid
| shell (d : doll)

open doll

/-!
We can now construct dolls of arbitrary depth, always starting 
with a solid doll and then iterating the application of shell
as many times as desired, always yielding a new doll or a size
larger by one.
-/
def d0 := solid
def d1 := shell d0
def d2 := shell d1
def d3 := shell d2

/-!
Let's see what d3 really looks like. We'll just keep
expanding the "inner" dolls until we reach the final
solid doll at the "bottom," that can be expanded no
further.

- d3 =
- shell d2 =
- shell (shell d1) =
- shell (shell (shell d0)) =
- shell (shell (shell solid))

The final term is the actual value of d3.
-/

/-!
### Recursive Function

Now suppose we're given an arbitrary object of type *doll*
and that we want to count how many layers deep it goes and
return that result as a natural number. Given a doll, we have 
to analyze it to determine its form: by pattern matching. If 
it's solid, the answer is zero. If it's of the form (shell d), 
where d is the smaller doll inside the shell, then the answer 
is one, for the shell, plus the depth of the inner doll.
-/

def depth : doll → Nat 
| solid => 0                        -- base case
| shell d => 1 + depth d            -- recursive case

#eval depth d0
#eval depth d1
#eval depth d2
#eval depth d3

/-!
Let's see how the term, depth d3, get's evaluated

- depth d3                  (d3 is shell d2), so 1 + ...
- 1 + depth d2              (d2 is shell d1), so 1 + ...
- 1 + (1 + (depth d1))      (d1 is shell d0), so 1 + ...
- 1 + (1 + (1 + depth d0))  (d0 is solid) so 0
- 1 + (1 + (1 + 0))         1 + (1 + (1 + depth d0))
- 1 + (1 + 1)               1 + (1 + depth d1)
- 1 + 2                     1 + depth d2
- 3                         depth d3
-/