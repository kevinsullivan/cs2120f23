/-!
Another lesson: The *real* elimination rules for types
are their induction principles, also called *recursors*.
Much of what you've learned so far is nice notation with
recursor application *under the hood,* as they say.

What are the walk-away lessons so far?

First, Each inductive type has a corresponding induction
principles. It provides a way to compute a value or proof
for any value of a *motive* type.

The induction principle for Nat has two crucial arguments:
(1) a base case result, and (2) a step function. A base case
value is defined without further nesting. The step function
computes the correct result for n = n' + 1 given the value,
n' (derivable from n of course), and the currect answer for
n'.
-/
