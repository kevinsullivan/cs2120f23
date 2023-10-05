def nat_to_bin'' : Nat → List Nat
| 0 => [0]
| (n' + 1) => nat_to_bin'' ((n'+1)/2) ++ [((n'+1)%2)] 

#eval nat_to_bin'' 0
#eval nat_to_bin'' 1
#eval nat_to_bin'' 5
#eval nat_to_bin'' 6    

/-!
There are two problems. First, it prepends a superfluous
leading zero to outputs for other than input 0. Why? Well,
suppose the input is one. What gets returned is the list 
of Boolean digits for 1/2 followed by the 1 resulting from
the evaluation of 1%2. Integer division of one by two is
zero, so we get an extra zero on the left. 

The solution is to have both zero and one as base cases and 
to recurse only for argument values of 2 or greater. Think 
carefully about what happens now when the argument value is 
1. Trace through the evaluation of the function to see how 
it works in detail.  Here's the revised code. There's still 
a problem with Lean not being able to verify termination. We
address that in the final version to follow. 
-/

def nat_to_bin' : Nat → List Nat
| 0 => [0]
| 1 => [1]
| (n' + 1) => nat_to_bin' ((n'+1)/2) ++ [((n'+1)%2)] 

#eval nat_to_bin' 6    
#eval nat_to_bin' 5
#eval nat_to_bin' 1
#eval nat_to_bin' 0

/-!
With the leading zero problem solved, we now explain the
termination problem. Lean will issue an error if it can't
determine that a recursive function terminations. Structural
recursions always terminate, because inductively defined
objects are final, substructures passed as arguments are
always smaller, and there can be only a finite number of
calls with smaller substructures before reaching a base 
case.

Here, howeer, the argument to the recursive call is not
a substructure of the Nat argument, n, but rather the 
result of applying a divide-by-two function to n. Even
though we can see that the argument always decreases, Lean
isn't "smart" enough to figure that out. 

What we have here is not a structural but rather a 
generative recursion, and when you use generative
recursions, you have to make a convincing argument
that the arguments to recursive calls are always
decreasing relative to the incoming argument values.
What Lean requires is a proof. Here's how we can 
tell Lean to trust us. We promise to give a proof
of the proposition that n/2 is always less than n.
The sorry says, "ok, we lied, we'll work out that
proof and give it to you later, just trust us for
now." That's enough to get rid of the termination
warning, and we have a final algorithm, good enough
for government work, as they say.
-/

