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





/-!
The rightmost digit of a binary expansion of a number, n,
is 0 if n is even and 1 if n is odd. In other words, the
rightmost binary digit is n%2. To get the next digit, you
use integer division to divide n by 2, and repeat. 

Here's a first version. If the input is 0 it returns the
list of binary digits, [0]. Otherwise it returns a list 
of all the digits to the left of the last digit, whcih is
computed recursively, with the singlton list containing
the correct rightmost digit appended at the end.

As an example, suppose we're given a row index of 5.
We want its binary expansion as a list of bits, which 
is [1,0,1]. That's *1*2^2 + 0*2^1 + 1*2^0*, which in
turn is *4 + 0 * 1*, which is 5. 

The basic idea then is as follows. If the input, n, is 
0, we'll return [0] (the list containing just zero). If
the the input is 1, we'll return [1]. Otherwise n is at
least 2, so we can write it as n = n' + 2. We thus have
three cases to consider, and have already give solutions
for the first two.

So now suppose *n = n' + 2* for some *n'*. The rightmost 
bit is (n%2)*. Once we have this bit in hand, we want to 
eliminate it, shift all the remaining bits one place to 
the right and repeat. To throw away the rightmost bit of 
*n*, we just divide it by 2.

So now we have our algorithm. If n is a base case, output 
the corresponding singleton list of binary digits. In any
other case, we output the list obtained by appending two
lists: (1) the recursively computed list of digits to the
left of the rightmost bit, and (2) the list containing just
the rightmost bit. 

To make our code even clearer, we'll *reify* the abstract
operations of extracting the rightmost bit, and shifting
all remaining bits to the right.
-/

