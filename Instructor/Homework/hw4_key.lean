/-!
# Homework #4

The purpose of this homework is to strengthen your
understanding of the construction and use of the data
types we've introduced to far: Empty, Unit, Bool, Nat,
String, Sum, Product, and function types. You will be 
asked to solve some problems that in some cases will
require a bit of creative thinking, where you start
to put together several of the ideas we've covered. 


READ THIS: It is vitally important that you learn how 
to solve these problems on your own. You will have to 
be able to do this to do well on the first exam, a month 
or so away. Therefore, the collaboration rule for this 
homework is that you may *not* collaborate. You can ask 
friends and colleagues to help you understand the class
material, but you may not discuss this homework itself 
with anyone other than one of the instructors or TAs.
-/

/-!
## #1: Read All of the Class Notes

You won't be graded on this part of the assignment,
but it is nevertheless serious and required work on
your part. Read and genuinely understand *all* the 
class notes through lecture_08. Everything that we
have covered in class is covered in the notes, and
more. You can work with the examples in the notes in
VSCode with the corresponding files. Don't be afraid 
to "play around" with the examples in VSCode to get
a really solid understanding. 
-/

/-!
## #2. Is Prod Commutative?

If you have *bread and cheese* can you always get
yourself *cheese and bread?* Let's again convert
this question into one that's both more abstract 
and general as well one that's completely formal
(mathematical).

If you're given an arbitrary ordered pair of type 
α × β, can you always construct and return a value 
of type β × α? If your answer is yes, then prove it 
by writing a function that takes *any* value of type
α × β value and that returns a value of type β × α. 
Call your function prod_comm.
-/

def prod_comm { α β : Type } : α × β → β × α
| (a, b) => (b, a)

/-!
Is the transformation from *α × β* to *β × α*
reversible? That is, if you have any term of 
type *β × α*, can you always convert it into 
a term of type *α × β*? Prove it by defining
a function of the appropriate type. You can 
call it prod_com_reverse.
-/

-- Here:

/-! 
## #3: Associativity of Prod

Suppose you have *bread and (cheese and jam)*. 
Can you have *(bread and cheese) and jam* (just 
grouping the *ands* differently)? Let's turn this
into a slightly more abstract and formal question,
using *α, β,* and *γ* as names instead, of *bread,
cheese,* and *jam*.

Suppose α, β, and γ are arbitrary types. If you're 
given an arbitrary *value* of type α × (β × γ), can
you can always produce a value of type  (α × β) × γ? 

To show that you can, write a function of type 
{ α β γ : Type} → (α × (β × γ)) → ((α × β) × γ).
Call it prod_assoc. Declare the type parameters 
before the colon in your definition so that you
don't have to match on them. Hint: You can use 
ordered pair notation to match the input value.
-/

-- Here 

def prod_assoc { α β γ : Type} :  α × (β × γ) → (α × β) × γ
| (a, (b, c)) => ((a, b), c)


/-!
## #4. Is Sum Commutative?

Suppose you have either bread or cheese. Can you
always have either cheese or bread? In other words
are sums *commutative?* That's the technical word
that we use for any *operator*, such as +, with the
property that *a + b* is convertible to *b + a*. 

One again let's formulate the question abstractly,
in a general way, and with mathematical precision.

If you have either a value of type α or a value of
type β, then do you have either a value of type β 
or a value of type α? The answer should be obvious.
To prove it, define a function, that, when applied
to any term of type α ⊕ β, returns a value of type 
β ⊕ α. Call it sum_comm.  
-/

def sum_comm { α β : Type} : α ⊕ β → β ⊕ α 
| Sum.inl a => Sum.inr a
| Sum.inr b => Sum.inl b

/-!
Can you always convert a term of type *β ⊗ α* into 
one of type *α × β*? If so, prove it by writing a
function that does it.
-/

-- Here:



/-!
## #5: Is Sum Associative? 

If you have bread or (cheese or jam), can you always
have (bread or cheese) or jam? In other words, are sum
types *associative*? That's the word we use for an
operator with the property that *a + (b + c)* is 
equivalent to *(a + b) + c*. You can *associate* the
arguments differently without really changing the
meaning. 

So, if you have an arbitrary value of type α ⊕ (β ⊕ γ) 
can you construct a value of type (α ⊕ β) ⊕ γ? If you 
answer yes, prove it by defining a function of type 
α ⊕ (β ⊕ γ) → (α ⊕ β) ⊕ γ. Call it sum_assoc.
-/

def sum_assoc { α β γ : Type} : α ⊕ (β ⊕ γ) → (α ⊕ β) ⊕ γ
| (Sum.inl a) => (Sum.inl (Sum.inl a))
| (Sum.inr (Sum.inl b)) => (Sum.inl (Sum.inr b))
| (Sum.inr (Sum.inr g)) => (Sum.inr g)

/-!
And does the conversion also work in reverse? Prove it
with a function that takes a term of the second sum type
(in the preceding example) as an argument and that returns
a value of the first sum type.
-/

-- Here:

/-!
## #6. Even more fun!

If you have bread and (cheese or jam) do you have
(bread and cheese) or (bread and jam)? We think so.
Before you move on, think about it!

Define *wowser : α × (β ⊕ γ) → (α × β) ⊕ (α × γ).* 
In other words, if you have a value that includes (1) a 
value of type *α* and (2) either a value of type *β* or 
a value of type *γ*, then you can derive a value that is 
either an *α* value and a *β* value, or an *α* value and 
a *γ* value. 
 -/

 def prod_dist_sum {α β γ : Type} : 
  α × (β ⊕ γ) → (α × β) ⊕ (α × γ)
 | (a, Sum.inl b) => Sum.inl (a,b)
 | (a, Sum.inr g) => Sum.inr (a,g)

/-!
Does the preceding principle work in reverse? In other 
words, if you have *(α × β) ⊕ (α × γ)* can you derive 
*α × (β ⊕ γ)*? Concretely, if you have either bread and 
cheese or bread and jam. do you have bread and either 
cheese or jam? Prove it with a function, that converts
any value of type *(α × β) ⊕ (α × γ)* into one of type 
*α × (β ⊕ γ)*.
-/

def  wowser_rev {α β γ : Type} : (α × β) ⊕ (α × γ) → α × (β ⊕ γ) 
| Sum.inl (a, b) => (a, Sum.inl b)
| Sum.inr (a, g) => (a, Sum.inr g)
 
/-!
In the forward (first) direction we can say that products
distribute over sums, just as, say, *4 * (2 + 3)* is the
same as (4 * 2) + (4 * 3)*. In the reverse direction, we
can say that can *factor out* the common factor, *4*. So
in a sense, we're now doing mathematical logic but with
sandwiches! 
-/

/-!
## #8. Sum Elimination 

Suppose you have: (1) types called *rain, sprinkler,* and 
*wet*; (2) a value of type *rain ⊕ sprinkler*; and (3), 
functions of types *rain → wet* and *sprinkler → wet*. 
Show that you can produce a value of type *wet*. Do this 
by defining a function called *its_wet*, that, if given 
values of those types as arguments, returns a value of 
type *wet*. 
-/

def its_wet {rain sprinkler wet : Type} : 
  rain ⊕ sprinkler → 
  (rain → wet) → 
  (sprinkler → wet) → 
  wet
| (Sum.inl r), rw, _ => rw r
| (Sum.inr s), _, sw => sw s

/-!
Now rewrite your function using the type names,
*α, γ,* and *β* instead of *rain, sprinkler* and
*wet*. Call it *sum_elim*. 
-/


-- This answer is already great
def sum_elim' {α β γ : Type} : 
  α ⊕ β → 
  (α → γ) → 
  (β → γ) → 
  γ
| (Sum.inl r), rw, _ => rw r
| (Sum.inr s), _, sw => sw s

-- Changing a few identifiers makes it even nicer
def sum_elim {α β γ : Type} : 
  α ⊕ β → 
  (α → γ) → 
  (β → γ) → 
  γ
| (Sum.inl a), ab, _ => ab a
| (Sum.inr b), _, bc => bc b

-- Here:

/-!
What you've now by understand the sum_elim function, 
is to understanding how to use values of sum types* in
general. given sum value and functions for each case,
(1): do case analysis on the sum by pattern matching; 
(2), within each case, (1) get the value it carries (of 
type either α or β); (2) apply the correct function to 
it to get a return value of the fina result type, here
called γ to keep things general.  
-/


/-!
You should now better understand how to program 
with arbitrary values of arbitrary sum types. To do 
so, you need to be able to derive a result of the 
return type, *γ* from *either* of the possible types 
in the sum: from a value of either type *α* or *β*. 
-/
