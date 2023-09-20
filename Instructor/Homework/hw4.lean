/-!
# Homework #4

The PURPOSE of this homework is to greatly strengthen 
your understanding of the construction and use of the 
data types we've introduced to far, especially the sum
and product types. You will be asked to solve problems 
that in some cases will require a bit of programming
creativity, requiring you to to put together several 
of the ideas we've covered so far. 

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
VSCode by opening the corresponding files. Don't be 
afraid to "play around" with the examples in VSCode. 
Doing to will really solidify your understanding. 
-/

/-!
## #2. Is Prod Commutative?

If you have *bread and cheese* can you always get
yourself *cheese and bread?* Let's convert this 
question into one that's both more abstract and 
general as well as formal (mathematical).

If you're given types, α and β, and an arbitrary 
ordered pair of type α × β, can you always construct 
and return a value of type β × α? Prove that the
answer is yes by writing a function that takes any 
value of type α × β value and that returns a value 
of type β × α. Call your function prod_comm.
-/

def prod_comm { α β : Type } : α × β → β × α
| _ => _

/-!
Is the transformation from *α × β* to *β × α*
reversible? That is, given types *α* and *β* (in
that order), then if you have any term of type 
*β × α*, can you always convert it into a term 
of type *α × β*? Prove it by defining a function 
of the appropriate type. Call it prod_com_reverse.
-/

-- Here:

/-! 
## #3: Associativity of Prod

Suppose you have *bread and (cheese and jam)*. 
Can you have *(bread and cheese) and jam* (just 
grouping the *ands* differently)? Let's again turn 
this into an abstract, general, and formal question,
using *α, β,* and *γ* as names instead, of *bread,
cheese,* and *jam*.

Suppose α, β, and γ are arbitrary types. If you're 
given an arbitrary *value* of type α × (β × γ), can
you can always produce a value of type  (α × β) × γ? 

To show that you can, write a function of type 
{ α β γ : Type} → (α × (β × γ)) → ((α × β) × γ).
Call it prod_assoc. We declare the type parameters 
before the colon in our skeleton definition so that 
you don't have to match on them. Hint: You can use 
ordered pair notation to match the input value.
-/

-- Here 

def prod_assoc { α β γ : Type} :  α × (β × γ) → (α × β) × γ
| _ => _

/-!
Prove that the conversion works in the reverse direction
as well, from *(α × β) × γ* to *α × (β × γ)* by defining
a function, *prod_assoc_reverse* accordingly.
-/

-- Here:

/-!
## #4. Is Sum Commutative?

Suppose you have either bread or cheese. Can you
always have either cheese or bread? In other words
are sums *commutative?* That's the technical word
that we use for any *operator*, such as +, with the
property that *a + b* is equivalent to *b + a*. 

Once again let's formulate the question abstractly,
in a general way, and with mathematical precision.

If you have either a value of type α or a value of
type β, then do you have either a value of type β 
or a value of type α? The answer should be obvious.
To prove it, define a function, that, when applied
to any term of type α ⊕ β, returns a value of type 
β ⊕ α. Call it sum_comm. 

Note that in the outline code we provide we use a
syntax that is a bit new. Re-read the material in
the notes if necessary. We declare the type of 
*sum_com* then use a := followed by a *lambda 
expression* that gives the function definition.
That expression, in turn uses an explcit match 
statement. The form you've mostly seen up to now 
is really just notational shorthand for this kind 
of definition.
-/

def sum_comm { α β : Type} : α ⊕ β → β ⊕ α :=
fun s => 
  match s with
  | _ => _
  | _ => _

/-!
Can you always convert a term of type *β ⊕ α* into 
one of type *α ⊕ β*? Prove it by writing a function 
that does it. Call is sum_comm_reverse.
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

Hint: Consider two cases for α ⊕ (β ⊕ γ), and within
the "right" case, consider two further cases. You can
solve this problem with three matching patterns: one
for the first case and two for the second, each of
which starts with a Sum.inr. You will need to use
"nested" expressions involving Sum.inl and Sum.inr
in both matching and to define return result values. 
-/

def sum_assoc { α β γ : Type} : α ⊕ (β ⊕ γ) → (α ⊕ β) ⊕ γ
| (Sum.inl a) => (Sum.inl _)
| (Sum.inr (Sum.inl b)) => _
| _ => _

/-!
Does this conversion also work in reverse? Prove it
with a function that takes a term of the second sum type
(in the preceding example) as an argument and that returns
a value of the first sum type as a result.
-/

-- Here:

/-!
## #6. Products Distribute Over Sums

If you have bread and (cheese or jam) do you have
(bread and cheese) or (bread and jam)? We think so.
Before you move on, think about it!

Define *prod_dist_sum : α × (β ⊕ γ) → (α × β) ⊕ (α × γ).* 
In other words, if you have a value that includes (1) a 
value of type *α* and (2) either a value of type *β* or 
a value of type *γ*, then you can derive a value that is 
either an *α* value and a *β* value, or an *α* value and 
a *γ* value. 
 -/

 def prod_dist_sum {α β γ : Type} : _
 | _ => _
 | _ => _

/-!
Does the preceding principle work in reverse? In other 
words, if you have *(α × β) ⊕ (α × γ)* can you derive 
*α × (β ⊕ γ)*? Concretely, if you have either bread and 
cheese or bread and jam. do you have bread and either 
cheese or jam? Prove it with a function, that converts
any value of type *(α × β) ⊕ (α × γ)* into one of type 
*α × (β ⊕ γ)*.
-/

-- Here:
 
/-!
In the forward (first) direction we can say that products
distribute over sums, just as, say, *4 * (2 + 3)* is the
same as (4 * 2) + (4 * 3)*. In the reverse direction, we
can say that can *factor out* the common factor, *4*. So
in a sense, we're now doing Algebra 1 but with sandwiches! 
-/

/-!
## #8. Sum Elimination 

Suppose you're given: (1) types called *rain, sprinkler,* 
and *wet*; (2) a value of type *rain ⊕ sprinkler*; and (3), 
two functions, of types *rain → wet* and *sprinkler → wet*. 
Show that you can construct and return a value of type *wet*. 
Do this by defining a function called *its_wet*, that, if 
given values of those types as arguments, returns a value of 
type *wet*. 
-/

-- Here

/-!
Now rewrite your function using the type names,
*α, γ,* and *β* instead of *rain, sprinkler* and
*wet*. Call it *sum_elim*. 
-/

-- Here:

/-!
You should now better understand how to program 
with arbitrary values of arbitrary sum types. To do 
so, you need to be able to derive a result of the 
return type, *γ* from *either* of the possible types 
in the sum: from a value of either type *α* or *β*. 
-/

/-!
## Wrap-Up

The programs (functions) we've asked you to write
for this homework are deeply important, in that
they correspond directly to fundamental principles
of logical reasoning. The until now hidden purpose
of this assignment has been to warm you up to this
profound idea. 
-/
