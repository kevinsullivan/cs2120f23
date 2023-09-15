/-!
# Homework #4

The purpose of this homework is to strengthen your
understanding of the construction and use of the data
types we've introduced to far: Empty, Unit, Bool, Nat,
String, Sum, Product, and function types. You will be 
asked to solve some problems that in some cases will
require a bit of creative thinking, where you start
to put together several of the ideas we've covered. 

## Overview and Rules

It is vitally important that you learn how to solve
these problems on your own. You will have to be able
to do this to do well on the first exam, a month or
so away. Therefore, the collaboration rule for this 
homework is that you may *not* collaborate. You can 
ask friends and colleagues to help you understand 
the material in the class notes, but you may not 
discuss this homework itself with anyone other than one
of the instructors or TAs.
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

/-! #2: Associativity of Prod

Suppose α, β, and γ are arbitrary types. If you're 
given an arbitrary *value* of type α × (β × γ), you
can always produce a value of type  (α × β) × γ. To
show that this claim is true, write a function of 
type { α β γ : Type} → α × (β × γ) → (α × β) × γ.
You can call it prod_assoc. You may declare the
type parameters before the colon in your definition
if you wish. Hint: You can use ordered pair notation
to match the input value
-/

-- Here 

def prod_assoc { α β γ : Type} :  α × (β × γ) → (α × β) × γ
| (a, (b, c)) => ((a, b), c)

/-!
## #3. Is Prod Commutative?

If you're given an arbitrary ordered pair (a, b),
of type α × β, can you always construct and return
a value of type β × α? If your answer is yes, then
prove it by writing a function that takes an α × β 
value and returns a β × α value, where α and β are
arbitary types. Call your function prod_comm.
-/

def prod_comm { α β : Type } : α × β → β × α
| (a, b) => (b, a)

/-!
## #4. Is Sum Commutative?

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
## #5: Is Sum Associative? 

Are sum types associative? That is, if you're given an 
arbitrary value of type α ⊕ (β ⊕ γ) can you construct 
and return a value of type (α ⊕ β) ⊕ γ? If you answer
yes, prove it with a function of type α ⊕ (β ⊕ γ) → 
(α ⊕ β) ⊕ γ. Call it sum_assoc.
-/

def sum_assoc { α β γ : Type} : α ⊕ (β ⊕ γ) → (α ⊕ β) ⊕ γ
| (Sum.inl a) => (Sum.inl (Sum.inl a))
| (Sum.inr (Sum.inl b)) => (Sum.inl (Sum.inr b))
| (Sum.inr (Sum.inr g)) => (Sum.inr g)

/-!
## #6. Even more fun!

Define a function, wowser, that "proves" α × (β ⊕ γ) → 
(α × β) ⊕ (α × γ). In other words, if you have a value
that include (2) a value of type α and (2) either a value 
of type β or a value of type γ, then you can derive a value 
that is either an α value and a β value, or an α value and 
a γ value. 
 -/

 def wowser {α β γ : Type} : α × (β ⊕ γ) → (α × β) ⊕ (α × γ)
 | (a, Sum.inl b) => Sum.inl (a,b)
 | (a, Sum.inr g) => Sum.inr (a,g)

/-!
## #7. Sum Elimination 

Suppose you have: types called rain, sprinkler, and wet;
a value of type rain ⊕ sprinkler; and functions of types
rain → wet and sprinkler → wet. Show that you can produce
a value of type wet. Do this by defining a function called
its_wet, that, if given those elements returns a value of 
type wet. 
-/

def its_wet {rain sprinkler wet : Type} : 
  rain ⊕ sprinkler → 
  (rain → wet) → 
  (sprinkler → wet) → 
  wet
| (Sum.inl r), rw, _ => rw r
| (Sum.inr s), _, sw => sw s

