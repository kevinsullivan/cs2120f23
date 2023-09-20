/-!
# Homework 5: Inhabitedness

The PURPOSE of this homework is to greatly strengthen 
your understanding of reasoning with sum and product
types along with properties of being inhabited or not. 

READ THIS: The collaboration rule for this homework is 
that you may *not* collaborate. You can ask friends and 
colleagues to help you understand the class material, 
but you may not discuss any of these homework problems
with anyone other than one of the instructors or TAs.

Finally, what you're seeing here is the FIRST set of
questions on this homework, giving you an opportunity
to deepen your understanding of the Empty type and its
uses. 
-/

/-!

## PART 1

Of particular importance in these questions is the
idea that *having* a function value (implementation) 
of type *α → Empty* proves that α is uninhabited, in
that if there were a value (a : α) then you'd be able
to derive a value of type Empty, and that simply can't
be done, so there must be no such (a : α). That's the
great idea that we reached at the end of lecture_09.

More concretely every time you see function type that
looks like (α → Empty) in what follows, you can read 
it as saying *there is no value of type α*. Second, if 
youwant to *return* a result of type (α → Empty), to
showing that there can be no α value, then you need 
to return a *function*; and you will often want to do
so by writing the return value as a lambda expression. 
-/

/-!
### #1 Not Jam or Not Cheese Implies Not Jam and Cheese

Suppose you don't have cheese OR you don't have jam. 
Then it must be that you don't have (cheese AND jam).
Before you go on, think about why this has to be true.
Here's a proof of it in the form of a function. The 
function takes jam and cheese implicitly as types.
It takes a value that either indicates there is no
jam, or a value that indicates that there's no cheese,
and you are to construct a value that shows that there
can be no jam and cheese. It works by breaking the first
argument into two cases: either a proof that there is
no jam (there are no values of this type), or a proof
that there is no cheese, and shows *in either case*
that there can be no jam AND cheese. 
-/

def not_either_not_both { jam cheese } :
  ((jam → Empty) ⊕ (cheese → Empty)) → 
  (jam × cheese → Empty) 
| Sum.inl nojam => (fun _ => _)
| Sum.inr _ => _

/-!
### #2: Not One or Not the Other Implies Not Both
Now prove this principle *in general* by defining a 
function, demorgan1, of the following type. It's will
be the same function, just with the names α and β for
the types, rather than the more suggestive but specific
names, *jam* and *cheese*. 

{α β : Type} → (α → Empty ⊕ β → Empty) → (α × β → Empty).
-/

def demorgan1  {α β : Type} : ((α → Empty) ⊕ (β → Empty)) → (α × β → Empty)  
| (Sum.inl noa) => _
| (Sum.inr nob) => _

/-!
### #3: Not Either Implies Not One And Not The Other
Now suppose that you don't have either jam and cheese. 
Then you don't have jam and you don't have cheese. More
generally, if you don't have an α OR a β, then you can
conclude that you don't have an α  Here's a function type that asserts
this fact in a general way. Show it's true in general
by implementing it. An implementation will show that
given *any* types, α and β,  
-/

def demorgan2 {α β : Type} : (α ⊕ β → Empty) → ((α → Empty) × (β → Empty))
| noaorb => _


/-!
### #4: Not One And Not The Other Implies Not One Or The Other 
Suppose you know that there is no α AND there is no β. Then 
you can deduce that there can be no (α ⊕ β) object. Again
we give you the function type that expresses this idea,
and you must show it's true by implementing the function. 
Hint: You might want to use an explicit match expression
in writing your solution.
-/
def demorgan3 {α β : Type} : ((α → Empty) × (β → Empty)) → ((α ⊕ β) → Empty)  
| _ => _

/-!
## PART 2

Coming Soon.
-/


