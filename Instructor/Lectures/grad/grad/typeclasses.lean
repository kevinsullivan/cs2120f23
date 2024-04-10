/-!
We've seen that we can generalize the notion of
mapping objects of one container-like type to
objects of a correspond value of the same type
by replacing each *element* in one container
corresponding objects computed by applying an
element-wise conversion function to each object
in the input container. Here we give two examples
that we saw in class: functions for mapping over
Lists, and functions for mapping over Options.
-/

def list_map {α β : Type} : (α → β) → List α → List β
| _, [] => []
| f, h::t => f h :: list_map f t

def option_map {α β : Type} : (α → β) → Option α → Option β
| _, Option.none => Option.none
| f, (Option.some a) => some (f a)

/-!
We now present two more "container-like" types that
we saw in class. The Box type is a container type for
exactly one object some type, α, and Tree is such a
type for representing binary trees of such objects.
-/
inductive Box (α : Type)
| contents (a : α)

def box_map {α : Type} : (α → β) → Box α → Box β
| f, (Box.contents a) => Box.contents (f a)

inductive Tree (α : Type): Type
| empty
| node (a : α) (l r : Tree α) : Tree α

def tree_map {α : Type} : (α → β) → Tree α → Tree β
| _, (Tree.empty) => Tree.empty
| f, (Tree.node a l r) => Tree.node (f a) (tree_map f l) (tree_map f r)

/-!
The crucial idea from last class is that we can
abstract from not just type type of elements in
a polymorphic container-like object, but we can
also abstract from the container type itself, by
associating with a container type a type-specific
*map* function. We add tick marks here because
we're about to replace this good definition with
an even better one.
-/

structure functor'' (c : Type → Type) where
map {α β : Type} (f : α → β) (ic : c α) : c β

/-!
The better definition declares the functor type
to be a *typeclass*. The result is still the same
type definition, but *instances* of this type will
now be registered with an automated instance lookup
subsystem of Lean that supports implicit *instances*.
-/

@[class]
structure functor' (c : Type → Type) where
map {α β : Type} (f : α → β) (ic : c α) : c β

/-!
It's preferred to use the class keyword rather
than the @[class] annotation, but you'll see
both in practice.
-/
class functor (c : Type → Type) where
map {α β : Type} (f : α → β) (ic : c α) : c β

/-!
We're now using our upgraded functor definition.
There is no change in this code from earlier. We
add '' to the names from the original code, as
we are about to replace these definitions with
better ones.
-/
def list_functor'' : functor'' List  := functor''.mk list_map
def option_functor'' : functor'' Option  := functor''.mk option_map


/-!
Here is our original definition of a polymorphic
mapping function that can operate on any *container*
type for which we have a functor instance. You will
recall that such an instances carries a type-specific
implementation of *map*. The key observation here is
that we have to pass the functor instance explicitly.
-/
def do_map' {α β : Type} {c : Type → Type} (m : functor'' c) :
  (f : α → β) → c α → c β
| f, c => m.map f c

#eval do_map' list_functor'' Nat.succ [1,2,3]  -- [2, 3, 4]
#eval do_map' option_functor'' (λ s => s ++ "!") (some "Hi")

/-!
Now recall that we want to be able to map a
function over any container using <$> notation,
where <$> invokes the do_map' function. As an
example, we'd like to write *Nat.succ <$> a_box*,
to map the successor function over a Box Nat
value. But we've seen that that doesn't work.
See the broken examples in the last problem in
HW6.
-/

/-!
Here's how we fix our definition. Note the change
in the type definition of this function! The change
in the parentheses around (m : functor c) to square
brackets instructs Lean to search its registry of
functor *typeclass* instances for a suitable value
and to pass it as an implicit *instance* argument.
-/

def do_map {α β : Type} {c : Type → Type} [m : functor c] :
  (f : α → β) → c α → c β
| f, c => m.map f c

/-!
But we're not done yet. What's the problem?
-/
#reduce do_map Nat.succ [1,2,3]
#reduce do_map Nat.succ (Box.contents 1)

/-!
We need registered typeclass instances!
-/

instance : functor List := ⟨ list_map ⟩
instance : functor Box := ⟨ box_map ⟩
instance : functor Option := ⟨ option_map ⟩

-- Yay!
#reduce do_map Nat.succ [1,2,3]
#reduce do_map Nat.succ (Box.contents 1)
#reduce do_map Nat.succ (some 3)

/-!
We now have what is syntactically a *binary*
do_map function; so it now makes sense to define
an infix notation for this case.
-/

infix:50 " <$> " => do_map
#reduce Nat.succ <$> (Box.contents 1)

/-!
But whereas <$> worked before for lists but
not for Box, now it works for Box but not for
List. Look at the error message. What's going
on?
-/
#reduce Nat.succ <$> [1,2,3]
#reduce do_map Nat.succ [1,2,3]

/-!
Right: Lean already defines <$> for list functors,
so it doesn't know whether to use our definition of
<$> or its own.
-/

/-!
So this brings us to the punch line of this entire
discussion. Lean defines the functor typeclass but
it's called Functor (with a capital F). It also
defines Functor instsances for several container
types in its library, including List and Option.

So now that you understand what a functor is and
how to use this type, you're ready to go. Let's
see our examples using Lean's Functor typeclass.
-/

#reduce Functor.map Nat.succ [1,2,3]
#reduce Nat.succ <$> [1,2,3]

/-!
Let's practice in a separate file: one that does
not overload the <$> operator (again).
-/
