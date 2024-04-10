/-!
The algebraic structure, monoid.

A monoid comprises a carrier set of objects (here all
values of any given type, α), an associative binary
operator, op, closed on this set, and an element, e,
that is both a left and right identity for op.
-/

structure monoid' (α : Type) where -- carrier set is α
(op : α → α → α)                  -- binary operator
(id : α)                          -- identity element
(left_id: ∀ a, op id a = a)       -- proof it's left id
(right_id: ∀ a, op a id = a)      -- proof it's right id
(op_assoc:                        -- proof op's associative
  ∀ a b c,
    op (op a b) c = op a (op b c))

/-!
Foldr applied to a monoid returns an n-ary version
of the monoid operator, taking an arbitrary length
list of "n" arguments, and reducing it to a single
value by "op-ing" them all up (e.g., adding them).
The type of the returned function is List α → α.
-/
def foldr' {α : Type} : monoid' α → List α → α
| m, [] => m.id
| m, h::t => m.op h (foldr' m t)

/-!
Examples
-/

def nat_add_monoid' : monoid' Nat :=
  ⟨  Nat.add,
    0,
    λ a => by simp [Nat.add],
    λ a => by simp,
    Nat.add_assoc
   ⟩

def add_n := foldr' nat_add_monoid'   -- n-ary addition
#check (add_n)                      -- right type
#eval add_n [1,2,3,4,5]             -- works right

/-!
-/

#check Nat.mul_assoc

def nat_mul_monoid' : monoid' Nat :=
  ⟨  Nat.mul,
    1,
    λ a => by simp [Nat.mul],
    λ a => by simp,
    Nat.mul_assoc
   ⟩

def mul_n := foldr' nat_add_monoid'   -- n-ary addition
#check (mul_n)                      -- right type
#eval mul_n [1,2,3,4,5]             -- works right


/-!
-/
def string_append_monoid' : monoid' String :=
  ⟨  String.append,
    "",
    λ a => by simp [String.append],
    λ a => by simp [String.append],
    sorry
   ⟩

def app_n := foldr' string_append_monoid'
#check (app_n)
#eval app_n ["He", " ", "went to ", "the store."]


/-!
Another mathematical structure: Functor.
-/

#check (@Option)

def pred : Nat → Option Nat
| Nat.zero => Option.none
| (Nat.succ n') => n'

#reduce pred 3
#reduce pred 0

def list_map {α β : Type} : (α → β) → List α → List β
| _, [] => []
| f, h::t => f h :: list_map f t

def option_map {α β : Type} : (α → β) → Option α → Option β
| _, Option.none => Option.none
| f, (Option.some a) => some (f a)

/-!
structure functor' (α β : Type) (c : Type → Type) : Type where
map (f : α → β) (ic : c α) : c β
-/

structure functor (c : Type → Type) where
map {α β : Type} (f : α → β) (ic : c α) : c β

/-
def convert' {α β : Type} (c : Type → Type) (m : functor c) : (f : α → β) → c α → c β
| f, c => m.map f c
-/

def convert {α β : Type} {c : Type → Type} (m : functor c) : (f : α → β) → c α → c β
| f, c => m.map f c

-- instance of functor for list
def list_functor : functor List  := functor.mk list_map
/-
#reduce convert List list_functor Nat.succ [1,2,3,4,5]
-/
#reduce convert list_functor Nat.succ [1,2,3,4,5]

-- instance of functor for option
def option_functor : functor Option  := functor.mk option_map
#reduce convert option_functor Nat.succ (Option.some 4)


inductive Box (α : Type)
| contents (a : α)

/-!
Homework: Define a functor instance for the Box type and
show that you can then use the convert function to map a
Box α to a Box β. You will first need to define a Box map
function, box_map.
-/

def box_map {α β : Type} : (f : α → β) → Box α → Box β
| f, (Box.contents a) => Box.contents (f a)
def box_functor : functor Box  := functor.mk box_map
#reduce convert box_functor Nat.succ (Box.contents 4)


inductive Tree (α : Type): Type
| empty
| node (a : α) (l r : Tree α) : Tree α

def tree_map : (α → β) → Tree α → Tree β
| _, Tree.empty => Tree.empty
| f, (Tree.node a l r) => Tree.node (f a) (tree_map f l) (tree_map f r)

#reduce tree_map Nat.succ Tree.empty

def a_tree :=
  Tree.node
    1
    (Tree.node
      2
      Tree.empty
      Tree.empty
    )
    (Tree.node
      3
      Tree.empty
      Tree.empty
    )

#reduce tree_map Nat.succ a_tree

/-!
-/

@[class]
structure monoid (α : Type) where -- carrier set α
(op : α → α → α)                  -- binary operator
(e : α)                          -- identity element
(left_id: ∀ a, op e a = a)       -- proof it's left id
(right_id: ∀ a, op a e = a)      -- proof it's right id
(op_assoc:                        -- proof op's associative
  ∀ a b c,
    op (op a b) c = op a (op b c))

open monoid

def foldr {α : Type} : [monoid α] → List α → α
| m, [] => m.e
| m, h::t => m.op h (foldr t)

instance : monoid Nat := ⟨ Nat.add, 0, sorry, sorry, sorry ⟩
instance : monoid String := ⟨ String.append, "", sorry, sorry, sorry ⟩

def nary_add := @foldr Nat
#eval nary_add [1,2,3,4,5]

def nary_append := @foldr String
#eval nary_append []

def nary_and := @foldr Bool
#eval nary_and [true]         -- no typeclass instance for Bool
