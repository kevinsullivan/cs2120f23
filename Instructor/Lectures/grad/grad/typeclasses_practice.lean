#reduce Nat.succ <$> [0,1,2]

#check Functor

/-!
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α := Function.comp map (Function.const _)
-/

#check Function.comp
#check Function.const

inductive Box (α : Type)
| contents (a : α)

def box_map {α : Type} : (α → β) → Box α → Box β
| f, (Box.contents a) => Box.contents (f a)

def box_mapConst {α β : Type} :  α → Box β → Box α
| a, _ => Box.contents a          -- no other choice

/-!
As usual there are multiple notations for defining
strucure instances. Here we need a Functor instance
with box_map and box_MapConst as field values. The
first notation uses an abstract syntax to apply the
constructor to its arguments. The second example uses
concrete syntax for constructor application defined
by the ⟨ ⟩ "outfix" notation. These lines of "code"
do/mean exactly the same thing.

- instance : Functor Box := Functor.mk box_map box_mapConst
- instance : Functor Box := ⟨ box_map, box_mapConst ⟩

However, we prefer a third, {} notation. It allows you
to give field values in any order by name and will fill
in default values given in structure definitions, which
you can override by giving values explicitly here. In the
first line, we give box_map and box_mapConst explicitly,
by name, but in a different order than they appear in the
structure definition, to show that it works. The second
example gives only box_map as an explicit argument, and
Lean picks up the default from the structure definition.

- instance : Functor Box := { mapConst := box_mapConst, map := box_map }

Here then is the most concise definition we can offer.
We give the box_map argument by name, while Lean picks
up the default definition of mapConst from the typeclass
definition.
-/

instance : Functor Box := { map := box_map }

/-!
And now, finally, we can map functions such as Nat.succ
over Boxes containing Nat values.
-/

#reduce Nat.succ <$> (Box.contents 2)
