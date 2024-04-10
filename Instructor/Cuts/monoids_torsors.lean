
-- OLD
/-!
In Lean, even as a simple a structure as a monoid is
implemented by combining several even simpler parts.
In particular, the Add typeclass is used to overload
addition (with notation +) for a given type (Rotation
in our case) with *no* additional structure required.

The AddSemigroup typeclass extends the Add typeclass
(thus inheriting an add function implementation) with
a proof of its associativity. A semigroup is simply a
set with an *associative* addition operation.

Finally a monoid is a semigroup with a value that will
serve as a left and right identity (with proofs that it
is one). The AddMonoid typeclass is what we will have to
instantiate for the Rotation type. In addition to a *zero*
field (and proofs), this typeclass provides some additional
convenience features, which we'll introduce below.
-/


/-!
Indeed, + is overloaded (by typeclass instances) for many
types defined in mathlib, including Nat and many others. For
any type, + can be overloaded by instantiating the Add class,
just as we've done here for the Rotation type.
-/

/-!
Jumping ahead a little, we can assert and prove something:
here a simple test case. Open your Lean InfoView and put your
cursor at the end of each line to see what the effect of each
tactic is on the proof state. First we simplify the + notation
to Add.add, then we simplify Add.add to add_Rotations, and as
the last step, we simplify/reduce addRotations r120 r240 to r0.
The remaining step is to prove r0 = r0, which Lean does for us
automatically using rfl. QED!
-/

example : r120 + r240 = r0 :=
by
simp [(· + ·)]
simp [Add.add]
simp [add_Rotations]


/-!
Note: in this example, we've given the Add Rotation instance
an explicit name, *add_rot_inst*. In general, we don't have to
name typeclass instances, as they will be fetched by Lean's
instance lookup/synthesis operation. We give a name in this
case to help explain class and instance inheritance in what
now follows.
-/


/-!
In Lean, AddSemiroup extends Add, and thus inherits Add.add
as a field. The AddSemigroup typeclass simply adds an field
to hold a proof that a given add function is associative.

Here's the essence of Lean's definition of AddSemigroup.
We're not going to try to provide proofs when we create
instances,m so we'll plan to stub out values of this proof
field when creating instances, at least for now.

- class AddSemigroup (G : Type u) extends Add G where
-   add_assoc : ∀ a b c : G, a + b + c = a + (b + c)
-/

-- OLD
With these instances in hand, we can now construct an instance
of AddZeroClass for Rotations. Here's the class definition. Note
that this class uses abstract notation, 0 and + for Zero.zero and
Add.add when writing the axioms that enforce that 0 is a left and
right identity.

class AddZeroClass (M : Type u) extends Zero M, Add M where
  protected zero_add : ∀ a : M, 0 + a = a
  protected add_zero : ∀ a : M, a + 0 = a

We give a proofs of zero_add and add_zero here, to give you
a preview of what's to come.  If you open your Lean InfoView
and put your cursor at the end of each line of the proof you
can see how the proof works: it's basically just by unfolding
and applying definitions.
-/

instance : AddZeroClass Rotation := {
  -- Give values to inherited fields
  toZero := zero_rot      -- use explicitly named instance
  toAdd := inferInstance  -- Lean finds/synthesizes instance
  -- Give values to fields newly added by AddZeroClass
  -- Be sure to step through the proof using Lean InfoView
  zero_add := by
    intro a         -- assume a is arbitrary rotation
    simp [( · + ·)] -- simplify + notation to Add.add
    simp [Add.add]  -- simplify Add.add to add_Rotations
    show add_Rotations r0 a = a -- eliminate 0 notation
    simp [add_Rotations]  -- simplify using definition
  add_zero := by
    intro a         -- assume a is arbitrary rotation
    show add_Rotations a r0 = a -- eliminate 0 notation
    simp [add_Rotations]  -- we'll leave this one stubbed out
    sorry           -- not reducing; what's the BUG?
}



/-!
Note again that AddSemigroup G extends (i.e., inherits from)
Add G. So when forming an instance of AddSemigroup, we have
to provide an instance of AddSemigroup, as the value of a field
implicitly named toAdd ("to" followed by the name, Add, of the
inherited class).
-/

-- Use explicit instance name to set parent class field ...
instance : AddSemigroup Rotation :=
  {
    toAdd := add_rot_inst   -- inherit add from Add Rotations instance
    add_assoc := sorry      -- add requirement that add be associative
                            -- stubbed: accepted as an axiom w/o proof
  }

/-!
A key observation here is that we provide an explicitly named
(instance (add_rot_inst) of the Add typeclass as the value of
the toAdd field here. An AddSemigroup instance thus includes
an Add instance as a field value. In the next section we'll
see that we don't need to use explicit naming. Rather, we can
just have Lean look up (synthesize) a value of the Add class,
as we've already registered one with the typeclass inferencer.
-/
