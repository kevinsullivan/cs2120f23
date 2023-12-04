/-!
## Exercises

### Transitivity of Subset Relation

Suppose we have sets, s1, s2, and s3, with s1 ⊆ s2 and s2 ⊆ s3.
Does it necessarily follow that s1 ⊆ s3? In other words, is it
the case that s1 ⊆ s2 → s2 ⊆ s3 → s1 ⊆ s3? First think about in
concrete terms. For example, suppose a bag of pearls is inside a
bag of rice, and that in turn is inside a bag of straw. Are the
pearls inside the bag of straw? Yeah, really they are. Formalize
and prove it in Lean. Hint State the proposition in the language
of set theory then construct a proof of its reduction to logical
definitions.

### Distributivity of Intersection Over Union
-/

#check ∀ (α : Type) (r s t : Set α), (r ∩ (s ∪ t)) = ((r ∩ s) ∪ (r ∩ t))

#check propext

example (α : Type) (r s t : Set α) : (r ∩ (s ∪ t)) = ((r ∩ s) ∪ (r ∩ t)) := by
    apply Set.ext   -- replaces = with logical ↔

    intro x
    apply Iff.intro

    -- forward
    intro h
    cases h with
    | intro hl hr =>
      _




/-!
### DeMorgan's Laws In Set Theory
-/
