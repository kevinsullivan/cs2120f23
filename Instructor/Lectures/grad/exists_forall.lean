example :
∀ (Person : Type)
  (Loves : Person → Person → Prop),
  (∃ (q : Person), ∀ (p : Person), Loves p q) →
  (∀ (p : Person), ∃ (q : Person), Loves p q) :=
λ _ _ sel k => match sel with
| ⟨ joe, everyone_loves_joe⟩  =>
  ⟨ joe, everyone_loves_joe k⟩

variable
  (Ball : Type)
  (Heavy : Ball → Prop)
  (Red : Ball → Prop)

example : (∃ (b : Ball), Red b ∧ Heavy b) → (∃ (b : Ball), Red b) :=
λ h => match h with
| ⟨ rhb, bisredandheavy ⟩ => ⟨rhb , bisredandheavy.left⟩

example : (∃ (b : Ball), Red b ∧ Heavy b) → (∃ (b : Ball), Red b ∨ Heavy b) :=
λ h => match h with
| ⟨ rhb, bisredandheavy ⟩ => ⟨rhb, Or.inr bisredandheavy.right⟩

example : (¬((∀ (b : Ball), Red b))) → (b : Ball) → (∃ (b: Ball), ¬(Red b)) :=
λ nabr aball => ⟨ aball, λ rb => _⟩

example : (∃ (b: Ball), ¬(Red b)) → (¬((∀ (b : Ball), Red b))) :=
λ nonred =>
  match nonred with
  | ⟨ nrb, pfnr ⟩ => λ h =>
    let rb := (h nrb)
    False.elim (pfnr rb)

example :
  ∀ (T : Type)
    (P : T → Prop),
    ¬ (∀ (t : T), P t) → (∃ (t : T), ¬ P t) :=
λ T P h => match (Classical.em ((∀ (t : T), P t))) with
| h => match h with
  | Or.inl l => by contradiction
  | Or.inr r => _
