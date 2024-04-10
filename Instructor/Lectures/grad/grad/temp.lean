example : 
  ∀ (P Q R : Prop), 
    (P ∨ Q) → 
    (P → R) → 
    (Q → R) → 
    R := 
by -- starts a program or proof construction using tactics
  -- intros: assume arguments
  intros P Q R rors ptor qtor
  -- cases: case analysis
  cases rors with
  -- case were r is true
  -- exact: takes complete proof term for current goal
  | inl p => exact (ptor p)
  -- case where
  -- apply: like exact
  | inr q => apply (qtor q)