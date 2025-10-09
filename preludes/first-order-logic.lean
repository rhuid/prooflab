/- Exercises from the book: Theorem Proving in Lean 4 -/

/- First order (predicate) logic -/

set_option linter.unusedVariables false

variable (α : Type)
variable (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
  (fun h => And.intro (fun w => (h w).1) (fun w => (h w).2))
  (fun ⟨h₁, h₂⟩ x => And.intro (h₁ x) (h₂ x))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun hpq hp x => (hpq x) (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun hpq x => Or.elim hpq
  (fun hp => Or.inl (hp x))
  (fun hq => Or.inr (hq x))

-- Bring a component of a formula outside a universal quantifier,
-- when it does not depend on the quantified variable

variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun a => Iff.intro
  (fun h => h a)
  (fun hr _ => hr)

example : α → ((∀ x : α, r) ↔ r) := by
  intro ha
  apply Iff.intro
  { intro h
    exact h ha }
  { intro hr
    exact (fun _ => hr)}

variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun a => Iff.intro
  (fun h => h a)
  (fun hr _ => hr)

example : α → ((∀ x : α, r) ↔ r) := by
  intro ha
  apply Iff.intro
  { intro h
    exact h ha }
  { intro hr
    exact (fun _ => hr)}
