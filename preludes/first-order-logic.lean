/- Exercises from the book: Theorem Proving in Lean 4 -/

/- First order (predicate) logic -/

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
