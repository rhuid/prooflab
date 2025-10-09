/- Exercises from the book: Theorem Proving in Lean 4 -/

/- First order (predicate) logic -/

variable (α : Type)
variable (p q : α → Prop)

example : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) :=
  fun h => And.intro
  (fun w => (h w).1) (fun w => (h w).2)
