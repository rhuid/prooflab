/- Exercises from the book: Theorem Proving in Lean 4 -/

/- First order (predicate) logic -/

set_option linter.unusedVariables false
set_option diagnostics true

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

-- It is often possible to bring a component of a formula
-- outside a universal quantifier, when it does not depend on the quantified variable

variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun a => Iff.intro
  (fun h => h a)
  (fun hr _ => hr)

open Classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
  (fun h => if hr : r then Or.inr hr
           else Or.inl (fun x =>
             Or.elim (h x)
             (fun hpx => hpx)
             (fun hr' => absurd hr' hr)))
  (fun h => match h with
           | Or.inl hp => (fun x => Or.inl (hp x))
           | Or.inr r  => (fun x => Or.inr r))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h =>
  match h with
  | Or.inl hp => (fun x => Or.inl (hp x))
  | Or.inr hq => (fun x => Or.inr (hq x))
