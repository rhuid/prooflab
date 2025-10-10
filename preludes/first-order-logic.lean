/- Exercises from the book: Theorem Proving in Lean 4 -/

/- First order (predicate) logic -/

set_option linter.unusedVariables false
set_option diagnostics true

-- Universal quantifiers

section universal_quantifiers

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

end universal_quantifiers

-- Russell's paradox (barber paradox)
section barber_paradox

variable (Men : Type) (barber : Men)
variable (shaves : Men → Men → Prop)

open Classical in
theorem barber_paradox (h : ∀ x : Men, shaves barber x ↔ ¬ shaves x x) : False :=
  let ⟨h₁, h₂⟩ := h barber
  if h' : shaves barber barber
  then absurd h' (h₁ h')
  else absurd (h₂ h') h'

end barber_paradox

-- Existential quantifiers
section existential_quantifiers

variable (α : Type)
variable (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun ⟨_, h⟩ => h

example (a : α) : r → (∃ x : α, r) :=
  fun hr => Exists.intro a hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
  (fun ⟨x, hpxr⟩ => ⟨Exists.intro x hpxr.1, hpxr.2⟩)
  (fun ⟨⟨x, hpx⟩, r⟩ => Exists.intro x ⟨hpx, r⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
  (fun ⟨x, hpq⟩ => match hpq with
                  | Or.inl hp => Or.inl ⟨x, hp⟩
                  | Or.inr hq => Or.inr ⟨x, hq⟩)
  (fun h => match h with
           | Or.inl ⟨x, hp⟩ => Exists.intro x (Or.inl hp)
           | Or.inr ⟨x, hq⟩ => Exists.intro x (Or.inr hq))

open Classical

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
  (fun ha ⟨x, he⟩ => absurd (ha x) he)
  (fun h x => byContradiction (fun hnp => h ⟨x, hnp⟩))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
  (fun ⟨x, hp⟩ h => absurd hp (h x))
  (fun h => byContradiction (fun hnp =>
                            let h' : ∀ x, ¬ p x := fun x hp => hnp ⟨x, hp⟩
                            h h'))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
  (fun hnp x hp => hnp ⟨x, hp⟩)
  (fun h ⟨x, hp⟩ => (h x) hp)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
  (fun h => byContradiction
           (fun h' => let h'' : ∀ x, p x :=
                     fun x => byContradiction (fun hnpx => h' ⟨x, hnpx⟩)
           h h''))
  (fun ⟨x, hnp⟩ h => absurd (h x) hnp)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
  (fun h ⟨x, hp⟩ => h x hp)
  (fun h x hp => h ⟨x, hp⟩)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
  (fun ⟨x, hpr⟩ hp => hpr (hp x))
  (fun h => if hr : r then ⟨a, fun _ => hr⟩
           else have h₁ : ¬ ∀ x, p x := fun hx => hr (h hx)
                have h₂ : ∃ x, ¬ p x := byContradiction
                                        (fun hnp =>
                                        have hpx : ∀ x, p x := fun x => by grind
                                        h₁ hpx)
                match h₂ with
                | ⟨x, hx⟩ => ⟨x, fun hpx => absurd hpx hx⟩)

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
  (fun ⟨x, hrp⟩ hr => Exists.intro x (hrp hr))
  (fun h => if hr : r then let ⟨x, hh⟩ := h hr; Exists.intro x (fun _ => hh)
           else Exists.intro a (fun hr' => absurd hr' hr))

end existential_quantifiers
