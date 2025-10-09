/- Exercises from the book: Theorem Proving in Lean 4 -/

/- Some propositional logic -/

variable (p q r s : Prop)

example : (p → q → r) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun hpqr hpq => hpqr hpq.1 hpq.2)
    (fun hpqr hp hq => hpqr ⟨hp, hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun hpqr => And.intro
                (fun hp => hpqr (Or.inl hp))
                (fun hq => hpqr (Or.inr hq)))
    (fun hprqr => (fun hpq => Or.elim hpq hprqr.1 hprqr.2))

-- This kind of De Morgan's law is provable in intuitionistic logic
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun hpq => ⟨fun hp => hpq (Or.inl hp), fun hq => hpq (Or.inr hq)⟩)
    (fun hpq h => Or.elim h hpq.1 hpq.2)

-- One half of the other De Morgan's law is also provable in intuitionistic logic
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun hpq h => match hpq with
              | Or.inl hp => hp h.1
              | Or.inr hq => hq h.2

-- The remaining De Morgan's law requires classical logic (see Classical part)

example : ¬(p ∧ ¬p) :=
  fun h => absurd h.1 h.2

example : p ∧ ¬q → ¬(p → q) :=
  fun h₁ h₂ => absurd (h₂ h₁.1) h₁.2

-- Note: absurd proves anything from a proof of p and ¬p (in this order)
-- Because from p and ¬p, you get False and from False, you get anything

example : ¬p → (p → q) :=
  fun h₁ h₂ => absurd h₂ h₁

example : ¬p ∨ q → (p → q) :=
  fun h hp => match h with
             | Or.inl hnp => absurd hp hnp
             | Or.inr hq  => hq

-- later (requires classical?) example : (p → q) → ¬p ∨ q :=

-- Iff.mp and Iff.mpr return the forward and backward direction proofs
example : ¬(p ↔ ¬p) :=
  fun h => have hnp : ¬p := fun hp => (Iff.mp h hp) hp
          hnp (Iff.mpr h hnp)

-- Contrapositive? (the other direction is not provable in intuitionistic logic)
example : (p → q) → (¬q → ¬p) :=
  fun h hnq hp => hnq (h hp)

-- The following require classical logic

open Classical

example : ¬(p ∧ ¬q) → (p → q) := by
  intro h hp
  apply Or.elim (em q)
  { intro hq; exact hq }
  { intro hnq;
    have cont := h ⟨hp, hnq⟩
    contradiction }

-- Same as above but without using by tactic (note: contradiction vs. absurd)
example : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp =>
  Or.elim (em q)
  (fun hq  :  q => hq)
  (fun hnq : ¬q => absurd ⟨hp, hnq⟩ h)

-- this one is quite long (a shorter one is given below using `if else` construct)
example : (p → r ∨ s) → (p → r) ∨ (p → s) := by
  intro h
  apply Or.elim (em p)
  { intro hp
    have hrs := h hp
    apply Or.elim hrs
    { intro hr
      exact Or.inl (fun _ => hr) }
    { intro hs
      exact Or.inr (fun _ => hs) } }
  { intro hnp
    apply Or.elim (em r)
    { intro hr
      exact Or.inl (fun _ => hr) }
    { intro hnr
      apply Or.elim (em s)
      { intro hs
        exact Or.inr (fun _ => hs) }
      { intro hns
        apply Or.inr
        intro hp
        contradiction }}}

-- using if else automatically activates Classical.em
example : (p → r ∨ s) → (p → r) ∨ (p → s) :=
  fun h =>
  if hr : r then Or.inl (fun _ => hr)
  else if hs : s then Or.inr (fun _ => hs)
  else have hnp : ¬p := fun hp =>
    match h hp with
    | Or.inl hr' => hr hr'
    | Or.inr hs' => hs hs'
  Or.inr (fun hp => byContradiction (fun _ => hnp hp))

-- Pierce's law
example : ((p → q) → p) → p :=
  fun h =>
  if hp : p then hp
  else let hpq : p → q := fun hp' => absurd hp' hp
  h hpq

example : (¬q → ¬p) → (p → q) :=
  fun h hp =>
  if hq : q then hq
  else let hnp : ¬p := h hq
  absurd hp hnp

example : (p ∨ ¬p) :=
  if hp : p then Or.inl hp else Or.inr hp

example : (p → q) → (¬p ∨ q) :=
  fun h => if hp : p then Or.inr (h hp) else Or.inl hp

-- another long tactic proof again (see below for term mode proof)
example : ¬(p → q) → p ∧ ¬q := by
  intro h
  apply Or.elim (em p)
  { intro hp
    apply Or.elim (em q)
    { intro hq
      have hpq : p → q := fun _ => hq
      have hh := h hpq
      contradiction }
    { intro hnq
      exact ⟨hp, hnq⟩ }}
  { intro hnp
    apply Or.elim (em q)
    { intro hq
      have hpq : p → q := fun _ => hq
      have hh := h hpq
      contradiction }
    { intro hnq
      have hpq : p → q := fun hp => absurd hp hnp
      have hh := h hpq
      contradiction }}

-- same as above (but using `if else` and shorter)
example : ¬(p → q) → p ∧ ¬q :=
  fun h =>
  if hp : p then
    if hq : q then
      have hpq : p → q := fun _ => hq
      absurd hpq h
    else ⟨hp, hq⟩
  else if hq : q then
         have hpq : p → q := fun _ => hq
         absurd hpq h
       else
         have hpq : p → q := fun h' => absurd h' hp
         absurd hpq h

-- The part of De Morgan's law which is not provable in intuitionistic logic
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h =>
  if hp : p then
    if hq : q then
      absurd ⟨hp, hq⟩ h
    else Or.inr hq
  else Or.inl hp
