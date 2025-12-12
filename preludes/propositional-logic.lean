/- Exercises from the book: Theorem Proving in Lean 4 -/

/- Some propositional logic -/

section propositional_logic

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

variable (A B : Prop)

-- Resolution rule
example : (p ∨ A) ∧ (¬p ∨ B) → A ∨ B :=
  fun ⟨ha, hb⟩ =>
  match ha with
  | Or.inl hp =>
    match hb with
    | Or.inl hnp => absurd hp hnp
    | Or.inr h   => Or.inr h
  | Or.inr h  => Or.inl h

end propositional_logic

----------------------------------------------------------------------------
-- Some new experiments

section inductive_case_constructor

-- `cases' and `constructor' for elements of inductive data type
-- destructor and constructor

example : p ∧ q → q ∧ p := by
  intro hpq
  cases hpq with
  | intro hp hq => constructor ; exact hq ; exact hp                  -- exact ⟨hq, hp⟩

example (P Q : Nat → Prop) : (∃ x, P x) → ∃ x, P x ∨ Q x := by
  intro h
  cases h with
  | intro n px => constructor ; exact Or.inl px                       -- exact Exists.intro n (Or.inl px)

example (P Q : Nat → Prop) : (∃ x, P x ∧ Q x) → ∃ x, Q x ∧ P x := by
  intro h
  cases h with
  | intro k hpq =>
    cases hpq with
    | intro hp hq => constructor ; apply And.intro ; exact hq ; exact hp    -- exact Exists.intro k ⟨hq, hp⟩

-- these tactics can be used on data just as well as propositions
-- define functions which swap components of the product and sum types

def swap_pair' (α β : Type) : α × β → β × α := by
  intro p
  cases p with
  | mk pa pb => constructor <;> assumption

def swap_pair : α × β → β × α :=
  fun (pa, pb) => (pb, pa)

def swap_sum' (α β : Type) : Sum α β → Sum β α := by
  intro p
  cases p
  { apply Sum.inr ; assumption }
  { apply Sum.inl ; assumption }

def swap_sum'' (α β : Type) : Sum α β → Sum β α := by
  intro p
  cases p with
  | inl a => exact Sum.inr a
  | inr b => exact Sum.inl b

def swap_sum : Sum α β → Sum β α :=
  fun p =>
  match p with
  | Sum.inl a => Sum.inr a
  | Sum.inr b => Sum.inl b

end inductive_case_constructor

----------------------------------------------------------------------------
-- About automation, repeat, try, all_goals, etc.

section automation

example : p → q → r → p ∧ q ∧ r := by
  intros
  constructor
  assumption
  constructor
  repeat assumption

example : p → q → r → p ∧ q ∧ r := by
  try intros
  constructor
  any_goals constructor
  repeat assumption

example : p → q → r → p ∧ q ∧ r := by
  try intros
  repeat any_goals constructor
  repeat assumption

example : r → p ∨ q ∨ r := by
  intros
  repeat right
  assumption

variable (a k : Nat) (f : Nat → Nat)

example (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂, h₁]

-- by default, rw uses the equation in the forward direction but the left arrow
-- can be used to specify backward direction

example (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
  rw [←h₁, h₂]

example (a b c : Nat) : a + b + c = a + c + b := by
  rw [Nat.add_assoc, ←Nat.add_comm c, Nat.add_assoc]

-- by default, rw rewrites the goal but can be instructed to rewrite the hypothesis

example (h : a + 0 = 0) : f a = f 0 := by
  rw [Nat.add_zero] at h
  rw [h]

-- rw tactic is not restricted to propositions

def Tuple (α : Type) (n : Nat) :=
  { as : List α // as.length = n }

example (n : Nat) (h : n = 0) (t : Tuple α n) : Tuple α 0 := by
  rw [h] at t
  exact t

-- simp
-- extensible tactics

end automation



-- ** Tactic combinators
-- + ~tac_1 <;> tac_2~
--   + applies ~tac_1~ on current goal and then applies ~tac_2~ on all subgoals.
-- + ~try tac~
--   + tries ~tac~ (it never fails even when the tactic fails).
-- + ~repeat tac~
--   + repeatedly applies ~tac~ so long as it succeeds.
-- + ~repeat' tac~
--   + is like ~repeat tac~ but recursive.
-- + ~any_goals tac~
--   + applies ~tac~ to every goal and fails only when it fails on all goals.
-- + ~all_goals tac~
--   + is like ~any_goals tac~ but fails when ~tac~ fails on at least one goal.

-- #+REVEAL: split

-- #+BEGIN_SRC lean4
--   example : p → q → r → p ∧ q ∧ r := by
--     intros
--     constructor
--     assumption
--     constructor
--     repeat assumption

--   example : p → q → r → p ∧ q ∧ r := by
--     try intros
--     constructor
--     any_goals constructor
--     repeat assumption

--   example : p → q → r → p ∧ q ∧ r := by
--     try intros
--     repeat any_goals constructor
--     repeat assumption

--   example : p → q → r → p ∧ q ∧ r := by
--     intros
--     repeat' apply And.intro
--     all_goals assumption
-- #+END_SRC
