/-
Inductive Predicates

These are like indutive types but give propositions. Each constructor gives an introduction rule. Therefore, to prove inductive propositions, we use the constructors. We also eliminate (elimination rule) them using `induction` or `cases`.
-/

-- Defining Even numbers as inductive predicates
-- Each `Even k` for natural number k is a proposition

inductive Even : Nat → Prop
| zero : Even 0
| next : ∀ n : Nat, Even n → Even (n + 2)

-- Let's prove that 0 and 4 are even (straight-forward)

theorem even_zero : Even 0 := Even.zero

theorem even_four : Even 4 := by
  have even_2 : Even 2 := Even.next 0 .zero
  exact .next 2 even_2

-- Let's prove that 5 is not even

theorem not_even_five : ¬Even 5 := by
  intro h
  cases h                                -- some magic?
  contradiction

-- Building some more familiar inductive predicates
-- And'

-- the following doesn't work (why?)
-- inductive And' : Prop → Prop → Prop
-- | intro : ∀ p q : Prop, And' p q

inductive And' (p q : Prop) : Prop
| intro : p → q → And' p q

example : And' (Even 0) (Even 4) := by
  exact And'.intro (even_zero) (even_four)

-- using constructor directly
example : And' (Even 0) (Even 4) := And'.intro (even_zero) (even_four)

-- using shorthand for constructor
example : And' (Even 0) (Even 4) := ⟨even_zero, even_four⟩


-- Or'

inductive Or' : Prop → Prop → Prop
| inl : p → Or' p q
| inr : q → Or' p q

example : Or' (Even 3) (Even 4) := by
  exact Or'.inr even_four


-- Exists'

inductive Exists' {α : Type} (P : α → Prop) : Prop
| intro : (a : α) → P a → Exists' P

example : Exists' Even := by
  apply Exists'.intro 4
  exact even_four


-- Let's do XOR operation

inductive Xor' : Prop → Prop → Prop
| inl : p → ¬q → Xor' p q
| inr : ¬p → q → Xor' p q

example : Xor' (Even 4) (Even 5) := by
  apply Xor'.inl
  exact even_four
  exact not_even_five

example : Xor' (Even 4) (Even 5) := by
  left                                          -- Applies the left constructor
  exact even_four
  exact not_even_five

example : Xor' (Even 4) (Even 5) := Xor'.inl even_four not_even_five

-- using induction/cases
example (p q : Prop) : Xor' p q → (p ∧ ¬q) ∨ (¬p ∧ q) := by
  intro hpq
  induction hpq with
  | inl hp hnq => exact Or.inl ⟨hp, hnq⟩
  | inr hnp hq => exact Or.inr ⟨hnp, hq⟩
