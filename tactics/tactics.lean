
-- Using tactics

-- `intro` introduces hypotheses
-- `apply` tries to match the current goal against the conclusion its argument's type

example :
    ∀ a b : Prop, a → b → a :=
by
  intro a
  intro b
  intro ha
  intro hb
  apply ha

example :
    ∀ a b : Prop, a → b → a :=
by
  intro a b ha hb
  apply ha

-- Without using ∀ notation
-- `exact`

example (a b : Prop) : a → b → a := by
  intro ha hb
  exact ha

-- `assumption` tries to match the goal with the hypotheses at hand starting from the most recent one

example (a b : Prop) : a → b → a := by
  intro ha hb
  assumption

-- Chaining... hypothesis for a → b takes hypothesis for a, and gives hypothesis for b

example (a b : Prop) : (a → b) → a → b := by
  intro hab ha
  exact hab ha

-- `have` adds hypothesis to the local context of the main goal
-- `let` adds definitions to the local context of the main goal

example (a b c : Prop) : (a → b) → (b → c) → (a → c) := by
  intro hab hbc ha
  have  hb : b := hab ha
  exact hbc hb

-- Proving propositions involving conjunctions
-- `And.intro` takes two arguments of type a and b, then constructs hypothesis of a ∧ b

example (a b : Prop) : a → b → a ∧ b := by
  intro ha hb
  exact And.intro ha hb

-- `And.left` takes hypothesis of a ∧ b, then gives hypothesis for a
-- Similarly for `And.right`

example (a b : Prop) : a ∧ b → a := by
  intro hab
  exact And.left hab

example (a b : Prop) : a ∧ b → b ∧ a := by
  intro hab
  have ha : a := And.left  hab
  have hb : b := And.right hab
  exact And.intro hb ha

-- More succinctly,... bypassing local definitions

example (a b : Prop) : a ∧ b → b ∧ a := by
  intro hab
  exact And.intro (And.right hab) (And.left hab)

-- More succinctly,... using <·>

example (a b : Prop) : a ∧ b → b ∧ a := by
  intro hab
  exact ⟨And.right hab, And.left  hab⟩
