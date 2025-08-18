
/-

++++++++++++++++++++++
| Structural tactics |
++++++++++++++++++++++

We are calling them structural because these tactics look at the structure of the proposition
and use constructors and destructors (another informal term?) to prove goals.
Some common tactics are `intro`, `apply`, `exact`, `assumption`, etc.

-/

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

-- Even more succinctly,... using <·>

example (a b : Prop) : a ∧ b → b ∧ a := by
  intro hab
  exact ⟨And.right hab, And.left  hab⟩

-- Proving propositions involving disjunctions
-- `Or.inl` and `Or.inr` give hypotheses for a ∨ b from hypotheses for a and b respectively

example (a b : Prop) : a → a ∨ b := by
  intro ha
  exact Or.inl ha

-- `left` and `right` can also be used to prove left and right sides of the disjunction
-- For instance, the same proof above may be rewritten as

example (a b : Prop) : a → a ∨ b := by
  intro ha
  left
  exact ha

-- `cases` may be used to perform case analysis on disjunction

example (a b : Prop) : a ∨ b → b ∨ a := by
  intro hab
  cases hab with
    | inl ha => exact Or.inr ha
    | inr hb => exact Or.inl hb

-- Proving associativity (for conjunction)

example (a b c : Prop) : (a ∧ b) ∧ c → a ∧ (b ∧ c) := by
  intro habc
  have ha : a := And.left (And.left habc)
  have hb : b := And.right (And.left habc)
  have hc : c := And.right habc
  exact And.intro ha (And.intro hb hc)

-- Proving associativity (for disjunction)

example (a b c : Prop) : (a ∨ b) ∨ c → a ∨ (b ∨ c) := by
  intro habc
  cases habc with
  | inl hab =>
    cases hab with
    | inl ha => exact Or.inl ha
    | inr hb => exact Or.inr (Or.inl hb)
  | inr hc => exact Or.inr (Or.inr hc)

-- Proving the distributive law

example (a b c : Prop) : a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c) := by
  intro habc
  have ha : a := And.left habc
  have hbc : b ∨ c := And.right habc
  cases hbc with
    | inl hleft =>
      left
      exact And.intro ha hleft
    | inr hright =>
      right
      exact And.intro ha hright

example (a b c : Prop) : (a ∧ b) ∨ (a ∧ c) → a ∧ (b ∨ c) := by
  intro habac
  cases habac with
    | inl hab =>
      have ha : a := And.left hab
      have hb : b := And.right hab
      exact And.intro ha (Or.inl hb)
    | inr hac =>
      have ha : a := And.left hac
      have hc : c := And.right hac
      exact And.intro ha (Or.inr hc)

-- Proving (a → b) ∧ (a → c) → a → b ∧ c

example (a b c : Prop) : (a → b) ∧ (a → c) → a → b ∧ c := by
  intro habac ha
  have hb : b := And.left habac ha
  have hc : c := And.right habac ha
  exact ⟨hb, hc⟩

-- Proving (a → c) ∧ (b → c) → a ∨ b → c

example (a b c : Prop) : (a → c) ∧ (b → c) → a ∨ b → c := by
  intro hacbc hab
  cases hab with
    | inl ha => exact And.left hacbc ha
    | inr hb => exact And.right hacbc hb

-- Proving ((a → b) → a) → a
-- The proof involves the law of the excluded middle
-- Classic logic is used as constructive mathematics is unable to do the proof
-- `Classical.em` allows using the law of the excluded middle

open Classical in
example (a b : Prop) : ((a → b) → a) → a := by
  intro h
  cases em a with
    | inl ha  =>
      exact ha
    | inr hna =>
      apply h
      intro ha
      contradiction

-- The same above proof may be rewritten using `by_cases`

open Classical in
example (a b : Prop) : ((a → b) → a) → a := by
  intro h
  by_cases ha : a
  case pos => exact ha
  case neg =>
    apply h
    intro ha'
    contradiction

-- The same proof may be rewritten more succinctly using dot (.) syntax
-- The dot (.) marks each case branch

open Classical in
example (a b : Prop) : ((a → b) → a) → a := by
  intro h
  by_cases ha : a
  . exact ha
  . apply h
    intro ha'
    contradiction

-- Proving existential propositions
-- `Exists.intro` constructs, `Exists.elim` deconstructs

-- Swapping existentials
example (α : Type) (p q : α → Prop) :
    (∃ x, p x ∧ q x) → (∃ x, q x ∧ p x) :=
by
  intro h
  apply Exists.elim h
  intro a hpaqa
  apply Exists.intro a
  exact ⟨hpaqa.right, hpaqa.left⟩

-- From ∃ to ∀
example (α : Type) (p : α → Prop) :
    (∃ x, p x) → ¬ (∀ x, ¬ p x) :=
by
  intro hpₑ hpₐ
  apply Exists.elim hpₑ
  intro a hpx
  have hpx' := hpₐ a             -- apply the universal here
  contradiction

-- Combining existentials
example (α : Type) (p q : α → Prop) :
    (∃ x, p x) → (∃ x, q x) → ∃ x y, p x ∧ q y :=
by
  intro hp hq
  apply Exists.elim hp
  intro a hpa
  apply Exists.elim hq
  intro b hqb
  apply Exists.intro a
  apply Exists.intro b
  exact ⟨hpa, hqb⟩

-- Proofs by induction

section

-- First let's build natural numbers

inductive Natural where
| zero
| succ : Natural → Natural

-- Addition for natural numbers using recursion

def Natural.add : Natural → Natural → Natural
| zero,   n => n
| succ k, n => succ (Natural.add k n)

-- An infix (non-associative) operator for our addition

infix:55 " + " => Natural.add

-- Some preliminary proofs (we will need them later)

theorem Natural.zero_add (n : Natural) : Natural.zero + n = n := by rfl

theorem Natural.add_zero (n : Natural) : n + Natural.zero = n := by
  induction n with
  | zero      => rfl
  | succ k ih => simp [Natural.add, ih]

-- Proving our addition is commutative

theorem Natural.add_comm (m n : Natural) : m + n = n + m := by
  induction m with
  | zero      => simp [Natural.zero_add, Natural.add_zero]
  | succ k ih =>
    simp [Natural.add]
    rfl

-- simp [Natural.add]




-- #eval Natural.succ .zero + Natural.succ .zero
-- #eval Natural.succ (.succ .zero)

end


-- example (n : Nat) :
--     add 0 n = n :=
-- by
--   induction n with
--   | zero => rfl
--   | succ k' ih => simp [add, ih]

-- need tweaks on the induction

-- Let's do more later...
