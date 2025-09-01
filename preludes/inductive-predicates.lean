/-
  Inductive Predicates

  These are like indutive types but give propositions. Each constructor gives an introduction rule.
  Therefore, to prove inductive propositions, we use the constructors.
  We also eliminate (elimination rule) them using `induction` or `cases`.
-/

-- Defining Even numbers as inductive predicates
-- Each `Even k` for natural number k is a proposition

inductive Even : Nat → Prop
| zero : Even 0
| next : ∀ n : Nat, Even n → Even (n + 2)

-- #check Even.zero
-- #check Even.next
-- #check Even.next _ Even.zero

-- Let's prove that some numbers are even (straight-forward)

theorem even_zero : Even 0 := Even.zero

example : Even 4 := by
  have even_2 : Even 2 := Even.next 0 .zero
  exact .next 2 even_2

theorem even_four : Even 4 :=
  Even.next _ (Even.next _ Even.zero)

theorem even_six : Even 6 :=
  Even.next _ (Even.next _ (Even.next _ Even.zero))

-- For all natural number n, the number 2*n is even

example : ∀ n : Nat, Even (2 * n) := by
  intro n
  induction n with
  | zero      => exact Even.zero              -- simp [Even.zero] also works
  | succ k ih => exact Even.next _ ih

-- Note: Cannot use 0 or (k + 1) inside induction (above) (why?)

-- Sum of two even numbers is even

theorem even_add : Even n → Even m → Even (n + m) := by
  intro hn hm
  induction hn with
  | zero => simp [Nat.zero_add]; assumption
  | next k hk ih =>
    have : k + 2 + m = (k + m) + 2 := by simp [Nat.add_assoc, Nat.add_comm]
    rw [this]
    exact Even.next _ ih

/-
  Why use inductive predicates over other alternatives?
  * Can prove that 5 is not even
  * Constructors provide a nice way to perform induction or cases

  Note: We cannot use rfl or simp directly on inductive predicates
-/

-- Let's prove that 5 is not even

theorem not_even_five : ¬ Even 5 := by
  intro h
  cases h                                -- some magic?
  contradiction

-- For all natural number n, the number 2*n + 1 is not even

theorem not_even_one : ¬ Even 1 :=
  fun h => by cases h                    -- another magic?

example (n : Nat) : ¬ Even (2 * n + 1) := by
  intro h
  induction n with
  | zero       => contradiction
  | succ k ih =>
    have : (2 * (k + 1) + 1) = (2 * k + 1 + 2) := by rfl
    rw [this] at h
    have : Even (2 * k + 1) := by cases h; simp_all
    contradiction

/-

++++++++++++++++++++++++++++++++++++++++++++++++++
| Experimenting with our own logical connectives |
++++++++++++++++++++++++++++++++++++++++++++++++++

-/

-- And'

inductive And' (p q : Prop) : Prop
| intro : p → q → And' p q

-- #check And'.intro even_zero even_four

example : And' (Even 0) (Even 4) := by
  exact And'.intro (even_zero) (even_four)

example : And' (Even 0) (Even 4) := ⟨even_zero, even_four⟩

-- using constructor directly
example : And' (Even 0) (Even 4) := And'.intro (even_zero) (even_four)

-- using shorthand for constructor
example : And' (Even 0) (Even 4) := ⟨even_zero, even_four⟩

/-
  We already have the introduction rule for And' (given by the constructor)
  Now we want an elimination rule
-/

theorem And'.left : And' p q → p := by
  intro hpq
  cases hpq with
  | intro => assumption                           -- use of unnamed hypotheses

theorem And'.right : And' p q → q := by           -- rewrite this in term mode
  intro hpq
  cases hpq with
  | intro => assumption

-- Now, we can use And'.left and And'.right

example (p q : Prop) : And' p q → And' q p := by
  intro hpq
  have hp : p := And'.left  hpq
  have hq : q := And'.right hpq
  exact And'.intro hq hp


-- Or'... use two constructors (introduction rules)

inductive Or' : Prop → Prop → Prop
| inl : p → Or' p q
| inr : q → Or' p q

example : Or' (Even 3) (Even 4) := by
  exact Or'.inr even_four

-- how about elimination? Use `cases` or `induction`

example : Or' (Even 31) (Even 8) → Even 10 := by       -- but `contradiction` will fail for (Even 33)
  intro h
  cases h with
  | inl hl => contradiction
  | inr hr => exact Even.next _ hr


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
  exact even_four                               -- can use . (dot) or {} (braces)
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


-- the following doesn't work (why?)
-- inductive And' : Prop → Prop → Prop
-- | intro : ∀ p q : Prop, And' p q

/-
  A digression: Using typeclasses to overload operators
-/

-- class AddOp' (α : Type) where
--   and : α → α → α

-- infixl:35 " ∧ " => AndOp'.and

-- instance : AddOp' Prop where
--   and := And'
