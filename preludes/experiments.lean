example : p ∧ q ∧ r → p ∨ q ∨ r := by
  try intro h
  try intro
  try constructor
  try apply And.right h
  try apply And.left h

example : p ∧ q ∧ r → p ∨ q ∨ r := by
  intro h
  repeat
  first
  | cases h
  | cases h_snd
  | cases h_fst
  try
  first
  | left; assumption
  | right; left; assumption
  | right; right; assumption

-- syntax "triv" : tactic

-- macro_rules
-- | `(tactic| triv) => `(tactic| assumption)

-- example (h : p) : p := by
--   triv

-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

-- You cannot prove the following theorem using `triv`
-- example (x : α) : x = x := by
--  triv

-- Let's extend `triv`. The tactic interpreter
-- tries all possible macro extensions for `triv` until one succeeds
macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

-- We now add a (recursive) extension
macro_rules | `(tactic| triv) => `(tactic| apply And.intro <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv

example : p → q → r → p ∧ q ∧ r := by
  intros
  repeat' apply And.intro
  all_goals assumption

def divide (x y : Nat) (_ : y ≠ 0) : Nat := x / y

def head {α : Type} {n : Nat} : Vector α (n + 1) → α
| ⟨data, h⟩ => data[0]

#print Vector

-- Type of the function already guarantees correctness
-- Impossible cases are removed by logical reasoning
-- No runtime errors

inductive NonEmptyList (α : Type) where
| mk : (xs : List α) → xs ≠ [] → NonEmptyList α

def NonEmptyList.head {α} : NonEmptyList α → α
| .mk (x :: _) _ => x
| .mk [] h => (h rfl).elim

#print False.elim


-- | ⟨[], _⟩ => by cases n
-- | ⟨x :: _,_⟩ => x
