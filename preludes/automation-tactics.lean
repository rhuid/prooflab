/-

++++++++++++++++++++++
| Automation tactics |
++++++++++++++++++++++

We are calling them automation because these tactics try to use Lean library or custom lemmas or results
to simplify or rewrite or even build the proof instead of doing it manually.
Some common tactics are `rfl`, `simp`, `rw`, etc.

-/

-- `rfl` (reflexivity) tries to close the goal by using definitional equality (or uses reduction)

example : 4 + 8 = 12 := by rfl               -- uses the definition of addition

example : (fun _ => a) b = a := by rfl       -- uses β-reduction

example : (λ x : Nat => x + 7) 0 = 7 := by rfl

def _natToString : Nat → String
  | 4 => "four"
  | _ => "something else"

example : _natToString (2 + 2) = "four" := by rfl

-- `ac_rfl` is just like `rfl` but uses reordering and rearraging (commutativity and associativity)

example (a b : Nat) : a + b = b + a := by ac_rfl

-- `simp` simplifies both sides of the equation using known lemmas

example (α : Type) (xs : List α) : List.reverse (List.reverse xs) = xs := by simp

-- `rw` rewrites the goals using lemmas and results which are munaully given

example (a b c : Nat) (h : a = b) : a + c = b + c := by rw [h]

example (a b c d : Nat) (hab : a = b) (hbc : b = c) (hcd : c = d) :
    a = d :=
by
  rw [hab]
  rw [hbc]
  exact hcd

-- The same proof above can written more concisely (by combining multible rw) as

example (a b c d : Nat) (hab : a = b) (hbc : b = c) (hcd : c = d) :
    a = d :=
by
  rw [hab, hbc, hcd]

namespace TempSpace

opaque m : Nat
opaque n : Nat
opaque k : Nat

axiom mn_equal : m = n

@[simp]
theorem nk_equation : n = k + 2 := by sorry

example : m + 2 = k + 4 := by simp [mn_equal]

example : m + 2 = k + 4 := by rw [mn_equal, nk_equation]

end TempSpace



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

theorem Natural.add_succ (m n : Natural) : m + succ n = succ (m + n) := by
induction m with
| zero      => simp [Natural.zero_add]
| succ k ih => simp [Natural.add, ih]

-- #eval Natural.succ .zero + Natural.succ .zero
-- #eval Natural.succ (.succ .zero)

-- Proving our addition is commutative

theorem Natural.add_comm (m n : Natural) : Natural.add m n = Natural.add n m := by
induction m with
| zero      => simp [Natural.zero_add, Natural.add_zero]
| succ k ih => simp [Natural.add, Natural.add_succ, ih]

-- Proving our addition is associative

example (m n k : Natural) : (m + n) + k = m + (n + k) := by
induction k with
| zero       => simp [Natural.add, Natural.add_zero]
| succ k' ih => simp [Natural.add_succ, ih]

-- Induction using pattern matching and recursion

theorem Natural.add_assoc : ∀ m n k : Natural, (m + n) + k = m + (n + k)
| _, _, .zero    => by simp [Natural.add, Natural.add_zero]
| _, _, .succ k' => by simp [Natural.add_succ, Natural.add_assoc _ _ k']

-- succ is unique

example (n : Natural) : n.succ ≠ n := by
  induction n with
  | zero => simp
  | succ k ih => simp [ih]

-- Typeclasses

class IsCommutative' (α : Type) (f : α → α → α) where
  comm : ∀ a b, f a b = f b a

class IsAssociative' (α : Type) (f : α → α → α) where
  assoc : ∀ a b c, f (f a b) c = f a (f b c)

instance : IsCommutative' Natural Natural.add :=
  { comm := Natural.add_comm }

instance : IsAssociative' Natural Natural.add :=
  { assoc := Natural.add_assoc }

end
