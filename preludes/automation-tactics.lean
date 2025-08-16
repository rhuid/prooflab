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
