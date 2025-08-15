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

-- example (a b : Prop) : a ∧ b → b ∧ a := by ac_rfl
