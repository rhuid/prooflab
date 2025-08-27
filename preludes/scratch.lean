
/-
 Chapter 5: Inductive, structure, typeclasses
-/

section

class Inhabited' (α : Type) where
  default : α

instance : Inhabited' Nat :=
  { default := 5 }

#eval (Inhabited'.default : Nat)

end

inductive Tree (α : Type)
| nil  : Tree α
| node : α → Tree α → Tree α → Tree α

def mirror {α : Type} : Tree α → Tree α
| Tree.nil        => Tree.nil
| Tree.node a l r => Tree.node a (mirror r) (mirror l)

-- induction vs. cases
-- using induction because we need induction hypothesis

example {α : Type} (t : Tree α) :
  mirror (mirror t) = t :=
by
  induction t with
  | nil => rfl
  | node a l r ih_l ih_r => simp [mirror]
                            simp [ih_l, ih_r]

-- the following can be done in cases

example {α : Type} :
  ∀ t : Tree α, mirror t = Tree.nil ↔ t = Tree.nil :=
by
  intro t
  induction t with
  | nil                  => simp [mirror]
  | node a l r ih_l ih_r => simp [mirror]

example {α : Type} :
  ∀ t : Tree α, mirror t = Tree.nil ↔ t = Tree.nil :=
by
  intro t
  cases t with
  | nil  => simp [mirror]
  | node => simp [mirror]






-- opaque Even' : Nat → Prop
-- axiom Even'.zero : Even' 0
-- axiom Even'.next : ∀ n : Nat, Even' n → Even' (n + 2)

inductive Even : Nat → Prop
| zero : Even 0
| next : ∀ n : Nat, Even n → Even (n + 2)

-- example : Even 4 :=
--   have even_0 : Even 0 := Even.zero
--   have even_2 : Even 2 := Even.next _ even_0
--   show Even 4 from Even.next _ even_2

-- -- Reflexive-transitive closure

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop
| base  : ∀ a b : α, R a b → Star R a b
| refl  : ∀ a : α, Star R a b
| trans : ∀ a b c : α, Star R a b → Star R b c → Star R a c
-- example {α : Type} (R : α → α → Prop) (a b : α) :

--   Star (Star R) a b ↔ Star R a b :=
-- by
--   apply Iff.intro
--   . intro h
--     induction h with
--     | base a b hab => exact hab
--     | refl a       => apply Star.refl
--     | trans a b c hab hbc ihab ihbc =>
--       apply Star.trans a b
--       . exact ihab
--       . exact ihbc
--   . intro h
--     apply Star.base
--     exact






-- {́α : Type}

-- Proof that Star is the least

theorem temp {α : Type} {R : α → α → Prop} {S : α → α → Prop}
  (hr : ∀ a b, R a b → S a b)
  (hrefl : ∀ a, S a a)
  (htrans : ∀ a b c, S a b → S b c → S a c) :
  ∀ a b, Star R a b → S a b :=
by
  intro a b h
  induction h with
  | base _ _ hrab => exact hr _ _ hrab
