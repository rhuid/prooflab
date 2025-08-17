/-

++++++++++++++++++++
| Term mode proofs |
++++++++++++++++++++

We are calling them term mode proofs as these proof styles employ lambda terms directly,
that is, we construct a function (lambda term) as a proof.
Some keywords are `show`, etc.

Term mode proofs are more direct and concise at the cost of less interactive tactic-ky feedback.

-/

section

variable (a b c : Prop)

example : a ∧ b → b ∧ a :=
  fun hab : a ∧ b =>
  have ha : a := And.left hab
  have hb : b := And.right hab
  show b ∧ a from And.intro hb ha

-- using pattern matching and constructor
theorem and_comm' : a ∧ b → b ∧ a :=
  fun ⟨ha, hb⟩ => ⟨hb, ha⟩

example : (a → b) → a → b :=
  fun hab ha => hab ha

example : (a → b) → (b → c) → (a → c) :=
  fun hab hbc ha => hbc (hab ha)

example : a → a ∨ b :=
  fun ha => Or.inl ha

example : (a ∧ b) ∧ c → a ∧ (b ∧ c) :=
  fun habc =>
  have ha : a := And.left (And.left habc)
  have hb : b := And.right (And.left habc)
  have hc : c := And.right habc
  ⟨ha, ⟨hb, hc⟩⟩

-- The above can be written so concisely using pattern matching and type inference as follows
theorem and_assoc' : (a ∧ b) ∧ c → a ∧ (b ∧ c) :=
  fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, ⟨hb, hc⟩⟩

-- `cases` won't work, use `match` instead for pattern matching
example : (a → c) ∧ (b → c) → a ∨ b → c :=
  fun hacbc hab =>
  match hab with
  | Or.inl ha => And.left hacbc ha
  | Or.inr hb => And.right hacbc hb

-- `.elim` (eliminator) can also be used instead of `match`
-- Distributivity: ∧ distributes over ∨
theorem and_or_dist' : a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c) :=
  fun habc =>
  have ha : a := habc.left         -- `habc.left` is the same as `And.left habc`
  have hbc : b ∨ c := habc.right
  Or.elim hbc
    (fun hb => Or.inl ⟨ha, hb⟩)
    (fun hc => Or.inr ⟨ha, hc⟩)

end

/-

Tactic mode vs. Term mode

`intro`         `fun`
`have`          `have`
`exact`         `show` `from`
`cases`         `match` or `.elim`

-/
