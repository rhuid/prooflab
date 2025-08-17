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

-- Proving existential propositions
-- `Exists.intro` constructs, `Exists.elim` deconstructs

theorem greater_than_zero : ∃ x : Nat, x > 0 :=
  Exists.intro 5 (by decide)

example : ∃ x : Nat, (x > 0) ∧ (x % 2 == 0) :=
  Exists.intro 4 ⟨(by decide), (by rfl)⟩

example (ha : a) : ∃ x : Prop, x ∧ a :=
  Exists.intro (∃ x : Nat, x > 0) ⟨greater_than_zero, ha⟩

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
  exists a b
  exact ⟨hpa, hqb⟩

end

/-

Tactic mode vs. Term mode

`intro`         `fun`
`have`          `have`
`exact`         `show` `from`
`cases`         `match` or `.elim`

-/
