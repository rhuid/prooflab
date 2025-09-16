/-
  Modelling non-determinism using a custom Set monad.

  Here, we build a monad Set from scratch, define set operations, prove that Set is a monad.
-/

-- Set as a function type
def Set (α : Type) := α → Prop

-- Set membership
def Set.mem (a : α) (s : Set α) : Prop := s a
notation:50 a " ∈ " s => Set.mem a s

-- Empty set
def Set.empty : Set α := fun _ => False

-- Set union and intersection
def Set.union        (s t : Set α) : Set α := fun x => (x ∈ s) ∨ (x ∈ t)
def Set.intersection (s t : Set α) : Set α := fun x => (x ∈ s) ∧ (x ∈ t)
notation:50 s " ∪ " t => Set.union s t
notation:50 s " ∩ " t => Set.intersection s t

-- Set complement
def Set.complement (s : Set α) : Set α := fun x => ¬ (x ∈ s)

-- Examples
-- {2, 3, 5, 7}
def primesLessThanTen : Set Nat := fun x => (x = 2) ∨ (x = 3) ∨ (x = 5) ∨ (x = 7)

-- {1}
def one : Set Nat := fun x => x = 1

-- {2, 3, 5, 7} intersection {1}
def ourIntersection := primesLessThanTen ∩ one

-- Let's build the monad
-- Converts an element into a singleton set
def Set.pure (a : α) : Set α := fun x => x = a

-- Combines all possibilities from s and applies f to each
def Set.bind (s : Set α) (f : α → Set β) : Set β :=
fun b => ∃ a, (a ∈ s) ∧ (b ∈ f a)

instance Set.Monad : Monad Set where
pure := Set.pure
bind := Set.bind

-- Set extensibility (two sets are equal if they contain the same elements)
theorem Set.ext {s t : Set α} (h : ∀ x, (x ∈ s) ↔ (x ∈ t)) : s = t := by
  funext x
  apply propext
  exact h x

-- Monad laws proofs
theorem Set.pure_bind (a : α) (f : α → Set β) : bind (pure a) f = f a := by
  apply Set.ext
  intro b
  simp [pure, Set.pure, bind, Set.bind, Set.mem]

theorem Set.bind_pure (s : Set α) : Set.bind s Set.pure = s := by
  apply Set.ext
  intro a
  simp [pure, Set.pure, bind, Set.bind, Set.mem]

theorem Set.bind_assoc (s : Set α) (f : α → Set β) (g : β → Set γ) :
    bind (bind s f) g = bind s (fun x => bind (f x) g) := by
  apply Set.ext
  intro c
  simp [bind, Set.bind, Set.mem]
  apply Iff.intro
  . intro h
    cases h with
    | intro b hb =>
      cases hb with
      | intro inner hgbc =>
        cases inner with
        | intro a ha =>
          cases ha with
          | intro hsa hfab =>
            exists a
            apply And.intro
            . exact hsa
            . exact Exists.intro b ⟨hfab, hgbc⟩
  . intro h
    cases h with
    | intro a ha =>
      cases ha with
      | intro hsa he =>
        cases he with
        | intro b hb =>
          cases hb with
          | intro hfab hgbc =>
            apply Exists.intro b
            apply And.intro
            . exists a
            . exact hgbc
