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

-- Monad laws proofs
-- theorem pure_bind (a : α) (f : α → Set β) :
--     bind (pure a) f = f a := by
--   ext b
--   unfold bind Set.bind pure Set.pure Set.mem
--   constructor
--   · intro ⟨a', ⟨ha', hb⟩⟩
--     rw [ha'] at hb
--     exact hb
--   · intro h
--     exists a
--     constructor <;> assumption

-- theorem bind_pure (s : Set α) : bind s pure = s := by
--   ext x
--   unfold bind Set.bind pure Set.pure Set.mem
--   constructor
--   · intro ⟨a, ha, hx⟩
--     rw [hx] at ha
--     exact ha
--   · intro h
--     exists x
--     constructor <;> assumption

-- theorem bind_assoc (s : Set α) (f : α → Set β) (g : β → Set γ) :
--     bind (bind s f) g = bind s (fun x => bind (f x) g) := by
--   ext c
--   unfold bind Set.bind Set.mem
--   constructor
--   · intro ⟨b, ⟨⟨a, ha, hb⟩, hc⟩⟩
--     exact ⟨a, ha, b, hb, hc⟩
--   · intro ⟨a, ha, b, hb, hc⟩
--     exact ⟨b, ⟨a, ha, hb⟩, hc⟩
