/-
  Monads
-/

-- to get first, third, fifth element...
def _firstThirdFifth (xs : List α) : Option (α × α × α) := -- to return a tuple
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth => (first, third, fifth)

-- #eval _firstThirdFifth [3, 4, 5, 8]
-- #eval _firstThirdFifth [3, 4, 1, 3, 5, 8]

-- observe: the above could go quite long and may clutter
-- solution: use a helper to take care of propagating none values
def _bind (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x

-- then rewrite our earlier long function..
def _firstThirdFifth' (xs : List α) : Option (α × α × α) :=
  _bind xs[0]? fun first =>           -- early exit, return none if xs[0] is none, otherwise chain...
  _bind xs[2]? fun third =>           -- chaining
  _bind xs[4]? fun fifth =>
  some (first, third, fifth)          -- final return

infix:55 " ~~> " => _bind

-- rewriting the same function using the infix operator
def _firstThirdFifthSeventhNinth (xs : List α) : Option (α × α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  xs[8]? ~~> fun ninth =>
  some (first, third, fifth, seventh, ninth)

-- #eval _firstThirdFifthSeventhNinth [3, 4, 1, 3, 5, 8, 3, 2]
-- #eval _firstThirdFifthSeventhNinth [3, 4, 1, 3, 5, 8, 3, 2, 1]

inductive _Option (α : Type) where
| none
| some : α → _Option α

-- Using the monad typeclass
-- Monad instance for Option can be created as...
instance : Monad _Option where
pure x := _Option.some x
bind opt next :=
  match opt with
  | _Option.none => _Option.none
  | _Option.some x => next x

-- the previous function rewritten using Monad
def _firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

#eval _firstThirdFifthSeventh (fun xs i => xs[i]?) [7, 8, 12, 4, 3, 10, 1]

/-

There is a contract that each instance of Monad should obey.

* `pure` should be a left identity of `bind`, that is, `bind (pure v) f` should be the same as `f v`.
* `pure` should be a right identity of `bind`, so `bind v pure` is the same as `v`
* `bind` should be associative, that is, `bind (bind v f) g` is the same as `bind v (λ x => bind (f x) g)`

-/

-- do-notation
def _firstThirdFifthSeventh' [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) := do
  let first   ← lookup xs 0
  let third   ← lookup xs 2
  let fifth   ← lookup xs 4
  let seventh ← lookup xs 6
  return (first, third, fifth, seventh)

-- can make it even more succinct
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) := do
  pure (← lookup xs 0, ← lookup xs 2, ← lookup xs 4, ← lookup xs 6)

-- #eval firstThirdFifthSeventh (λ xs i => xs[i]?) [7, 8, 12, 4, 3, 10, 1]

-- custom monad
class Monad' (m : Type → Type) where   -- adding this {α β : Type} causes type mismatch
pure : α → m α
bind : m α → (α → m β) → m β

class LawfulMonad' (m : Type → Type) extends Monad' m where
pure_bind (a : α) (f : α → m β) :
  bind (pure a) f = f a
bind_pure (ma : m α) :
  bind ma (pure) = ma
bind_assoc (f : α → m β) (g : β → m γ) (ma : m α) :
  bind (bind ma f) g = bind ma (fun a => bind (f a) g)

-- Showing that Option' is a monad
inductive Option' (α : Type) : Type
| none : Option' α
| some : (k : α) → Option' α

def Option'.pure : α → Option' α := Option'.some

def Option'.bind : Option' α → (f : α → Option' β) → Option' β
| none, _ => none
| some k, f => f k

instance Option'.LawfulMonad' : LawfulMonad' Option' := {
pure := Option'.pure
bind := Option'.bind
pure_bind := by
  intro α β a f
  rfl
bind_pure := by
  intro α ma
  cases ma with
  | none   => rfl
  | some _ => rfl
bind_assoc := by
  intro α β γ f g ma
  cases ma <;> rfl
}




  -- cases ma with
  -- | none   => rfl
  -- | some _ => rfl




























-- -- Set as a function type (α to Prop)
def Set (α : Type) := α → Prop

-- -- Set membership notation
def Set.mem (a : α) (s : Set α) : Prop := s a
notation:50 a " ∈ " s => Set.mem a s

-- -- Define pure and bind operations
def Set.pure (a : α) : Set α := fun x => x = a
def Set.bind (s : Set α) (f : α → Set β) : Set β := fun b => ∃ a, a ∈ s ∧ b ∈ f a
