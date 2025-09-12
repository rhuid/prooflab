/- # Program Semantics:
  Operational Semantics
  Axiomatic Semantics (Haore Logic)
  Denotational Semantics -/

/- ## Operational Semantics:
  + Like rules of a game that describe how programs run, step by step
  + A playthrough of the game is the execution trace of a program
  + Like an instruction manual: it doesn't just tell you the end result--it tells you how to get there

### Three key flavors:
  + Big-step semantics (natural semantics)
  + Small-step semantics (structural operational semantics)
  + Abstract machine semantics -/

/- Modelling a small imperative language -/

-- State modelled as a function that takes a variable and gives its current value
def State := String → Nat

-- Grammar for statement
inductive Stmt : Type where
| skip : Stmt
| assign : String → (State → Nat) → Stmt                               -- fun x => s "y" + 1
| seq : Stmt → Stmt → Stmt
| ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
| whileDo : (State → Prop) → Stmt → Stmt

-- Some examples
def smallLoop : Stmt
| Stmt.whileDo (fun s => s "x" > s "y") (Stmt.assign "x" (fun s => s "x" + 2))
