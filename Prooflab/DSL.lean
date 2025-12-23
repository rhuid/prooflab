/-- A variable is encoded as a string -/
abbrev Var := String

/-- State is a total mapping from variables to values -/
def State := Var → Int

def State.update (s : State) (x : Var) (v : Int) : State :=
  fun y => if y = x then v else s y

/-- A type for arithmetic expressions, defined inductively -/
inductive AExp
| const (n : Int)
| var   (x : Var)
| add   (e₁ e₂ : AExp)
| sub   (e₁ e₂ : AExp)
| mul   (e₁ e₂ : AExp)

/-- A function that evaluates arithmetic expressions -/
def AExp.eval : AExp → State → Int
| .const n, _ => n
| .var x, s => s x
| .add e₁ e₂, s => e₁.eval s + e₂.eval s
| .sub e₁ e₂, s => e₁.eval s - e₂.eval s
| .mul e₁ e₂, s => e₁.eval s * e₂.eval s

/-- A type for Boolean expressions, defined inductively -/
inductive BExp
| tt
| ff
| eq  (e₁ e₂ : AExp)
| le  (e₁ e₂ : AExp)
| not (b : BExp)
| and (b₁ b₂ : BExp)

/-- A function that evaluates Boolean expressions -/
def BExp.eval : BExp → State → Prop
| .tt, _ => True
| .ff, _ => False
| .eq e₁ e₂, s => e₁.eval s = e₂.eval s
| .le e₁ e₂, s => e₁.eval s ≤ e₂.eval s
| .not b, s => ¬ b.eval s
| .and b₁ b₂, s => b₁.eval s ∧ b₂.eval s

/-- An assertion is a predicate over state -/
abbrev Assertion := State → Prop

/-- Commands in our DSL
- `while` carries an explicit invariant
- This avoids invariant inference (out of scope)
- This matches textbook Hoare logic exactly
-/
inductive Cmd
| skip
| assign (x : Var) (e : AExp)
| seq    (c₁ c₂ : Cmd)
| ite    (b : BExp) (ct ce : Cmd)
| while  (b : BExp) (I : Assertion) (c : Cmd)

/-- Big step operational semantics
This will gives us semantic grounding for soundness proofs.
-/
inductive Exec : Cmd → State → State → Prop
| skip :
    Exec Cmd.skip s s

| assign :
    Exec (Cmd.assign x e) s (s.update x (e.eval s))

| seq :
    Exec c₁ s s' →
    Exec c₂ s' s'' →
    Exec (Cmd.seq c₁ c₂) s s''

| ite_true :
    b.eval s →
    Exec ct s s' →
    Exec (Cmd.ite b ct ce) s s'

| ite_false :
    ¬ b.eval s →
    Exec ce s s' →
    Exec (Cmd.ite b ct ce) s s'

| while_false :
    ¬ b.eval s →
    Exec (Cmd.while b I c) s s

| while_true :
    b.eval s →
    Exec c s s' →
    Exec (Cmd.while b I c) s' s'' →
    Exec (Cmd.while b I c) s s''

/-- A Hoare triple captures the semantic notion of correctness -/
def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ s s', Exec c s s' → P s → Q s'
