/-- A variable is encoded as a string -/
abbrev Var := String

/-- State is a total mapping from variables to integer values -/
def State := Var → Int

def State.update (s : State) (x : Var) (v : Int) : State :=
  fun y => if y = x then v else s y

/-- Arithmetic expressions -/
inductive AExp
| const (n : Int)
| var   (x : Var)
| add   (e₁ e₂ : AExp)
| sub   (e₁ e₂ : AExp)
| mul   (e₁ e₂ : AExp)

open AExp

/-- Evaluate arithmetic expressions -/
def AExp.eval : AExp → State → Int
| .const n, _ => n
| .var x, s  => s x
| .add e₁ e₂, s => e₁.eval s + e₂.eval s
| .sub e₁ e₂, s => e₁.eval s - e₂.eval s
| .mul e₁ e₂, s => e₁.eval s * e₂.eval s

/-- Boolean expressions (return Prop to simplify proofs) -/
inductive BExp
| tt
| ff
| eq  (e₁ e₂ : AExp)
| le  (e₁ e₂ : AExp)
| not (b : BExp)
| and (b₁ b₂ : BExp)

open BExp

def BExp.eval : BExp → State → Prop
| .tt, _ => True
| .ff, _ => False
| .eq e₁ e₂, s => e₁.eval s = e₂.eval s
| .le e₁ e₂, s => e₁.eval s ≤ e₂.eval s
| .not b, s => ¬ (b.eval s)
| .and b₁ b₂, s => (b₁.eval s) ∧ (b₂.eval s)

/-- Assertions are predicates on states -/
abbrev Assertion := State → Prop

/-- Commands (while carries an explicit invariant) -/
inductive Cmd
| skip
| assign (x : Var) (e : AExp)
| seq    (c₁ c₂ : Cmd)
| ite    (b : BExp) (ct ce : Cmd)
| while  (b : BExp) (I : Assertion) (c : Cmd)

open Cmd

/-- Big-step operational semantics, with constructors binding the relevant states.
    Note how every constructor introduces the states (σ, σ₁, σ₂) it mentions. -/
inductive Exec : Cmd → State → State → Prop
| skip   (σ : State) :
    Exec Cmd.skip σ σ

| assign (σ : State) (x : Var) (e : AExp) :
    Exec (Cmd.assign x e) σ (σ.update x (e.eval σ))

| seq    (σ σ1 σ2 : State) (c1 c2 : Cmd)
        (h1 : Exec c1 σ σ1) (h2 : Exec c2 σ1 σ2) :
    Exec (Cmd.seq c1 c2) σ σ2

| if_true  (σ σ' : State) (b : BExp) (ct ce : Cmd)
           (hb : BExp.eval b σ) (h : Exec ct σ σ') :
    Exec (Cmd.ite b ct ce) σ σ'

| if_false (σ σ' : State) (b : BExp) (ct ce : Cmd)
           (hb : ¬ (BExp.eval b σ)) (h : Exec ce σ σ') :
    Exec (Cmd.ite b ct ce) σ σ'

| while_false (σ : State) (b : BExp) (I : Assertion) (c : Cmd)
              (hb : ¬ (BExp.eval b σ)) :
    Exec (Cmd.while b I c) σ σ

| while_true (σ σ1 σ2 : State) (b : BExp) (I : Assertion) (c : Cmd)
             (hb : BExp.eval b σ)
             (h1 : Exec c σ σ1)
             (h2 : Exec (Cmd.while b I c) σ1 σ2) :
    Exec (Cmd.while b I c) σ σ2

open Exec

/-- Hoare triple (semantic definition) -/
def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ σ σ', Exec c σ σ' → P σ → Q σ'

/-- Example: small command and a concrete Exec derivation -/
def c1 : Cmd := Cmd.assign "x" (AExp.const 1)

def init : State := fun _ => 0

def s1 := init.update "x" 1

example : Exec c1 init s1 := Exec.assign init "x" (AExp.const 1)
