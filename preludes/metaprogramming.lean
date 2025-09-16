/-
  Metaprogramming monads (TaticM)

  This material is from Chapter 8 (Metaprogramming) of Hitchhiker's Guide to Logical Verification
-/

import Lean
open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic

/- Search for a matching hypothesis (like `assumption` tactic) -/

def hypothesis : TacticM Unit :=
  withMainContext (do
  let target ← getMainTarget
  let lctx ← getLCtx
  for ldecl in lctx do
    if ! LocalDecl.isImplementationDetail ldecl then
      let eq ← isDefEq (LocalDecl.type ldecl) target
      if eq then
        let goal ← getMainGoal
        MVarId.assign goal (LocalDecl.toExpr ldecl)
        return
  failure)

elab "hypothesis" : tactic => hypothesis

example {p : α → Prop} {a : α} (hpa : p a) : p a := by hypothesis

/- A conjunction destructing tactic -/

example (h : a ∧ b ∧ c ∧ d) : a := by apply And.left h
example (h : a ∧ b ∧ c ∧ d) : b := by apply And.left (And.right h)
example (h : a ∧ b ∧ c ∧ d) : c := by apply And.left (And.right (And.right h))
example (h : a ∧ b ∧ c ∧ d) : d := by apply And.right (And.right (And.right h))

partial def destructAndExpr (hP : Expr) : TacticM Bool :=
  withMainContext (do
  let target ← getMainTarget
  let P ← inferType hP
  let eq ← isDefEq P target
  if eq then
    let goal ← getMainGoal
    MVarId.assign goal hP
    return true
  else
    match Expr.and? P with
    | Option.none   => return false
    | Option.some _ =>
      let hQ ← mkAppM ``And.left #[hP]
      let success ← destructAndExpr hQ
      if success then return true
      else
        let hR ← mkAppM ``And.right #[hP]
        destructAndExpr hR)

def destructAnd (name : Name) : TacticM Unit :=
  withMainContext do
  let h ← getFVarFromUserName name
  let success ← destructAndExpr h
  if ! success then failure

elab "destruct_and" h:ident : tactic => destructAnd h.getId

example (h : a ∧ b ∧ c ∧ d) : a := by destruct_and h
example (h : a ∧ b ∧ c ∧ d) : b := by destruct_and h
example (h : a ∧ b ∧ c ∧ d) : c := by destruct_and h
example (h : a ∧ b ∧ c ∧ d) : d := by destruct_and h

/- A direct proof finder -/

def isTheorem : ConstantInfo → Bool
| ConstantInfo.axiomInfo _ => true
| ConstantInfo.thmInfo _   => true
| _                        => false

def applyConstant (name : Name) : TacticM Unit := do
  let cst ← mkConstWithFreshMVarLevels name
  liftMetaTactic (fun goal => MVarId.apply goal cst)

def andThenOnSubgoals (tac₁ tac₂ : TacticM Unit) : TacticM Unit := do
  let origGoals ← getGoals
  let mainGoal ← getMainGoal
  setGoals [mainGoal]
  tac₁
  let subgoals₁ ← getUnsolvedGoals
  let mut newGoals := []
  for subgoal in subgoals₁ do
    let assigned ← MVarId.isAssigned subgoal
    if ! assigned then
      setGoals [subgoal]
      tac₂
      let subgoals₂ ← getUnsolvedGoals
      newGoals := newGoals ++ subgoals₂
  setGoals (newGoals ++ List.tail origGoals)

def proveUsingTheorem (name : Name) : TacticM Unit :=
  andThenOnSubgoals (applyConstant name) hypothesis

def proveDirect : TacticM Unit := do
  let origGoals ← getUnsolvedGoals
  let goal ← getMainGoal
  setGoals [goal]
  let env ← getEnv
  for (name, info) in SMap.toList (Environment.constants env) do
    if isTheorem info && ! ConstantInfo.isUnsafe info then
      try
       proveUsingTheorem name
       logInfo m!"Proved directly by {name}."
       setGoals (List.tail origGoals)
       return
      catch _ => continue
  failure

elab "prove_direct" : tactic => proveDirect

theorem new : 4 + 3 = 10 := by sorry

example : 4 + 3 = 10 := by prove_direct
