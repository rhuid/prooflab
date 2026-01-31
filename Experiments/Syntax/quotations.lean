set_option diagnostics true

#check ``Nat.succ

def var : Int := 4

#eval var

#print Lean.Name
#print Lean.Name.num

#check Lean.Name.num `crap 4

def newthing := Lean.Name.num `crap 10

#eval newthing
#check newthing
#print newthing

-- #eval crap

#check ``Nat.succ

-- #eval ``(Nat.succ 3)

#check Lean.TSyntax ``Nat

#print Lean.SyntaxNodeKind
#print Lean.SyntaxNodeKinds
#print Lean.Syntax.node

#print Lean.Syntax
