
/- Subtypes -/

#check Subtype
#print Subtype

#check Subtype.val
#print Subtype.val

#check Subtype.property
#print Subtype.property

#check Subtype.mk
#print Subtype.mk

def Vector' (α : Type) (n : Nat) : Type :=
  { xs : List α // List.length xs = n }

def someVect : Vector' Int 3 := Subtype.mk [2, 3, 5] (by rfl)

#eval someVect.val
#check someVect.property

-- Operations on vectors can be defined by decomposing vectors with Subtype.val and Subtype.property,
-- manipulating the underlying lists, and then recomposing them with Subtype.mk

def Vector'.neg (v : Vector' Int n) : Vector' Int n :=
  Subtype.mk (List.map Int.neg v.val)
  (by rw [List.length_map]
      exact v.property)

#print List.length_map
#print Subtype.eq

theorem Int.neg_neg_id : Int.neg ∘ Int.neg = id := by grind

theorem Vector'.neg_neg (n : Nat) (v : Vector' Int n) :
  Vector'.neg (Vector'.neg v) = v := by
    apply Subtype.eq
    simp [Vector'.neg]
    simp [Int.neg_neg_id, List.map_map, List.map_id]
