/- Quotients -/

import Mathlib.Tactic.Linarith

#print Setoid
#print Equivalence

instance Integer.Setoid : Setoid (Nat × Nat) :=
  { r := fun (a, b) (c, d) => a + d = c + b
    iseqv :=
      { refl := by intro ⟨x, y⟩; rfl
        symm := by
          intro ⟨a, b⟩ ⟨c, d⟩ h
          simp at h ⊢
          rw [h]
        trans := by
          intro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ h1 h2
          simp at h1 h2
          linarith } }

theorem Integer.Setoid_Iff (x y : Nat × Nat) :
  x ≈ y ↔ x.1 + y.2 = y.1 + x.2 := by rfl

#print Quotient
#print Quotient.mk

def Integer : Type := Quotient Integer.Setoid

def Integer.zero : Integer := ⟦(0, 0)⟧

-- Any term of the form ⟦(m, m)⟧ represents zero
theorem Integer.zero_eq (m : Nat) : Integer.zero = ⟦(m, m)⟧  := by
  rw [Integer.zero]
  apply Quotient.sound
  rw [Integer.Setoid_Iff]
  simp

#print Quotient.sound

-- Lifting operations from base type to quotient type
def Integer.add : Integer → Integer → Integer :=
  Quotient.lift₂
    (fun (a, b) (c, d) => ⟦(a + c, b + d)⟧)
    (by
      intros
      apply Quotient.sound
      rw [Integer.Setoid_Iff] at *
      omega)

def Integer.one : Integer := ⟦(1, 0)⟧
def Integer.two : Integer := ⟦(2, 0)⟧

example : Integer.add .one .zero = .two := by
  rw [Integer.add, Integer.one, Integer.zero, Integer.two]
  simp [*] at *
  sorry

-- #eval Integer.add .one .zero

instance Fraction.Setoid : Setoid (Int × Int) :=
  { r := _
    iseqv := _ }
