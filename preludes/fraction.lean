/- Quotient types -/

#print Equivalence
#print Setoid

structure Fraction where
num : Int
den : Int
den_ne_zero : den ≠ 0

def fraction_equiv (p q : Fraction) : Prop := p.num * q.den = q.num * p.den

theorem fraction_equiv_equiv : Equivalence fraction_equiv := by
  constructor
  { intro p; simp [fraction_equiv] }
  { intro p q h
    simp [fraction_equiv] at h ⊢
    rw [eq_comm]; exact h }
  { intro p q r hpq hqr
    simp [fraction_equiv] at hpq hqr ⊢
    linarith }

instance fractionSetoid : Setoid Fraction where
  r := fraction_equiv
  iseqv := fraction_equiv_equiv

def Rational := Quotient fractionSetoid





-- -- Lift operations to the quotient
-- def Rational.add : Rational → Rational → Rational :=
--   Quotient.lift₂ (fun a b =>
--     Quotient.mk fractionSetoid ⟨a.num * b.den + b.num * a.den, a.den * b.den, by simp [a.den_ne_zero, b.den_ne_zero]⟩)
--   (by
--     -- Must prove the operation respects equivalence
--     intro a₁ a₂ b₁ b₂ h₁ h₂
--     apply Quotient.sound
--     simp [fraction_equiv] at h₁ h₂ ⊢
--     linarith)
