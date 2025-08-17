/-
Formalization and verification of some part of propositional logic
-/

namespace Prooflab.Propositional

theorem and_comm' : a ∧ b → b ∧ a :=
  fun ⟨ha, hb⟩ => ⟨hb, ha⟩

theorem and_assoc' : (a ∧ b) ∧ c → a ∧ (b ∧ c) :=
  fun ⟨⟨ha, hb⟩, hc⟩ => ⟨ha, ⟨hb, hc⟩⟩

theorem and_or_dist' : a ∧ (b ∨ c) → (a ∧ b) ∨ (a ∧ c) :=
  fun habc =>
  Or.elim habc.right
    (fun hb => Or.inl ⟨habc.left, hb⟩)
    (fun hc => Or.inr ⟨habc.left, hc⟩)

end Prooflab.Propositional
