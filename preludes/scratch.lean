




(p ∧ (q ∨ ¬r)) ∨ (¬p ∧ (r → q)) ∧ ¬(q ∧ r)

((p ∨ q) → r) ∧ ¬(p ∧ r) ∧ ¬(¬q ∨ p)

¬((p ∧ q) ∨ (¬p ∧ ¬q))







p ∧ q ∧ r

p ∨ q ∨ r

(¬p ∨ ¬q) ∧ (¬q ∨ ¬r) ∧ (¬p ∨ ¬r)

¬p ∧ ¬q ∧ ¬r

(p ∧ ¬q ∧ ¬r) ∨ (¬p ∧ q ∧ ¬r) ∨ (¬p ∧ ¬q ∧ r)

--

For every person seated in some chair, we have the PBCs:

x11 + x12 + x13 ≥ 1
x21 + x22 + x23 ≥ 1
x31 + x32 + x33 ≥ 1

Its logical encoding is:

(x11 ∨ x12 ∨ x13) ∧ (x21 ∨ x22 ∨ x23) ∧ (x31 ∨ x32 ∨ x33)

--

At most one person may be seated in a chair, we have the PBC:

x11 + x21 + x31 ≤ 1
x12 + x22 + x32 ≤ 1
x13 + x23 + x33 ≤ 1

Its logical encoding is:

∧ ¬(x11 ∧ x21) ∧ ¬(x21 ∧ x31) ∧ ¬(x31 ∧ x11) ∧
¬(x12 ∧ x22) ∧ ¬(x22 ∧ x32) ∧ ¬(x32 ∧ x12) ∧
¬(x13 ∧ x23) ∧ ¬(x23 ∧ x33) ∧ ¬(x33 ∧ x13)
