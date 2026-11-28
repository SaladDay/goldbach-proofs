import Mathlib

/-!
# Cut `L-goldbach-cut-b9d6ce713bb35e6ec22ae214`

Absorb the square of a coefficient cutoff into the stronger logarithmic saving.

The cutoff hypothesis `x6 ≤ x1 ^ x4` gives `x6 ^ 2 ≤ x1 ^ (2 * x4)`, and since
`x1 ^ (x5 + 2 * x4) = x1 ^ x5 * x1 ^ (2 * x4)` with `x1 > 0`, the extra factor
`x1 ^ (2 * x4)` cancels exactly against the squared cutoff.  The nonnegativity of
`x3 * x2` makes the division monotone in the numerator coefficient.
-/

namespace Conjectures.Cuts.Taskb9d6ce713bb35e6ec22ae214_aux

/-- Squaring the cutoff bound. -/
lemma sq_le_pow_two_mul {x1 : ℝ} {x6 : ℕ} {x4 : ℕ}
    (h : (x6 : ℝ) ≤ x1 ^ x4) : (x6 : ℝ) ^ (2 : ℕ) ≤ x1 ^ (2 * x4) := by
  have h1 : (x6 : ℝ) ^ (2 : ℕ) ≤ (x1 ^ x4) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (Nat.cast_nonneg x6) h 2
  have h2 : (x1 ^ x4) ^ (2 : ℕ) = x1 ^ (2 * x4) := by
    rw [← pow_mul]
    congr 1
    ring
  linarith

/-- The cancellation of the extra power in the denominator. -/
lemma cancel (x1 : ℝ) (hx1 : 0 < x1) (x2 x3 : ℝ) (x4 x5 : ℕ) :
    x1 ^ (2 * x4) * (x3 * x2 / x1 ^ (x5 + (2 : ℕ) * x4)) = x3 * x2 / x1 ^ x5 := by
  have hxp : x1 ^ (x5 + (2 : ℕ) * x4) = x1 ^ x5 * x1 ^ (2 * x4) := pow_add x1 x5 (2 * x4)
  have h5 : x1 ^ x5 ≠ 0 := pow_ne_zero _ hx1.ne'
  have h24 : x1 ^ (2 * x4) ≠ 0 := pow_ne_zero _ hx1.ne'
  rw [hxp]
  field_simp

end Conjectures.Cuts.Taskb9d6ce713bb35e6ec22ae214_aux

theorem Conjectures.Cuts.Taskb9d6ce713bb35e6ec22ae214 :
∀ (x1 x2 x3 : ℝ) (x4 x5 x6 : ℕ), (0 : ℝ) < x1 → (0 : ℝ) ≤ x2 → (0 : ℝ) ≤ x3 → ↑x6 ≤ x1 ^ x4 → ↑x6 ^ (2 : ℕ) * (x3 * x2 / x1 ^ (x5 + (2 : ℕ) * x4)) ≤ x3 * x2 / x1 ^ x5 := by
  intro x1 x2 x3 x4 x5 x6 hx1 hx2 hx3 hx6
  have hsq : (x6 : ℝ) ^ (2 : ℕ) ≤ x1 ^ (2 * x4) :=
    Conjectures.Cuts.Taskb9d6ce713bb35e6ec22ae214_aux.sq_le_pow_two_mul hx6
  have hpos : (0 : ℝ) < x1 ^ (x5 + (2 : ℕ) * x4) := pow_pos hx1 _
  have hnn : (0 : ℝ) ≤ x3 * x2 := mul_nonneg hx3 hx2
  calc (x6 : ℝ) ^ (2 : ℕ) * (x3 * x2 / x1 ^ (x5 + (2 : ℕ) * x4))
      ≤ x1 ^ (2 * x4) * (x3 * x2 / x1 ^ (x5 + (2 : ℕ) * x4)) :=
        mul_le_mul_of_nonneg_right hsq (div_nonneg hnn hpos.le)
    _ = x3 * x2 / x1 ^ x5 :=
        Conjectures.Cuts.Taskb9d6ce713bb35e6ec22ae214_aux.cancel x1 hx1 x2 x3 x4 x5
