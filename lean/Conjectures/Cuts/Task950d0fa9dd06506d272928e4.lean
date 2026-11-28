import Mathlib

/-!
Short-window companion of the almost-all Goldbach exception estimate.

The formal statement keeps the long-window side condition `H ^ 2 ≤ X` together
with the short-window condition `X < 2 * H`.  For `X ≥ 2` these are
incompatible: `X < 2 * H` forces `H ≥ 2`, hence `2 * H ≤ H ^ 2 ≤ X < 2 * H`, a
contradiction.  So the quantified statement is satisfied by any positive
constants `B2`, `C2` with threshold `T2 = 2`; no analytic input is needed.
-/

namespace Conjectures.Cuts.Task950d0fa9dd06506d272928e4_aux

/-- The two window conditions `H ^ 2 ≤ X` and `X < 2 * H` are incompatible as
soon as `2 ≤ X`. -/
theorem no_short_window (x6 x7 : ℕ) (hx6 : 2 ≤ x6)
    (hsq : x7 ^ (2 : ℕ) ≤ x6) (hlt : x6 < (2 : ℕ) * x7) : False := by
  have h7 : 2 ≤ x7 := by omega
  have hsq' : x7 * x7 ≤ x6 := by simpa only [pow_two] using hsq
  have hmul : 2 * x7 ≤ x7 * x7 := Nat.mul_le_mul_right x7 h7
  omega

end Conjectures.Cuts.Task950d0fa9dd06506d272928e4_aux

theorem Conjectures.Cuts.Task950d0fa9dd06506d272928e4 :
    ∀ (x1 : ℝ), (0 : ℝ) < x1 → ∃ (x3 : ℝ) (x4 : ℝ), (0 : ℝ) < x3 ∧ (0 : ℝ) < x4 ∧ ∃ (x5 : ℕ), ∀ (x6 x7 : ℕ), x5 ≤ x6 → x7 ≤ x6 → x7 ^ (2 : ℕ) ≤ x6 → x6 < (2 : ℕ) * x7 → ↑x6 ^ (7 / 120 : ℝ) * Real.log ↑x6 ^ x3 ≤ ↑x7 → ↑{x13 ∈ Finset.Icc (x6 - x7) x6 | (4 : ℕ) ≤ x13 ∧ Even x13 ∧ ∀ x14 ∈ Finset.range (x13 + (1 : ℕ)), ¬(Nat.Prime x14 ∧ Nat.Prime (x13 - x14))}.card ≤ x4 * ↑x7 / Real.log ↑x6 ^ x1 := by
  intro x1 _hx1
  refine ⟨1, 1, by norm_num, by norm_num, 2, ?_⟩
  intro x6 x7 hx6 _hHle hsq hlt _hside
  exact (Conjectures.Cuts.Task950d0fa9dd06506d272928e4_aux.no_short_window
    x6 x7 hx6 hsq hlt).elim
