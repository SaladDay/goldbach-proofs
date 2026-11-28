import Mathlib

/-!
# Cut `L-goldbach-cut-e8628538989256216685faf6`

Bound the center whenever its balanced interval reaches prime 2 or 3.

The hypotheses say `x2 ≥ 0` and `d := x1 - x2 ∈ [2, 3]`, i.e. the interval of half-width `x2`
around the center `x1` contains `2` or `3`.  We claim that `2 * x2 ^ 3 ≤ x1 ^ 2` then forces
`x1 ≤ 5`.

Indeed, `x1 = x2 + d ≤ x2 + 3`.  If `x2 ≥ 3` then `x2 + 3 ≤ 2 * x2`, so `0 ≤ x1 ≤ 2 * x2`
gives `x1 ^ 2 ≤ 4 * x2 ^ 2`, while `x2 ≥ 3` gives `6 * x2 ^ 2 ≤ 2 * x2 ^ 3`; the two are
incompatible with `2 * x2 ^ 3 ≤ x1 ^ 2`.  Hence `x2 ≤ 2`, and then `x1 ≤ x2 + 3 ≤ 5`.

Self-contained: Mathlib only, all hypotheses used, no auxiliary definitions.
-/

theorem Conjectures.Cuts.Taske8628538989256216685faf6 :
    ∀ (x1 x2 : ℤ), (0 : ℤ) ≤ x2 → (2 : ℤ) ≤ x1 - x2 → x1 - x2 ≤ (3 : ℤ) → (2 : ℤ) * x2 ^ (3 : ℕ) ≤ x1 ^ (2 : ℕ) → x1 ≤ (5 : ℤ) := by
  intro x1 x2 h0 h2 h3 h4
  have hx2 : x2 ≤ 2 := by
    by_contra hlt
    have h3' : (3 : ℤ) ≤ x2 := by linarith
    have hx1 : x1 ≤ 2 * x2 := by linarith
    have hpos : (0 : ℤ) ≤ x1 := by linarith
    have hsq : x1 ^ (2 : ℕ) ≤ (2 * x2) ^ (2 : ℕ) := by nlinarith
    have hcube : (6 : ℤ) * x2 ^ (2 : ℕ) ≤ 2 * x2 ^ (3 : ℕ) := by nlinarith
    nlinarith
  linarith
