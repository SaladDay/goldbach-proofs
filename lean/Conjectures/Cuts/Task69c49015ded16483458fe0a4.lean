import Mathlib

theorem Conjectures.Cuts.Task69c49015ded16483458fe0a4 :
    ∀ (x1 x2 x3 x4 : ℝ), x1 ≤ (2 : ℝ) * x2 + (1 : ℝ) * x3 → (0 : ℝ) ≤ x3 → (1 : ℝ) ≤ x4 →
      x1 ≤ (2 : ℝ) * x2 + x4 * x3 := by
  intro x1 x2 x3 x4 h1 h2 h3
  have h4 : (1 : ℝ) * x3 ≤ x4 * x3 := by
    have : (1 : ℝ) ≤ x4 := h3
    nlinarith
  linarith
