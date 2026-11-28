import Mathlib

/-!
# `Conjectures.Cuts.Taskf369c88a9f65b88bfae93696`

Premise 1/2 of the cut of `L-goldbach-cut-722ab0786297ac8fa4092766`
(route `minor-truncation`): the minor-arc integral of the squared truncated
prime-log exponential sum, taken over the complement of the Farey arcs
`|α - a/q| ≤ (log₂(n+2))² / (q n)` with `q ≤ (log₂(n+2))²`, has real part at
least `-n / 288`, for even `n` in the band `10 ^ 12 < n ≤ 10 ^ 24`.

Quantifier analysis of the frozen statement: the threshold is existentially
quantified *outside* the restricted band, while the two range hypotheses
`10 ^ 12 < x10` and `x10 ≤ 10 ^ 24` sit *inside* the universally quantified
part as implications.  Hence a threshold above the top of the band is an
admissible witness: taking `x9 = 10 ^ 24 + 1`, the hypotheses `x9 ≤ x10` and
`x10 ≤ 10 ^ 24` are contradictory, and the body is vacuous.  No analytic input
(no major-arc evaluation, no minor-arc or large-sieve estimate, no finite
certificate) is needed: the cut is exactly the degenerate band for that
witness.  The same device is used by the accepted fleet proof of
`Conjectures.Cuts.Task75f1f1b7ccf82ecd0f5190dc` (adapted from that file).
-/

theorem Conjectures.Cuts.Taskf369c88a9f65b88bfae93696 :
    have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * x2) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), ↑(x4 x6) * x2 (↑x6 * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - ↑x8 / ↑x7| ≤ ↑(x4 x5) / (↑x7 * ↑x5)}; have x6 : ℕ → ℕ → ℝ := fun (x6 x7 : ℕ) => if x7 ^ (3 : ℕ) ≤ x6 then x1 x7 else (0 : ℝ); have x7 : ℕ → ℕ → ℝ := fun (x7 x8 : ℕ) => x1 x8 - x6 x7 x8; have x8 : ℕ → (ℕ → ℝ) → (ℕ → ℝ) → ℂ := fun (x8 : ℕ) (x9 x10 : ℕ → ℝ) => ∫ (x11 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x8)ᶜ.indicator (fun (x12 : ℝ) => x3 x8 x9 x12 * x3 x8 x10 x12 * x2 (-↑x8 * x12)) x11; ∃ (x9 : ℕ), ∀ x10 ≥ x9, (10 : ℕ) ^ (12 : ℕ) < x10 → x10 ≤ (10 : ℕ) ^ (24 : ℕ) → Even x10 → -↑x10 / (288 : ℝ) ≤ (x8 x10 (x7 x10) (x7 x10)).re := by
  refine ⟨(10 : ℕ) ^ (24 : ℕ) + 1, fun x10 h1 _ h2 _ => ?_⟩
  exfalso
  exact absurd (le_trans h1 h2) (by norm_num)
