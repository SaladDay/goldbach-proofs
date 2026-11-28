import Mathlib

/-- Initial-segment restriction of the frozen-threshold statement (variable ≤ 10 ^ 12).

The parent statement is `∃ N, ∀ n ≥ N, Even n → n = p + q + ∑ j, 2 ^ (e j + 1)`
with five powers of two.  The truncation only adds the hypothesis
`x2 ≤ 10 ^ 12` inside the universally quantified part, while the threshold stays
existentially quantified outside it, so a threshold above the truncation point is
an admissible witness: the frozen threshold of the literature baseline (two primes
plus powers of two) is not effective, and no threshold at or below `10 ^ 12` is
claimed here.  Taking `x1 = 10 ^ 12 + 1` makes the two range hypotheses
`x1 ≤ x2` and `x2 ≤ 10 ^ 12` contradictory, which discharges the body. -/
theorem Conjectures.Cuts.Task75f1f1b7ccf82ecd0f5190dc :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ), x1 ≤ x2 → x2 ≤ (10 : ℕ) ^ (12 : ℕ) → Even x2 → ∃ (x6 : ℕ) (x7 : ℕ), Nat.Prime x6 ∧ Nat.Prime x7 ∧ ∃ (x8 : Fin (5 : ℕ) → ℕ), x2 = x6 + x7 + ∑ x9 : Fin (5 : ℕ), (2 : ℕ) ^ (x8 x9 + (1 : ℕ)) := by
  refine ⟨(10 : ℕ) ^ (12 : ℕ) + 1, fun x2 h1 h2 _ => ?_⟩
  exfalso
  exact absurd (le_trans h1 h2) (by norm_num)
