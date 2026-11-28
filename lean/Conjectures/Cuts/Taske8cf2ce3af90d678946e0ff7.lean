import Mathlib

/-!
Zero-fiber control by the squared one-sided deficit from a threshold.

For a threshold `x3 ≥ 0` and a weight `x2 : ℕ → ℕ`, every index `a` of the zero fiber
`{a ∈ x1 | x2 a = 0}` contributes exactly `max 0 (x3 - x2 a) ^ 2 = max 0 x3 ^ 2 = x3 ^ 2`
to the right-hand sum, since `x3 ≥ 0`.  The zero fiber is a subset of `x1` and every summand
is a square, hence nonnegative, so `Finset.sum_le_sum_of_subset_of_nonneg` bounds the right-hand
sum from below by the sum over the zero fiber, which is the constant `x3 ^ 2` summed
`(card of the fiber)` times.

Self-contained: Mathlib only, two private auxiliary lemmas.  Quantifiers are exactly as stated:
arbitrary finset `x1`, arbitrary weight `x2`, arbitrary real threshold `x3` with the single
hypothesis `0 ≤ x3`.
-/

namespace Conjectures.Cuts.Taske8cf2ce3af90d678946e0ff7_aux

private lemma fiber_sum {x1 : Finset ℕ} {x2 : ℕ → ℕ} {x3 : ℝ} (hx3 : (0 : ℝ) ≤ x3) :
    ∑ x5 ∈ x1.filter (fun a => x2 a = 0), Max.max (0 : ℝ) (x3 - ↑(x2 x5)) ^ (2 : ℕ)
      = ((x1.filter (fun a => x2 a = 0)).card : ℝ) * x3 ^ (2 : ℕ) := by
  have h : ∀ a ∈ x1.filter (fun a => x2 a = 0),
      Max.max (0 : ℝ) (x3 - ↑(x2 a)) ^ (2 : ℕ) = x3 ^ (2 : ℕ) := by
    intro a ha
    have h0 : x2 a = 0 := (Finset.mem_filter.mp ha).2
    simp [h0, max_eq_right hx3]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]

private lemma fiber_le {x1 : Finset ℕ} {x2 : ℕ → ℕ} {x3 : ℝ} :
    ∑ x5 ∈ x1.filter (fun a => x2 a = 0), Max.max (0 : ℝ) (x3 - ↑(x2 x5)) ^ (2 : ℕ)
      ≤ ∑ x5 ∈ x1, Max.max (0 : ℝ) (x3 - ↑(x2 x5)) ^ (2 : ℕ) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun _ _ _ => sq_nonneg _)

end Conjectures.Cuts.Taske8cf2ce3af90d678946e0ff7_aux

theorem Conjectures.Cuts.Taske8cf2ce3af90d678946e0ff7 :
    ∀ (x1 : Finset ℕ) (x2 : ℕ → ℕ) (x3 : ℝ), (0 : ℝ) ≤ x3 → ↑{x5 ∈ x1 | x2 x5 = (0 : ℕ)}.card * x3 ^ (2 : ℕ) ≤ ∑ x5 ∈ x1, Max.max (0 : ℝ) (x3 - ↑(x2 x5)) ^ (2 : ℕ) := by
  intro x1 x2 x3 hx3
  calc (↑{x5 ∈ x1 | x2 x5 = (0 : ℕ)}.card : ℝ) * x3 ^ (2 : ℕ)
      = ∑ x5 ∈ x1.filter (fun a => x2 a = 0),
          Max.max (0 : ℝ) (x3 - ↑(x2 x5)) ^ (2 : ℕ) :=
        (Conjectures.Cuts.Taske8cf2ce3af90d678946e0ff7_aux.fiber_sum hx3).symm
    _ ≤ ∑ x5 ∈ x1, Max.max (0 : ℝ) (x3 - ↑(x2 x5)) ^ (2 : ℕ) :=
        Conjectures.Cuts.Taske8cf2ce3af90d678946e0ff7_aux.fiber_le
