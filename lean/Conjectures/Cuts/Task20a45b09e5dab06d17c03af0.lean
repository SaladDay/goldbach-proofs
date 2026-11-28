import Mathlib

open scoped BigOperators

/-- Elementary transfer: the flat weight `1 / |S|` on the sub-level set `S` of the window
already meets the `L²` mass budget (the exponent `8/3 + 1/12 = 11/4` is exactly the premise
exponent `3/4` plus `2`) and its weighted average of `x4` is at most the threshold. -/
theorem Conjectures.Cuts.Task20a45b09e5dab06d17c03af0 :
    ∀ (x1 : ℕ) (x2 x3 : ℝ) (x4 : ℕ → ℝ), (0 : ℕ) < x1 → (0 : ℝ) < x2 → (4 : ℝ) / x2 ^ (2 : ℕ) * ↑x1 ^ (3 / 4 : ℝ) ≤ ↑{x7 ∈ Finset.Icc x1 ((2 : ℕ) * x1) | x4 x7 ≤ x3 + x2 / (2 : ℝ) * ↑x1}.card → ∃ (x8 : ℕ → ℝ), (∀ (x9 : ℕ), (0 : ℝ) ≤ x8 x9) ∧ (∑ x9 ∈ Finset.Icc x1 ((2 : ℕ) * x1), x8 x9 ^ (2 : ℕ)) * ↑x1 ^ ((8 / 3 : ℝ) + (1 / 12 : ℝ)) ≤ (x2 / (2 : ℝ) * ↑x1) ^ (2 : ℕ) ∧ ∑ x9 ∈ Finset.Icc x1 ((2 : ℕ) * x1), x8 x9 * x4 x9 - x2 / (2 : ℝ) * ↑x1 ≤ x3 := by
  intro x1 x2 x3 x4 hx1 hx2 hcard
  set S : Finset ℕ :=
    {x7 ∈ Finset.Icc x1 ((2 : ℕ) * x1) | x4 x7 ≤ x3 + x2 / (2 : ℝ) * ↑x1}
  set T : ℝ := x3 + x2 / (2 : ℝ) * ↑x1
  have hx1R : (0 : ℝ) < (x1 : ℝ) := by exact_mod_cast hx1
  have hx2sq : (0 : ℝ) < x2 ^ (2 : ℕ) := by positivity
  have hpos : (0 : ℝ) < (4 : ℝ) / x2 ^ (2 : ℕ) * ↑x1 ^ (3 / 4 : ℝ) :=
    mul_pos (div_pos (by norm_num) hx2sq) (Real.rpow_pos_of_pos hx1R _)
  have hcard' : (4 : ℝ) / x2 ^ (2 : ℕ) * ↑x1 ^ (3 / 4 : ℝ) ≤ (S.card : ℝ) := hcard
  have hmR : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le hpos hcard'
  have hmne : (S.card : ℝ) ≠ 0 := ne_of_gt hmR
  set c : ℝ := 1 / (S.card : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hsub : S ⊆ Finset.Icc x1 ((2 : ℕ) * x1) := Finset.filter_subset _ _
  refine ⟨fun n => if n ∈ S then c else 0, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    by_cases hn : n ∈ S
    · simp [hn, hc]
    · simp [hn]
  · have hsum : (∑ n ∈ Finset.Icc x1 ((2 : ℕ) * x1), (if n ∈ S then c else 0) ^ (2 : ℕ)) =
        (S.card : ℝ) * c ^ (2 : ℕ) := by
      rw [← Finset.sum_subset hsub (fun n _ hn => by simp [hn])]
      have hcongr : (∑ n ∈ S, (if n ∈ S then c else 0) ^ (2 : ℕ)) = ∑ n ∈ S, c ^ (2 : ℕ) :=
        Finset.sum_congr rfl (fun n hn => by simp [hn])
      rw [hcongr, Finset.sum_const, nsmul_eq_mul]
    have hmc : (S.card : ℝ) * c ^ (2 : ℕ) = 1 / (S.card : ℝ) := by
      dsimp [c]
      field_simp
    have hexp : (x1 : ℝ) ^ ((8 / 3 : ℝ) + (1 / 12 : ℝ)) =
        (x1 : ℝ) ^ (3 / 4 : ℝ) * (x1 : ℝ) ^ (2 : ℝ) := by
      rw [show (8 / 3 : ℝ) + (1 / 12 : ℝ) = (3 / 4 : ℝ) + (2 : ℝ) by norm_num,
        Real.rpow_add hx1R, Real.rpow_two]
    have key : (4 : ℝ) * (x1 : ℝ) ^ (3 / 4 : ℝ) ≤ (S.card : ℝ) * x2 ^ (2 : ℕ) := by
      have h := mul_le_mul_of_nonneg_right hcard' (le_of_lt hx2sq)
      have hl : (4 : ℝ) / x2 ^ (2 : ℕ) * (x1 : ℝ) ^ (3 / 4 : ℝ) * x2 ^ (2 : ℕ) =
          (4 : ℝ) * (x1 : ℝ) ^ (3 / 4 : ℝ) := by
        field_simp
      rw [hl] at h
      exact h
    have key2 : (4 : ℝ) * (x1 : ℝ) ^ (3 / 4 : ℝ) * (x1 : ℝ) ^ (2 : ℝ) ≤
        (S.card : ℝ) * x2 ^ (2 : ℕ) * (x1 : ℝ) ^ (2 : ℝ) :=
      mul_le_mul_of_nonneg_right key (Real.rpow_nonneg hx1R.le _)
    rw [hsum, hmc, hexp]
    calc (1 / (S.card : ℝ)) * ((x1 : ℝ) ^ (3 / 4 : ℝ) * (x1 : ℝ) ^ (2 : ℝ))
        = (1 / (4 * (S.card : ℝ))) *
            ((4 : ℝ) * (x1 : ℝ) ^ (3 / 4 : ℝ) * (x1 : ℝ) ^ (2 : ℝ)) := by
          field_simp
      _ ≤ (1 / (4 * (S.card : ℝ))) *
            ((S.card : ℝ) * x2 ^ (2 : ℕ) * (x1 : ℝ) ^ (2 : ℝ)) := by
          gcongr
      _ = (x2 / (2 : ℝ) * ↑x1) ^ (2 : ℕ) := by
          rw [Real.rpow_two]
          field_simp
          ring
  · have hsum : (∑ n ∈ Finset.Icc x1 ((2 : ℕ) * x1), (if n ∈ S then c else 0) * x4 n) =
        c * ∑ n ∈ S, x4 n := by
      rw [← Finset.sum_subset hsub (fun n _ hn => by simp [hn])]
      have hcongr : (∑ n ∈ S, (if n ∈ S then c else 0) * x4 n) = ∑ n ∈ S, c * x4 n :=
        Finset.sum_congr rfl (fun n hn => by simp [hn])
      rw [hcongr, ← Finset.mul_sum]
    have hle : (∑ n ∈ S, x4 n) ≤ (S.card : ℝ) * T := by
      calc (∑ n ∈ S, x4 n) ≤ ∑ n ∈ S, T :=
            Finset.sum_le_sum (fun n hn => (Finset.mem_filter.mp hn).2)
        _ = (S.card : ℝ) * T := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    have hstep : c * (∑ n ∈ S, x4 n) ≤ c * ((S.card : ℝ) * T) :=
      mul_le_mul_of_nonneg_left hle hc
    have heq : c * ((S.card : ℝ) * T) = T := by
      dsimp [c]
      field_simp
    calc c * (∑ n ∈ S, x4 n) - x2 / (2 : ℝ) * ↑x1
        ≤ c * ((S.card : ℝ) * T) - x2 / (2 : ℝ) * ↑x1 := by linarith
      _ = T - x2 / (2 : ℝ) * ↑x1 := by rw [heq]
      _ = x3 := by dsimp [T]; ring
