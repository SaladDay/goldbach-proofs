import Mathlib

/-!
# Cut `L-goldbach-cut-c0b558a87bf94e8009b2c2de`

Balanced linear prime representations are detected by the complementary quotient.

The left side asks for primes `x6`, `x7` with `x2 * x6 + x3 * x7 = x1` whose two terms both
sit in the square-root window `|↑(x2 * x6) - ↑x1 / 2| ≤ √↑x1`.  Because the two terms add up
to `x1`, the two window conditions are the same condition (the second one is the first one
reflected in `x1 / 2`), so a single squared midpoint inequality
`(2 * ↑(x2 * x6) - ↑x1) ^ 2 ≤ 4 * ↑x1` suffices, and the second prime is recovered as the
quotient `(x1 - x2 * x6) / x3`.  The equivalence is elementary real and natural-number
arithmetic: the helper lemmas below only translate between `|a - n / 2| ≤ √n` and
`(2 * a - n) ^ 2 ≤ 4 * n` for `0 ≤ n`.
-/

namespace Conjectures.Cuts.Taskc0b558a87bf94e8009b2c2de_aux

/-- A term inside the square-root window satisfies the squared midpoint inequality. -/
lemma sq_le_four_of_abs_le {a n : ℝ} (hn : 0 ≤ n) (h : |a - n / 2| ≤ Real.sqrt n) :
    (2 * a - n) ^ (2 : ℕ) ≤ 4 * n := by
  have hs : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  have h1 : (a - n / 2) ^ (2 : ℕ) ≤ (Real.sqrt n) ^ (2 : ℕ) := by
    have := pow_le_pow_left₀ (abs_nonneg (a - n / 2)) h 2
    simpa [sq_abs] using this
  have h2 : (Real.sqrt n) ^ (2 : ℕ) = n := Real.sq_sqrt hn
  nlinarith [h1, h2]

/-- Conversely, the squared midpoint inequality puts the term inside the square-root window. -/
lemma abs_le_of_sq_le_four {a n : ℝ} (hn : 0 ≤ n) (h : (2 * a - n) ^ (2 : ℕ) ≤ 4 * n) :
    |a - n / 2| ≤ Real.sqrt n := by
  have hs : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
  have h2 : (Real.sqrt n) ^ (2 : ℕ) = n := Real.sq_sqrt hn
  have key : (a - n / 2) ^ (2 : ℕ) ≤ (Real.sqrt n) ^ (2 : ℕ) := by nlinarith [h, h2]
  rw [abs_le]
  constructor
  · by_contra hlt
    have hm : a - n / 2 + Real.sqrt n < 0 := by linarith
    have hd : a - n / 2 - Real.sqrt n < 0 := by linarith
    have hp : 0 < (a - n / 2 + Real.sqrt n) * (a - n / 2 - Real.sqrt n) :=
      mul_pos_of_neg_of_neg hm hd
    have hr : (a - n / 2 + Real.sqrt n) * (a - n / 2 - Real.sqrt n) =
        (a - n / 2) ^ (2 : ℕ) - (Real.sqrt n) ^ (2 : ℕ) := by ring
    linarith [hp, hr, key]
  · by_contra hgt
    have hm : a - n / 2 + Real.sqrt n > 0 := by linarith
    have hd : a - n / 2 - Real.sqrt n > 0 := by linarith
    have hp : 0 < (a - n / 2 + Real.sqrt n) * (a - n / 2 - Real.sqrt n) :=
      mul_pos hm hd
    have hr : (a - n / 2 + Real.sqrt n) * (a - n / 2 - Real.sqrt n) =
        (a - n / 2) ^ (2 : ℕ) - (Real.sqrt n) ^ (2 : ℕ) := by ring
    linarith [hp, hr, key]

end Conjectures.Cuts.Taskc0b558a87bf94e8009b2c2de_aux

theorem Conjectures.Cuts.Taskc0b558a87bf94e8009b2c2de :
∀ (x1 x2 x3 : ℕ), (0 : ℕ) < x2 → (0 : ℕ) < x3 → ((∃ (x6 : ℕ) (x7 : ℕ), Nat.Prime x6 ∧ Nat.Prime x7 ∧ x2 * x6 + x3 * x7 = x1 ∧ |↑(x2 * x6) - ↑x1 / (2 : ℝ)| ≤ √↑x1 ∧ |↑(x3 * x7) - ↑x1 / (2 : ℝ)| ≤ √↑x1) ↔ {x6 ∈ Finset.range (x1 + (1 : ℕ)) | Nat.Prime x6 ∧ x2 * x6 ≤ x1 ∧ x3 ∣ x1 - x2 * x6 ∧ Nat.Prime ((x1 - x2 * x6) / x3) ∧ ((2 : ℝ) * ↑(x2 * x6) - ↑x1) ^ (2 : ℕ) ≤ (4 : ℝ) * ↑x1}.Nonempty) := by
  intro x1 x2 x3 hx2 hx3
  constructor
  · rintro ⟨x6, x7, hp6, hp7, heq, hb1, _hb2⟩
    refine ⟨x6, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hp6, ?_, ?_, ?_, ?_⟩⟩
    · have hle : x6 ≤ x2 * x6 := Nat.le_mul_of_pos_left x6 hx2
      omega
    · omega
    · have hsub : x1 - x2 * x6 = x3 * x7 := by omega
      refine ⟨x7, ?_⟩
      omega
    · have hsub : x1 - x2 * x6 = x3 * x7 := by omega
      rw [hsub, Nat.mul_div_cancel_left x7 hx3]
      exact hp7
    · exact Conjectures.Cuts.Taskc0b558a87bf94e8009b2c2de_aux.sq_le_four_of_abs_le
        (Nat.cast_nonneg x1) hb1
  · rintro ⟨x6, hmem⟩
    obtain ⟨_, hp6, hle, hdvd, hpq, hsq⟩ := Finset.mem_filter.mp hmem
    refine ⟨x6, (x1 - x2 * x6) / x3, hp6, hpq, ?_, ?_, ?_⟩
    · have h7 : x3 * ((x1 - x2 * x6) / x3) = x1 - x2 * x6 := by
        rw [mul_comm]
        exact Nat.div_mul_cancel hdvd
      omega
    · exact Conjectures.Cuts.Taskc0b558a87bf94e8009b2c2de_aux.abs_le_of_sq_le_four
        (Nat.cast_nonneg x1) hsq
    · have h7 : x3 * ((x1 - x2 * x6) / x3) = x1 - x2 * x6 := by
        rw [mul_comm]
        exact Nat.div_mul_cancel hdvd
      have hb1 : |↑(x2 * x6) - ↑x1 / (2 : ℝ)| ≤ √↑x1 :=
        Conjectures.Cuts.Taskc0b558a87bf94e8009b2c2de_aux.abs_le_of_sq_le_four
          (Nat.cast_nonneg x1) hsq
      have hcast : ((x3 * ((x1 - x2 * x6) / x3) : ℕ) : ℝ) =
          (x1 : ℝ) - ((x2 * x6 : ℕ) : ℝ) := by
        rw [h7, Nat.cast_sub hle]
      rw [hcast]
      have hneg : (x1 : ℝ) - ((x2 * x6 : ℕ) : ℝ) - (x1 : ℝ) / (2 : ℝ) =
          -(((x2 * x6 : ℕ) : ℝ) - (x1 : ℝ) / (2 : ℝ)) := by ring
      rw [hneg, abs_neg]
      exact hb1
