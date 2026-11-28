import Mathlib

/-!
Transport a common density bound for fixed-length blocks to a longer interval.

The long window `Icc (x3 - x4) x3` is covered by the `x4 / x5 + 1` short windows
`Icc (x3 - k * x5 - x5) (x3 - k * x5)` for `k < x4 / x5 + 1`, each of which is
one of the windows controlled by the hypothesis.  Since
`(x4 / x5 + 1) * x5 ≤ x4 + x5 ≤ 2 * x4` (using `x5 ≤ x4`), summing the short
bounds loses at most the factor two.
-/

namespace Conjectures.Cuts.Task10e276396a3256b00707ddf1_aux

/-- Covering a long interval by short windows that extend to the left of their
right endpoint. -/
theorem card_le_sum_windows (x1 : ℕ → Prop) [DecidablePred x1] (a b s : ℕ)
    (hab : a ≤ b) (hs : 0 < s) :
    ((Finset.Icc a b).filter x1).card ≤
      ∑ k ∈ Finset.range ((b - a) / s + 1),
        ((Finset.Icc (b - k * s - s) (b - k * s)).filter x1).card := by
  have hsub : (Finset.Icc a b).filter x1 ⊆
      (Finset.range ((b - a) / s + 1)).biUnion
        (fun k => (Finset.Icc (b - k * s - s) (b - k * s)).filter x1) := by
    intro n hn
    obtain ⟨hnIcc, hP⟩ := Finset.mem_filter.mp hn
    obtain ⟨ha, hb⟩ := Finset.mem_Icc.mp hnIcc
    have hd : n + (b - n) = b := Nat.add_sub_of_le hb
    have hdiv : (b - n) / s * s + (b - n) % s = b - n := by
      rw [mul_comm]
      exact Nat.div_add_mod (b - n) s
    have hmod := Nat.mod_lt (b - n) hs
    have hle : (b - n) / s * s ≤ b - n := Nat.div_mul_le_self (b - n) s
    have hk : (b - n) / s ≤ (b - a) / s := Nat.div_le_div_right (by omega)
    refine Finset.mem_biUnion.mpr ⟨(b - n) / s, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hP⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

end Conjectures.Cuts.Task10e276396a3256b00707ddf1_aux

theorem Conjectures.Cuts.Task10e276396a3256b00707ddf1 :
    ∀ (x1 : ℕ → Prop) [x2 : DecidablePred x1] {x3 x4 x5 : ℕ} {x6 : ℝ}, (0 : ℕ) < x5 → x5 ≤ x4 → x4 ≤ x3 → (0 : ℝ) ≤ x6 → (∀ (x11 : ℕ), x3 - x4 ≤ x11 → x11 ≤ x3 → ↑(Finset.filter x1 (Finset.Icc (x11 - x5) x11)).card ≤ ↑x5 * x6) → ↑(Finset.filter x1 (Finset.Icc (x3 - x4) x3)).card ≤ (2 : ℝ) * ↑x4 * x6 := by
  intro x1 _x2 x3 x4 x5 x6 h5 h54 h43 h6 hwin
  have hba : x3 - (x3 - x4) = x4 := by omega
  have hcov := Conjectures.Cuts.Task10e276396a3256b00707ddf1_aux.card_le_sum_windows
    x1 (x3 - x4) x3 x5 (by omega) h5
  rw [hba] at hcov
  have hterm : ∀ k ∈ Finset.range (x4 / x5 + 1),
      (((Finset.Icc (x3 - k * x5 - x5) (x3 - k * x5)).filter x1).card : ℝ) ≤
        (x5 : ℝ) * x6 := by
    intro k hk
    have hk' : k ≤ x4 / x5 := by
      have := Finset.mem_range.mp hk
      omega
    have hks : k * x5 ≤ x4 :=
      le_trans (Nat.mul_le_mul_right x5 hk') (Nat.div_mul_le_self x4 x5)
    exact hwin (x3 - k * x5) (by omega) (by omega)
  have hcast : (((Finset.Icc (x3 - x4) x3).filter x1).card : ℝ) ≤
      ∑ k ∈ Finset.range (x4 / x5 + 1),
        (((Finset.Icc (x3 - k * x5 - x5) (x3 - k * x5)).filter x1).card : ℝ) := by
    exact_mod_cast hcov
  have hKnat : (x4 / x5 + 1) * x5 ≤ 2 * x4 := by
    have h1 : (x4 / x5 + 1) * x5 = x4 / x5 * x5 + x5 := Nat.succ_mul _ _
    have h2 : x4 / x5 * x5 ≤ x4 := Nat.div_mul_le_self x4 x5
    omega
  have hK : ((x4 / x5 + 1 : ℕ) : ℝ) * (x5 : ℝ) ≤ 2 * (x4 : ℝ) := by
    exact_mod_cast hKnat
  calc (((Finset.Icc (x3 - x4) x3).filter x1).card : ℝ)
      ≤ ∑ k ∈ Finset.range (x4 / x5 + 1),
          (((Finset.Icc (x3 - k * x5 - x5) (x3 - k * x5)).filter x1).card : ℝ) :=
        hcast
    _ ≤ ∑ _k ∈ Finset.range (x4 / x5 + 1), (x5 : ℝ) * x6 :=
        Finset.sum_le_sum hterm
    _ = ((x4 / x5 + 1 : ℕ) : ℝ) * ((x5 : ℝ) * x6) := by
        simp [Finset.sum_const, Finset.card_range]
    _ = (((x4 / x5 + 1 : ℕ) : ℝ) * (x5 : ℝ)) * x6 := by ring
    _ ≤ (2 * (x4 : ℝ)) * x6 := mul_le_mul_of_nonneg_right hK h6
    _ = (2 : ℝ) * ↑x4 * x6 := by ring
