import Mathlib

theorem Conjectures.Cuts.Taskb72d4592a6c19cfb776ee5b2 :
    ∀ (x1 : ℕ) (x2 : ℕ → Prop),
      (∃ (x3 : ℕ) (x4 : ℕ), x2 x3 ∧ x2 x4 ∧ x3 + x4 = (2 : ℕ) * x1 ∧
          (x3 - x4) ^ (2 : ℕ) ≤ (2 : ℕ) * x1 ∧ (x4 - x3) ^ (2 : ℕ) ≤ (2 : ℕ) * x1) ↔
        ∃ x3 ≤ x1, x3 ≤ (x1 / (2 : ℕ)).sqrt ∧ x2 (x1 - x3) ∧ x2 (x1 + x3) := by
  intro x1 x2
  constructor
  · rintro ⟨a, b, ha, hb, hab, h₁, h₂⟩
    by_cases hle : a ≤ b
    · have hk : b - a = 2 * (x1 - a) := by omega
      have hsq : (2 * (x1 - a)) ^ 2 ≤ 2 * x1 := by rw [← hk]; exact h₂
      have hhalf : 2 * (x1 - a) ^ 2 ≤ x1 := by nlinarith
      refine ⟨x1 - a, by omega, ?_, ?_, ?_⟩
      · rw [Nat.le_sqrt']
        have : (x1 - a) ^ 2 * 2 ≤ x1 := by omega
        exact (Nat.le_div_iff_mul_le (by norm_num)).mpr this
      · have : x1 - (x1 - a) = a := by omega
        rw [this]; exact ha
      · have : x1 + (x1 - a) = b := by omega
        rw [this]; exact hb
    · have hk : a - b = 2 * (x1 - b) := by omega
      have hsq : (2 * (x1 - b)) ^ 2 ≤ 2 * x1 := by rw [← hk]; exact h₁
      have hhalf : 2 * (x1 - b) ^ 2 ≤ x1 := by nlinarith
      refine ⟨x1 - b, by omega, ?_, ?_, ?_⟩
      · rw [Nat.le_sqrt']
        have : (x1 - b) ^ 2 * 2 ≤ x1 := by omega
        exact (Nat.le_div_iff_mul_le (by norm_num)).mpr this
      · have : x1 - (x1 - b) = b := by omega
        rw [this]; exact hb
      · have : x1 + (x1 - b) = a := by omega
        rw [this]; exact ha
  · rintro ⟨k, hk₁, hk₂, hk₃, hk₄⟩
    have hsq : k ^ 2 ≤ x1 / 2 := (Nat.le_sqrt').mp hk₂
    have hmul : 2 * k ^ 2 ≤ x1 := by
      have := (Nat.le_div_iff_mul_le (by norm_num : (0 : ℕ) < 2)).mp hsq
      omega
    refine ⟨x1 - k, x1 + k, hk₃, hk₄, by omega, ?_, ?_⟩
    · have hzero : x1 - k - (x1 + k) = 0 := by omega
      rw [hzero]
      omega
    · have htwo : x1 + k - (x1 - k) = 2 * k := by omega
      rw [htwo]
      nlinarith
