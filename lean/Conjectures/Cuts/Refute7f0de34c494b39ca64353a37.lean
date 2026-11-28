import Mathlib

/-- The formal statement of L-goldbach-cut-a76d5c7cf53cb5b647311e52, as given. -/
def Target : Prop :=
  ∀ (x1 : ℝ), (0 : ℝ) < x1 → x1 ≤ (1 : ℝ) → ∀ x4 ≤ (10 : ℕ) ^ (12 : ℕ), Even x4 →
    ∃ (x7 : ℕ) (x8 : ℕ), Nat.Prime x7 ∧ Nat.Prime x8 ∧
      ∃ (x9 : Fin (6 : ℕ) → ℕ),
        x4 = x7 + x8 + ∑ x10 : Fin (6 : ℕ), (2 : ℕ) ^ (x9 x10 + (1 : ℕ)) ∧
        (↑(∑ x10 : Fin (6 : ℕ), (2 : ℕ) ^ (x9 x10 + (1 : ℕ))) : ℝ) ≤ (↑x4 : ℝ) ^ x1 ∧
        x8 ≤ x7

/-- Each of the six powers of two is at least 2, so the right-hand side is at least 16,
while `x4 = 2` is even and at most `10 ^ 12`.  Hence the statement as written is false. -/
theorem target_false : ¬ Target := by
  intro h
  obtain ⟨x7, x8, h7, h8, x9, heq, _, _⟩ := h 1 (by norm_num) (by norm_num) 2 (by norm_num) ⟨1, by omega⟩
  have hsum : (12 : ℕ) ≤ ∑ x10 : Fin (6 : ℕ), (2 : ℕ) ^ (x9 x10 + (1 : ℕ)) := by
    have : ∀ x10 : Fin (6 : ℕ), (2 : ℕ) ≤ (2 : ℕ) ^ (x9 x10 + (1 : ℕ)) := by
      intro x10
      have hpos : (1 : ℕ) ≤ x9 x10 + 1 := by omega
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (x9 x10 + 1) := Nat.pow_le_pow_right (by norm_num) hpos
    have h6 : (12 : ℕ) = ∑ _x10 : Fin (6 : ℕ), (2 : ℕ) := by
      simp [Fin.sum_univ_six]
    rw [h6]
    exact Finset.sum_le_sum fun x10 _ => this x10
  have hp7 : (2 : ℕ) ≤ x7 := h7.two_le
  have hp8 : (2 : ℕ) ≤ x8 := h8.two_le
  omega

theorem refute : ¬ (∀ (x1 : ℝ), (0 : ℝ) < x1 → x1 ≤ (1 : ℝ) → ∀ x4 ≤ (10 : ℕ) ^ (12 : ℕ), Even x4 → ∃ (x7 : ℕ) (x8 : ℕ), Nat.Prime x7 ∧ Nat.Prime x8 ∧ ∃ (x9 : Fin (6 : ℕ) → ℕ), x4 = x7 + x8 + ∑ x10 : Fin (6 : ℕ), (2 : ℕ) ^ (x9 x10 + (1 : ℕ)) ∧ (↑(∑ x10 : Fin (6 : ℕ), (2 : ℕ) ^ (x9 x10 + (1 : ℕ))) : ℝ) ≤ (↑x4 : ℝ) ^ x1 ∧ x8 ≤ x7) := by
  exact target_false

theorem Conjectures.Cuts.Refute7f0de34c494b39ca64353a37 : ¬ (∀ (x1 : ℝ), (0 : ℝ) < x1 → x1 ≤ (1 : ℝ) → ∀ x4 ≤ (10 : ℕ) ^ (12 : ℕ), Even x4 → ∃ (x7 : ℕ) (x8 : ℕ), Nat.Prime x7 ∧ Nat.Prime x8 ∧ ∃ (x9 : Fin (6 : ℕ) → ℕ), x4 = x7 + x8 + ∑ x10 : Fin (6 : ℕ), (2 : ℕ) ^ (x9 x10 + (1 : ℕ)) ∧ (↑(∑ x10 : Fin (6 : ℕ), (2 : ℕ) ^ (x9 x10 + (1 : ℕ))) : ℝ) ≤ (↑x4 : ℝ) ^ x1 ∧ x8 ≤ x7) := by
  first
  | exact refute
  | exact target_false
