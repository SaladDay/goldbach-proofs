import Mathlib

/-- The formal statement of L-goldbach-cut-fe29a5c3fc03666b369419d6, as given. -/
def Target : Prop :=
  ∀ (x1 : ℕ), Even x1 → ∃ (x3 : ℕ) (x4 : ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧
    ∃ (x5 : Fin (6 : ℕ) → ℕ), x1 = x3 + x4 + ∑ x6 : Fin (6 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ))

/-- Each of the six powers of two is at least 2, so the right-hand side is at least 16,
while `x1 = 2` is even.  Hence the statement as written is false. -/
theorem target_false : ¬ Target := by
  intro h
  obtain ⟨x3, x4, h3, h4, x5, heq⟩ := h 2 ⟨1, by omega⟩
  have hsum : (12 : ℕ) ≤ ∑ x6 : Fin (6 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ)) := by
    have : ∀ x6 : Fin (6 : ℕ), (2 : ℕ) ≤ (2 : ℕ) ^ (x5 x6 + (1 : ℕ)) := by
      intro x6
      have hpos : (1 : ℕ) ≤ x5 x6 + 1 := by omega
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (x5 x6 + 1) := Nat.pow_le_pow_right (by norm_num) hpos
    have h6 : (12 : ℕ) = ∑ _x6 : Fin (6 : ℕ), (2 : ℕ) := by
      simp [Fin.sum_univ_six]
    rw [h6]
    exact Finset.sum_le_sum fun x6 _ => this x6
  have hp3 : (2 : ℕ) ≤ x3 := h3.two_le
  have hp4 : (2 : ℕ) ≤ x4 := h4.two_le
  omega

theorem Conjectures.Cuts.Refute0a8870449b4845d1dbce40b0 : ¬ (∀ (x1 : ℕ), Even x1 → ∃ (x3 : ℕ) (x4 : ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧ ∃ (x5 : Fin (6 : ℕ) → ℕ), x1 = x3 + x4 + ∑ x6 : Fin (6 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ))) := by
  first
  | exact target_false
