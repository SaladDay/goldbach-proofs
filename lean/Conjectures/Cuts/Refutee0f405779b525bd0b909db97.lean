import Mathlib

theorem refutation_main : ¬ (∀ x1 ≤ (10 : ℕ) ^ (12 : ℕ), Even x1 → ∃ (x4 : ℕ) (x5 : ℕ), Nat.Prime x4 ∧ Nat.Prime x5 ∧ (3 : ℕ) * x4 ≤ (2 : ℕ) * x1 ∧ (2 : ℕ) * x1 ≤ (6 : ℕ) * x4 ∧ |(↑x4 : ℤ) + (↑x5 : ℤ) - (↑x1 : ℤ)| ≤ (2 : ℤ)) := by
  intro h
  have hzero : (0 : ℕ) ≤ (10 : ℕ) ^ (12 : ℕ) := by norm_num
  have h0 := h 0 hzero ⟨0, rfl⟩
  obtain ⟨x4, x5, hp4, hp5, hle, hge, habs⟩ := h0
  have htwo : 2 ≤ x4 := hp4.two_le
  omega

theorem Conjectures.Cuts.Refutee0f405779b525bd0b909db97 : ¬ (∀ x1 ≤ (10 : ℕ) ^ (12 : ℕ), Even x1 → ∃ (x4 : ℕ) (x5 : ℕ), Nat.Prime x4 ∧ Nat.Prime x5 ∧ (3 : ℕ) * x4 ≤ (2 : ℕ) * x1 ∧ (2 : ℕ) * x1 ≤ (6 : ℕ) * x4 ∧ |(↑x4 : ℤ) + (↑x5 : ℤ) - (↑x1 : ℤ)| ≤ (2 : ℤ)) := by
  first
  | exact refutation_main
