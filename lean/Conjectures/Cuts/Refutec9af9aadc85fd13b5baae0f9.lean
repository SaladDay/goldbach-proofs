import Mathlib

/-!
Refutation of the statement of L-goldbach-cut-f41aaf07e0e1ef5a506d6fa0.

The statement is `∀ x1 ≤ 10 ^ 12, Even x1 → ∃ x4 x5 x6, 1 ≤ x4 ∧ ((2 : ℕ) ^ x4) ^ 2 ≤ x1 ∧ ...`.
`Even` is Mathlib's `Even` (`∃ r, x1 = r + r`), so `x1 = 2` satisfies the two hypotheses
(`2 ≤ 10 ^ 12` and `Even 2`), but the existential is empty: `1 ≤ x4` forces `2 ≤ 2 ^ x4`,
hence `4 ≤ (2 ^ x4) ^ 2`, which cannot be `≤ 2`.

Hence the negation of the statement is provable.
-/

theorem refutation :
    ¬ (∀ x1 ≤ (10 : ℕ) ^ (12 : ℕ), Even x1 → ∃ (x4 : ℕ) (x5 : ℕ) (x6 : ℕ),
      (1 : ℕ) ≤ x4 ∧ ((2 : ℕ) ^ x4) ^ (2 : ℕ) ≤ x1 ∧ Nat.Prime x5 ∧ Nat.Prime x6 ∧
      x1 = x5 + x6 + (2 : ℕ) ^ x4 ∧ x5 + x6 ≤ (3 : ℕ) * x5 ∧
      (3 : ℕ) * x5 ≤ (2 : ℕ) * (x5 + x6)) := by
  intro h
  have h2 : (2 : ℕ) ≤ (10 : ℕ) ^ (12 : ℕ) := by decide
  have hev : Even (2 : ℕ) := ⟨1, by ring⟩
  obtain ⟨x4, x5, x6, hx4, hle, _⟩ := h 2 h2 hev
  have h2le : (2 : ℕ) ≤ 2 ^ x4 := by
    have : 2 ^ 1 ≤ 2 ^ x4 := Nat.pow_le_pow_right (by decide) hx4
    simpa using this
  have h4 : (4 : ℕ) ≤ ((2 : ℕ) ^ x4) ^ (2 : ℕ) := by
    have := Nat.mul_self_le_mul_self h2le
    simpa [pow_two] using this
  omega

theorem Conjectures.Cuts.Refutec9af9aadc85fd13b5baae0f9 : ¬ (∀ x1 ≤ (10 : ℕ) ^ (12 : ℕ), Even x1 → ∃ (x4 : ℕ) (x5 : ℕ) (x6 : ℕ), (1 : ℕ) ≤ x4 ∧ ((2 : ℕ) ^ x4) ^ (2 : ℕ) ≤ x1 ∧ Nat.Prime x5 ∧ Nat.Prime x6 ∧ x1 = x5 + x6 + (2 : ℕ) ^ x4 ∧ x5 + x6 ≤ (3 : ℕ) * x5 ∧ (3 : ℕ) * x5 ≤ (2 : ℕ) * (x5 + x6)) := by
  first
  | exact refutation
