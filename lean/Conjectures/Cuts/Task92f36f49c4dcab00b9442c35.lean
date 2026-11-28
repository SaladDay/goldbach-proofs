import Mathlib

/-- Swapping the two primes turns a `p ≤ q` witness into a `q ≤ p` witness: the
power sum and the equation are unchanged, only the order of the two summands
`x2 + x3` is commuted.  The six-term power sum `∑ x5, 2 ^ (x4 x5 + 1)` and the
index type `Fin 6` are carried over verbatim from the hypothesis. -/
theorem Conjectures.Cuts.Task92f36f49c4dcab00b9442c35 :
    ∀ (x1 : ℕ), (∃ (x2 : ℕ) (x3 : ℕ), Nat.Prime x2 ∧ Nat.Prime x3 ∧ x2 ≤ x3 ∧ ∃ (x4 : Fin (6 : ℕ) → ℕ), x1 = x2 + x3 + ∑ x5 : Fin (6 : ℕ), (2 : ℕ) ^ (x4 x5 + (1 : ℕ))) → ∃ (x3 : ℕ) (x4 : ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧ x4 ≤ x3 ∧ ∃ (x5 : Fin (6 : ℕ) → ℕ), x1 = x3 + x4 + ∑ x6 : Fin (6 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ)) := by
  intro x1 h
  obtain ⟨x2, x3, hp2, hp3, hle, x4, heq⟩ := h
  refine ⟨x3, x2, hp3, hp2, hle, x4, ?_⟩
  rw [heq, add_comm x2 x3]
