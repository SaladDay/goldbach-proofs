import Mathlib

/-!
# `Conjectures.Cuts.Task27ff951ae6c1969a8e366c86`

Swap the two primes of a representation `x1 = p + q + ∑ i : Fin 5, 2 ^ (e i + 1)`
so that the second prime is at most the first.  The power sum and the equation are
carried over verbatim from the hypothesis; only the order of the two prime summands
is commuted, and the two primes are ordered by a case split on `x2 ≤ x3`.
-/

theorem Conjectures.Cuts.Task27ff951ae6c1969a8e366c86 :
    ∀ (x1 x2 x3 : ℕ), Nat.Prime x2 → Nat.Prime x3 → ∀ (x6 : Fin (5 : ℕ) → ℕ), x1 = x2 + x3 + ∑ x7 : Fin (5 : ℕ), (2 : ℕ) ^ (x6 x7 + (1 : ℕ)) → ∃ (x8 : ℕ) (x9 : ℕ), Nat.Prime x8 ∧ Nat.Prime x9 ∧ ∃ (x10 : Fin (5 : ℕ) → ℕ), x1 = x8 + x9 + ∑ x11 : Fin (5 : ℕ), (2 : ℕ) ^ (x10 x11 + (1 : ℕ)) ∧ x9 ≤ x8 := by
  intro x1 x2 x3 hp2 hp3 x6 heq
  by_cases h : x2 ≤ x3
  · refine ⟨x3, x2, hp3, hp2, x6, ?_, h⟩
    rw [heq, add_comm x2 x3]
  · refine ⟨x2, x3, hp2, hp3, x6, heq, ?_⟩
    omega
