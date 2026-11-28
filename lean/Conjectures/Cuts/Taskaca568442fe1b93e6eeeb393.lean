import Mathlib

namespace Conjectures.Cuts

/-- Premise 2/2 of a cut of L-twin-primes-cut-2b5a8c39956bd7392fecdf97:
a natural number, cast to `ℤ`, is always above `-1`. -/
theorem Taskaca568442fe1b93e6eeeb393 :
    ∀ (x1 : ℕ), (-1 : ℤ) < ↑x1 := by
  intro x1
  have h : (0 : ℤ) ≤ (x1 : ℤ) := Nat.cast_nonneg x1
  have h1 : (-1 : ℤ) < 0 := by decide
  exact lt_of_lt_of_le h1 h

end Conjectures.Cuts
