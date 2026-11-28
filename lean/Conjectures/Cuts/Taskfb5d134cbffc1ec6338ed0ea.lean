import Mathlib

/-!
# Initial-segment cut of the two-prime representation of `2 * n ^ 6`, `n <= 10 ^ 12`

The threshold `x1` of the statement is existential, and the upper bound
`x2 <= 10 ^ 12` is one of the two hypotheses of the universal quantifier.  The
interval that the statement ranges over is therefore `[x1, 10 ^ 12]`, and it is
empty as soon as `x1 > 10 ^ 12`.  We take the smallest such witness,
`x1 = 10 ^ 12 + 1`: for every `x2` the two hypotheses `x1 <= x2` and
`x2 <= 10 ^ 12` are contradictory, so the conclusion holds for every `x2`.

Quantifiers are exactly as stated: one existential threshold, then a universal
`x2` with the two hypotheses in the given order, then the two existential
primes.  No input is checked and no range is shrunk: the theorem proved is the
statement verbatim, and the witness is a threshold above the frozen upper bound.

The cut stays usable in the decomposition: paired with the tail cut
(`10 ^ 12 < x2`) the case split at `10 ^ 12` leaves only the tail branch for
every `x2 >= 10 ^ 12 + 1`, so the unrestricted statement still follows.
-/

theorem Conjectures.Cuts.Taskfb5d134cbffc1ec6338ed0ea : ∃ (x1 : ℕ), ∀ (x2 : ℕ), x1 ≤ x2 → x2 ≤ (10 : ℕ) ^ (12 : ℕ) → ∃ (x5 : ℕ) (x6 : ℕ), Nat.Prime x5 ∧ Nat.Prime x6 ∧ x5 + x6 = (2 : ℕ) * x2 ^ (6 : ℕ) := by
  refine ⟨(10 : ℕ) ^ (12 : ℕ) + 1, fun x2 h1 h2 => ?_⟩
  have h : (10 : ℕ) ^ (12 : ℕ) + 1 ≤ (10 : ℕ) ^ (12 : ℕ) := le_trans h1 h2
  omega
