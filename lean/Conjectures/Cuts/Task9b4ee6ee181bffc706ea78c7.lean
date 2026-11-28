import Mathlib

/-!
# Cut premise: the exceptional Chen endpoint reduces to two linear forms

For `x ≥ 1` the companion endpoint condition that `6x + 3` has at most two prime factors, counted
with multiplicity, is equivalent to `2x + 1` being prime, because `6x + 3 = 3 * (2x + 1)` and the
number of prime factors of a product is additive (`ArithmeticFunction.cardFactors_mul`).

Self-contained: Mathlib only.
-/

namespace Conjectures.Cuts.Task9b4ee6ee181bffc706ea78c7_aux

/-- The number of prime factors (with multiplicity) of `3 * m` is `1` more than that of `m`. -/
private lemma length_mul_three (m : ℕ) (hm : m ≠ 0) :
    (3 * m).primeFactorsList.length = 1 + m.primeFactorsList.length := by
  have h := ArithmeticFunction.cardFactors_mul (m := 3) (n := m) (by norm_num) hm
  rw [ArithmeticFunction.cardFactors_apply, ArithmeticFunction.cardFactors_apply,
    ArithmeticFunction.cardFactors_apply] at h
  have h3 : (3 : ℕ).primeFactorsList.length = 1 := by
    rw [Nat.primeFactorsList_prime Nat.prime_three]
    rfl
  omega

/-- For `n > 1`, having at most one prime factor (with multiplicity) means being prime. -/
private lemma length_le_one_iff_prime {n : ℕ} (hn : 1 < n) :
    n.primeFactorsList.length ≤ 1 ↔ Nat.Prime n := by
  have h1 : 0 < n.primeFactorsList.length := by
    rw [← ArithmeticFunction.cardFactors_apply,
      ArithmeticFunction.cardFactors_pos_iff_one_lt]
    exact hn
  have h2 : n.primeFactorsList.length ≤ 1 ↔ n.primeFactorsList.length = 1 := by omega
  rw [h2, ← ArithmeticFunction.cardFactors_apply, ArithmeticFunction.cardFactors_eq_one_iff_prime]

theorem main (x1 : ℕ) (hx1 : 1 ≤ x1) :
    (Nat.Prime (6 * x1 + 1) ∧ (6 * x1 + 1 + 2).primeFactorsList.length ≤ 2) ↔
      Nat.Prime (6 * x1 + 1) ∧ Nat.Prime (2 * x1 + 1) := by
  have hmul : 6 * x1 + 1 + 2 = 3 * (2 * x1 + 1) := by ring
  have hm0 : 2 * x1 + 1 ≠ 0 := by omega
  have hm1 : 1 < 2 * x1 + 1 := by omega
  have hlen : (6 * x1 + 1 + 2).primeFactorsList.length = 1 + (2 * x1 + 1).primeFactorsList.length := by
    rw [hmul]
    exact length_mul_three _ hm0
  constructor
  · rintro ⟨hp, hlen2⟩
    refine ⟨hp, ?_⟩
    have hle : (2 * x1 + 1).primeFactorsList.length ≤ 1 := by omega
    exact (length_le_one_iff_prime hm1).mp hle
  · rintro ⟨hp, hq⟩
    refine ⟨hp, ?_⟩
    have h1 : (2 * x1 + 1).primeFactorsList.length = 1 := by
      rw [← ArithmeticFunction.cardFactors_apply, ArithmeticFunction.cardFactors_eq_one_iff_prime]
      exact hq
    omega

end Conjectures.Cuts.Task9b4ee6ee181bffc706ea78c7_aux

theorem Conjectures.Cuts.Task9b4ee6ee181bffc706ea78c7 :
    ∀ (x1 : ℕ), (1 : ℕ) ≤ x1 → (Nat.Prime ((6 : ℕ) * x1 + (1 : ℕ)) ∧ ((6 : ℕ) * x1 + (1 : ℕ) + (2 : ℕ)).primeFactorsList.length ≤ (2 : ℕ) ↔ Nat.Prime ((6 : ℕ) * x1 + (1 : ℕ)) ∧ Nat.Prime ((2 : ℕ) * x1 + (1 : ℕ))) := by
  intro x1 hx1
  exact Conjectures.Cuts.Task9b4ee6ee181bffc706ea78c7_aux.main x1 hx1
