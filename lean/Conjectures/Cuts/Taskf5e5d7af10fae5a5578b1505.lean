import Mathlib

namespace Conjectures.Cuts.Taskf5e5d7af10fae5a5578b1505_aux

/-- For a nonzero `m`, the prime-factor list of `m` has length at most one
exactly when `m = 1` or `m` is prime. -/
lemma length_primeFactorsList_le_one {m : ℕ} (hm : m ≠ 0) :
    m.primeFactorsList.length ≤ 1 ↔ m = 1 ∨ Nat.Prime m := by
  constructor
  · intro h
    have hcases : m.primeFactorsList.length = 0 ∨ m.primeFactorsList.length = 1 := by omega
    rcases hcases with h0 | h1
    · have hnil : m.primeFactorsList = [] := List.length_eq_zero_iff.mp h0
      rcases (Nat.primeFactorsList_eq_nil m).mp hnil with hzero | hone
      · exact absurd hzero hm
      · exact Or.inl hone
    · have hcard : ArithmeticFunction.cardFactors m = 1 := h1
      exact Or.inr (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp hcard)
  · rintro (rfl | hp)
    · simp
    · rw [Nat.primeFactorsList_prime hp]
      simp

/-- Splitting off the least prime factor of `n ≥ 2`. -/
lemma primeFactorsList_eq_minFac_cons {n : ℕ} (hn : 2 ≤ n) :
    n.primeFactorsList = n.minFac :: (n / n.minFac).primeFactorsList := by
  have h := Nat.primeFactorsList_add_two (n - 2)
  have hsub : n - 2 + 2 = n := Nat.sub_add_cancel hn
  rw [hsub] at h
  exact h

/-- The cofactor left after removing the least prime factor of `n ≥ 2` is nonzero. -/
lemma div_minFac_ne_zero {n : ℕ} (hn : 2 ≤ n) : n / n.minFac ≠ 0 := by
  intro h0
  have hmul : n / n.minFac * n.minFac = n := Nat.div_mul_cancel (Nat.minFac_dvd n)
  rw [h0, zero_mul] at hmul
  omega

end Conjectures.Cuts.Taskf5e5d7af10fae5a5578b1505_aux

theorem Conjectures.Cuts.Taskf5e5d7af10fae5a5578b1505 :
    ∀ (x1 : ℕ), (2 : ℕ) ≤ x1 → (x1.primeFactorsList.length ≤ (2 : ℕ) ↔ x1 / x1.minFac = (1 : ℕ) ∨ Nat.Prime (x1 / x1.minFac)) := by
  intro x1 hx
  have hsplit := Conjectures.Cuts.Taskf5e5d7af10fae5a5578b1505_aux.primeFactorsList_eq_minFac_cons hx
  have hm := Conjectures.Cuts.Taskf5e5d7af10fae5a5578b1505_aux.div_minFac_ne_zero hx
  rw [hsplit, List.length_cons]
  have hiff := Conjectures.Cuts.Taskf5e5d7af10fae5a5578b1505_aux.length_primeFactorsList_le_one hm
  constructor
  · intro h
    exact hiff.mp (by omega)
  · intro h
    have h1 := hiff.mpr h
    omega
