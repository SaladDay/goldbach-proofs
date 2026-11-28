import Mathlib
import Conjectures.Goldbach.ContinuousParseval

/-!
# `Conjectures.Cuts.Taskd0704b2852f060dbae134551`

The phase-cutoff threshold `τ(n) = 1 / (2304 (1 + (log n)²))` times the `L²` energy of the
high-prime exponential sum

  `S(α) = Σ_{k ≤ n, k³ > n, k prime} (log k) e(k α)`

is eventually at most `n / 11520`.

Method (no analytic number theory beyond Chebyshev's elementary bound):

* Parseval on `[0, 1]`: the accepted module `Conjectures.Goldbach.ContinuousParseval` gives
  `∫₀¹ ‖Σ_{k ≤ n} w_k e(kα)‖² dα = Σ_{k ≤ n} w_k²` for real weights `w`.
* With `w_k = log k` on primes `k ≤ n` with `k³ > n` and `0` elsewhere, every nonzero weight
  has `0 ≤ log k ≤ log n`, so `Σ w_k² ≤ (log n) Σ_{p ≤ n} log p = (log n) θ(n)`.
* Chebyshev's bound `θ(n) ≤ (log 4) n` (Mathlib, `Chebyshev.theta_le_log4_mul_x`) gives
  `∫₀¹ ‖S‖² ≤ (log 4) n log n`.
* For `n ≥ 2⁴⁰` we have `log n ≥ 20` and `log 4 ≤ 2`, hence `10 log n ≤ 1 + (log n)²`,
  which is exactly `(1 / (2304 (1 + (log n)²))) · ∫₀¹ ‖S‖² ≤ n / 11520`.

The parity hypothesis `Even x2` is not needed and is left unused.
-/

open scoped BigOperators

namespace Conjectures.Cuts.Taskd0704b2852f060dbae134551_aux

/-- The weight of the high-prime exponential sum at frequency `k`. -/
noncomputable def weight (N k : ℕ) : ℝ :=
  if k ^ (3 : ℕ) ≤ N then 0 else if Nat.Prime k then Real.log (k : ℝ) else 0

/-- The complex coefficient of the frozen statement is the cast of `weight`. -/
theorem coeff_eq (N k : ℕ) :
    (if k ^ (3 : ℕ) ≤ N then ((0 : ℝ) : ℂ)
      else if Nat.Prime k then ((Real.log (k : ℝ) : ℝ) : ℂ) else (0 : ℂ)) =
      ((weight N k : ℝ) : ℂ) := by
  unfold weight
  split_ifs <;> simp

/-- Parseval for the weighted exponential sum, in the shape used below. -/
theorem integral_norm_sq (N : ℕ) :
    (∫ x5 in (0 : ℝ)..(1 : ℝ),
      ‖∑ x6 ∈ Finset.range (N + 1),
        ((weight N x6 : ℝ) : ℂ) *
          Complex.exp (↑((2 : ℝ) * Real.pi * ((x6 : ℝ) * x5)) * Complex.I)‖ ^ (2 : ℕ)) =
      ∑ k ∈ Finset.range (N + 1), (weight N k) ^ 2 :=
  Conjectures.Goldbach.ContinuousParseval N (weight N)

/-- Chebyshev's bound turns the squared coefficients into `n log n`. -/
theorem sum_weight_sq_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range (N + 1), (weight N k) ^ 2 ≤ Real.log 4 * Real.log (N : ℝ) * (N : ℝ) := by
  have h1 : ∑ k ∈ Finset.range (N + 1), (weight N k) ^ 2 ≤
      ∑ k ∈ Finset.range (N + 1), (if Nat.Prime k then (Real.log (k : ℝ)) ^ 2 else 0) := by
    refine Finset.sum_le_sum ?_
    intro k _
    by_cases hp : Nat.Prime k
    · by_cases hk : k ^ (3 : ℕ) ≤ N
      · simp [weight, hp, hk]
        exact sq_nonneg _
      · simp [weight, hp, hk]
    · by_cases hk : k ^ (3 : ℕ) ≤ N
      · simp [weight, hp, hk]
      · simp [weight, hp, hk]
  have h2 : (∑ k ∈ Finset.range (N + 1),
      (if Nat.Prime k then (Real.log (k : ℝ)) ^ 2 else 0)) =
      ∑ p ∈ Nat.primesLE N, (Real.log (p : ℝ)) ^ 2 := by
    rw [Nat.primesLE_eq_filter_range, Finset.sum_filter]
  have h3 : (∑ p ∈ Nat.primesLE N, (Real.log (p : ℝ)) ^ 2) ≤
      Real.log (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro p hp
    have hp' : Nat.Prime p := Nat.prime_of_mem_primesLE hp
    have hple : p ≤ N := Nat.le_of_mem_primesLE hp
    have hp2 : 2 ≤ p := hp'.two_le
    have hlog0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ p))
    have hlogle : Real.log (p : ℝ) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < p)) (by exact_mod_cast hple)
    have hsq : (Real.log (p : ℝ)) ^ 2 = Real.log (p : ℝ) * Real.log (p : ℝ) := by ring
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hlogle hlog0
  have h4 : (∑ p ∈ Nat.primesLE N, Real.log (p : ℝ)) = Chebyshev.theta (N : ℝ) :=
    (Chebyshev.theta_eq_sum_primesLE_log N).symm
  have h5 : Chebyshev.theta (N : ℝ) ≤ Real.log 4 * (N : ℝ) :=
    Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)
  calc ∑ k ∈ Finset.range (N + 1), (weight N k) ^ 2
      ≤ ∑ k ∈ Finset.range (N + 1),
          (if Nat.Prime k then (Real.log (k : ℝ)) ^ 2 else 0) := h1
    _ = ∑ p ∈ Nat.primesLE N, (Real.log (p : ℝ)) ^ 2 := h2
    _ ≤ Real.log (N : ℝ) * ∑ p ∈ Nat.primesLE N, Real.log (p : ℝ) := h3
    _ = Real.log (N : ℝ) * Chebyshev.theta (N : ℝ) := by rw [h4]
    _ ≤ Real.log (N : ℝ) * (Real.log 4 * (N : ℝ)) := by
        refine mul_le_mul_of_nonneg_left h5 ?_
        exact Real.log_nonneg (by exact_mod_cast hN)
    _ = Real.log 4 * Real.log (N : ℝ) * (N : ℝ) := by ring

end Conjectures.Cuts.Taskd0704b2852f060dbae134551_aux

open Conjectures.Cuts.Taskd0704b2852f060dbae134551_aux

theorem Conjectures.Cuts.Taskd0704b2852f060dbae134551 :
    ∃ (x1 : ℕ), ∀ x2 ≥ x1, Even x2 → (1 : ℝ) / ((2304 : ℝ) * ((1 : ℝ) + Real.log ↑x2 ^ (2 : ℕ))) * ∫ (x5 : ℝ) in (0 : ℝ)..(1 : ℝ), ‖∑ x6 ∈ Finset.range (x2 + (1 : ℕ)), (if x6 ^ (3 : ℕ) ≤ x2 then ↑(0 : ℝ) else if Nat.Prime x6 then ↑(Real.log ↑x6) else (0 : ℂ)) * Complex.exp (↑((2 : ℝ) * Real.pi * (↑x6 * x5)) * Complex.I)‖ ^ (2 : ℕ) ≤ ↑x2 / (11520 : ℝ) := by
  refine ⟨(2 : ℕ) ^ (40 : ℕ), ?_⟩
  intro x2 hx2 _
  have hx2' : (2 : ℕ) ^ (40 : ℕ) ≤ x2 := hx2
  have hN1 : 1 ≤ x2 := by
    have : (1 : ℕ) ≤ (2 : ℕ) ^ (40 : ℕ) := by norm_num
    omega
  set L : ℝ := Real.log (x2 : ℝ)
  -- the frozen integrand, rewritten with `weight`
  have hrew : (∫ x5 in (0 : ℝ)..(1 : ℝ),
      ‖∑ x6 ∈ Finset.range (x2 + (1 : ℕ)),
        (if x6 ^ (3 : ℕ) ≤ x2 then ((0 : ℝ) : ℂ)
          else if Nat.Prime x6 then ((Real.log (x6 : ℝ) : ℝ) : ℂ) else (0 : ℂ)) *
          Complex.exp (↑((2 : ℝ) * Real.pi * ((x6 : ℝ) * x5)) * Complex.I)‖ ^ (2 : ℕ)) =
      ∑ k ∈ Finset.range (x2 + 1), (weight x2 k) ^ 2 := by
    have hfun : ∀ t : ℝ, (∑ x6 ∈ Finset.range (x2 + (1 : ℕ)),
        (if x6 ^ (3 : ℕ) ≤ x2 then ((0 : ℝ) : ℂ)
          else if Nat.Prime x6 then ((Real.log (x6 : ℝ) : ℝ) : ℂ) else (0 : ℂ)) *
          Complex.exp (↑((2 : ℝ) * Real.pi * ((x6 : ℝ) * t)) * Complex.I)) =
        ∑ x6 ∈ Finset.range (x2 + (1 : ℕ)),
          ((weight x2 x6 : ℝ) : ℂ) *
            Complex.exp (↑((2 : ℝ) * Real.pi * ((x6 : ℝ) * t)) * Complex.I) := by
      intro t
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [coeff_eq]
    refine (intervalIntegral.integral_congr (fun t _ => ?_)).trans (integral_norm_sq x2)
    rw [hfun t]
  have hsum : ∑ k ∈ Finset.range (x2 + 1), (weight x2 k) ^ 2 ≤
      Real.log 4 * L * (x2 : ℝ) := sum_weight_sq_le x2 hN1
  have hlog4 : Real.log 4 ≤ 2 := by
    have h : Real.log 4 = 2 * Real.log 2 := by
      have := Real.log_pow (2 : ℝ) 2
      norm_num at this
      linarith
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  -- `log x2 ≥ 20` from `x2 ≥ 2 ^ 40`
  have hL20 : 20 ≤ L := by
    have hcast : ((2 : ℕ) ^ (40 : ℕ) : ℝ) ≤ (x2 : ℝ) := by exact_mod_cast hx2'
    have hlog : Real.log ((2 : ℝ) ^ (40 : ℕ)) ≤ Real.log (x2 : ℝ) :=
      Real.log_le_log (by positivity) hcast
    have hpow : Real.log ((2 : ℝ) ^ (40 : ℕ)) = 40 * Real.log 2 := by
      rw [Real.log_pow]
      push_cast
      ring
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
  have hI : (∫ x5 in (0 : ℝ)..(1 : ℝ),
      ‖∑ x6 ∈ Finset.range (x2 + (1 : ℕ)),
        (if x6 ^ (3 : ℕ) ≤ x2 then ((0 : ℝ) : ℂ)
          else if Nat.Prime x6 then ((Real.log (x6 : ℝ) : ℝ) : ℂ) else (0 : ℂ)) *
          Complex.exp (↑((2 : ℝ) * Real.pi * ((x6 : ℝ) * x5)) * Complex.I)‖ ^ (2 : ℕ)) ≤
      2 * L * (x2 : ℝ) := by
    rw [hrew]
    have hx0 : (0 : ℝ) ≤ (x2 : ℝ) := Nat.cast_nonneg x2
    have hL0 : (0 : ℝ) ≤ L := by linarith
    have hstep : Real.log 4 * L ≤ 2 * L := mul_le_mul_of_nonneg_right hlog4 hL0
    have hstep' : Real.log 4 * L * (x2 : ℝ) ≤ 2 * L * (x2 : ℝ) :=
      mul_le_mul_of_nonneg_right hstep hx0
    linarith
  have hI0 : (0 : ℝ) ≤ (∫ x5 in (0 : ℝ)..(1 : ℝ),
      ‖∑ x6 ∈ Finset.range (x2 + (1 : ℕ)),
        (if x6 ^ (3 : ℕ) ≤ x2 then ((0 : ℝ) : ℂ)
          else if Nat.Prime x6 then ((Real.log (x6 : ℝ) : ℝ) : ℂ) else (0 : ℂ)) *
          Complex.exp (↑((2 : ℝ) * Real.pi * ((x6 : ℝ) * x5)) * Complex.I)‖ ^ (2 : ℕ)) := by
    rw [hrew]
    exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have h10 : 10 * L ≤ 1 + L ^ 2 := by nlinarith
  have hD : (0 : ℝ) < (2304 : ℝ) * (1 + L ^ 2) := by positivity
  have hmul : (2304 : ℝ) * (x2 : ℝ) * (10 * L) ≤ (2304 : ℝ) * (x2 : ℝ) * (1 + L ^ 2) :=
    mul_le_mul_of_nonneg_left h10 (by positivity)
  have hfin : (1 : ℝ) / ((2304 : ℝ) * (1 + L ^ 2)) * (2 * L * (x2 : ℝ)) ≤
      (x2 : ℝ) / 11520 := by
    rw [one_div_mul_eq_div, div_le_div_iff₀ hD (by norm_num)]
    have hring : 2 * L * (x2 : ℝ) * 11520 = (2304 : ℝ) * (x2 : ℝ) * (10 * L) := by ring
    linarith
  have hfac : (0 : ℝ) ≤ 1 / ((2304 : ℝ) * (1 + L ^ 2)) := by positivity
  calc (1 : ℝ) / ((2304 : ℝ) * ((1 : ℝ) + Real.log ↑x2 ^ (2 : ℕ))) *
        ∫ x5 in (0 : ℝ)..(1 : ℝ),
          ‖∑ x6 ∈ Finset.range (x2 + (1 : ℕ)),
            (if x6 ^ (3 : ℕ) ≤ x2 then ↑(0 : ℝ)
              else if Nat.Prime x6 then ↑(Real.log ↑x6) else (0 : ℂ)) *
            Complex.exp (↑((2 : ℝ) * Real.pi * (↑x6 * x5)) * Complex.I)‖ ^ (2 : ℕ)
      = (1 : ℝ) / ((2304 : ℝ) * (1 + L ^ 2)) *
        ∫ x5 in (0 : ℝ)..(1 : ℝ),
          ‖∑ x6 ∈ Finset.range (x2 + (1 : ℕ)),
            (if x6 ^ (3 : ℕ) ≤ x2 then ((0 : ℝ) : ℂ)
              else if Nat.Prime x6 then ((Real.log (x6 : ℝ) : ℝ) : ℂ) else (0 : ℂ)) *
            Complex.exp (↑((2 : ℝ) * Real.pi * ((x6 : ℝ) * x5)) * Complex.I)‖ ^ (2 : ℕ) := by
        rfl
    _ ≤ (1 : ℝ) / ((2304 : ℝ) * (1 + L ^ 2)) * (2 * L * (x2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hI hfac
    _ ≤ (x2 : ℝ) / 11520 := hfin
