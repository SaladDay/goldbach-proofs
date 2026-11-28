import Mathlib
import Conjectures.Goldbach.Type2FixedTargetReciprocalError

/-!
The (2,2) transition-band replacement of the von Mangoldt cofactor by the large
prime cofactor, on the deep minor arcs.  The estimate is the accepted
`GoldbachTransitionSquare.transition_power_saving` of
`Conjectures.Goldbach.Type2FixedTargetReciprocalError` (upstream, Apache-2.0),
specialised to the statement's cutoffs and arcs; its `K n^(124/128)` bound is
`o(n)`, which gives the required `ε n` bound eventually.
-/

open Finset MeasureTheory Filter Topology

theorem Conjectures.Cuts.Task9eebbb6afd3d2ba0d112a927 :
    have x1 : ℝ → ℂ := fun (x1 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x1) : ℂ) * Complex.I); have x2 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x2 : ℕ) (x3 : ℕ → ℝ) (x4 : ℝ) => ∑ x5 ∈ Finset.range (x2 + (1 : ℕ)), (↑(x3 x5) : ℂ) * x1 ((↑x5 : ℝ) * x4); have x3 : ℕ → ℕ := fun (x3 : ℕ) => Nat.log (2 : ℕ) (x3 + (2 : ℕ)) ^ (2 : ℕ); have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊(↑x4 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x5 : ℕ → ℕ := fun (x5 : ℕ) => (256 : ℕ) * x4 x5 * x3 x5; have x6 : ℕ → Set ℝ := fun (x6 : ℕ) => {x7 : ℝ | ∃ (x8 : ℕ) (x9 : ℕ), (1 : ℕ) ≤ x8 ∧ x8 ≤ x4 x6 ∧ x9 ≤ x8 ∧ x9.Coprime x8 ∧ |x7 - (↑x9 : ℝ) / (↑x8 : ℝ)| ≤ (↑(x5 x6) : ℝ) / ((↑x8 : ℝ) * (↑x6 : ℝ))}; have x7 : ArithmeticFunction ℝ := ArithmeticFunction.vonMangoldt; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (↑((ArithmeticFunction.moebius : ℕ → ℤ) x8) : ℝ); have x9 : ℕ → ℕ := fun (x9 : ℕ) => ⌊(↑x9 : ℝ) ^ (1 / 16 : ℝ)⌋₊; have x10 : ℕ → ℕ := fun (x10 : ℕ) => ⌊(↑x10 : ℝ) ^ (1 / 4 : ℝ)⌋₊; have x11 : ℕ → ℕ := fun (x11 : ℕ) => ⌊(↑x11 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x12 : ℕ → ℕ → ℝ := fun (x12 x13 : ℕ) => ∑ x14 ∈ x13.divisors with x10 x12 < x14 ∧ x14 ≤ x11 x12 ∧ x9 x12 < x13 / x14, (∑ x15 ∈ x14.divisors with x9 x12 < x15, x8 x15) * (x7 : ℕ → ℝ) (x13 / x14); have x13 : ℕ → ℕ → ℝ := fun (x13 x14 : ℕ) => ∑ x15 ∈ x14.divisors with x10 x13 < x15 ∧ x15 ≤ x11 x13 ∧ x9 x13 < x14 / x15, (∑ x16 ∈ x15.divisors with x9 x13 < x16, x8 x16) * if x13.sqrt < x14 / x15 then if Nat.Prime (x14 / x15) then Real.log (↑(x14 / x15) : ℝ) else (0 : ℝ) else (0 : ℝ); have x14 : ℕ → (ℕ → ℝ) → (ℕ → ℝ) → ℂ := fun (x14 : ℕ) (x15 x16 : ℕ → ℝ) => ∫ (x17 : ℝ) in (0 : ℝ)..(1 : ℝ), (x6 x14)ᶜ.indicator (fun (x18 : ℝ) => x2 x14 x15 x18 * x2 x14 x16 x18 * x1 (-(↑x14 : ℝ) * x18)) x17; ∀ (x15 : ℝ), (0 : ℝ) < x15 → ∃ (x17 : ℕ), ∀ (x18 : ℕ), x17 ≤ x18 → Even x18 → ‖x14 x18 (x12 x18) (x12 x18) - x14 x18 (x13 x18) (x13 x18)‖ ≤ x15 * (↑x18 : ℝ) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ε hε
  obtain ⟨K, hK, hmain⟩ := GoldbachTransitionSquare.transition_power_saving
  have ht : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-(1 / 32 : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := (1 / 32 : ℝ)) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa using (tendsto_const_nhds (x := K)).mul h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually_lt_const hε)
  refine ⟨max N 1, fun n hn _ => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hB : ((x11 n : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hset : x6 n = GoldbachTransitionSquare.wide n (x4 n) (x5 n) := rfl
  have hmeas : MeasurableSet ((x6 n)ᶜ) := by
    rw [hset]
    exact (GoldbachTransitionSquare.wide_measurable n (x4 n) (x5 n)).compl
  have key := hmain n (x9 n) (x10 n) (x11 n) hn1 hB (x6 n)ᶜ hmeas
  have heq : x14 n (x12 n) (x12 n) - x14 n (x13 n) (x13 n) =
      GoldbachTransitionSquare.pairIntegral ((x6 n)ᶜ) n
        (GoldbachTransitionSquare.full n (x9 n) (x10 n) (x11 n))
        (GoldbachTransitionSquare.full n (x9 n) (x10 n) (x11 n)) -
      GoldbachTransitionSquare.pairIntegral ((x6 n)ᶜ) n
        (GoldbachTransitionSquare.core n (x9 n) (x10 n) (x11 n))
        (GoldbachTransitionSquare.core n (x9 n) (x10 n) (x11 n)) := rfl
  rw [heq]
  refine key.trans ?_
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hexp : (124 / 128 : ℝ) = 31 / 32 := by norm_num
  have hpow : (n : ℝ) ^ (124 / 128 : ℝ) = (n : ℝ) * (n : ℝ) ^ (-(1 / 32 : ℝ)) := by
    rw [hexp]
    have h := Real.rpow_add hnpos (1 : ℝ) (-(1 / 32 : ℝ))
    rw [Real.rpow_one] at h
    norm_num at h
    exact h
  have hlt : K * (n : ℝ) ^ (-(1 / 32 : ℝ)) ≤ ε := by
    have h := hN n (by omega)
    exact h.le
  calc
    K * (n : ℝ) ^ (124 / 128 : ℝ) = (K * (n : ℝ) ^ (-(1 / 32 : ℝ))) * (n : ℝ) := by
      rw [hpow]; ring
    _ ≤ ε * (n : ℝ) := mul_le_mul_of_nonneg_right hlt hnpos.le
