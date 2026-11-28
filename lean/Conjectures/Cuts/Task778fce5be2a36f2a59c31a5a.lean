import Mathlib
import Conjectures.Goldbach.LowSkirtFromShortProgressions

open Finset MeasureTheory
open GoldbachExplicitModeledMajor
  (phase cutoff kernel kernelMass ram coefficient kernelMass_mono cutoff_positive)

noncomputable def Task778fce5be2a36f2a59c31a5a_wideWidth (n q : ℕ) : ℝ :=
  (cutoff n : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) / ((q : ℝ) * (n : ℝ))

noncomputable def Task778fce5be2a36f2a59c31a5a_band (n B : ℕ) : ℂ :=
  ∑ q ∈ Finset.Ioc (cutoff n) B,
    ∑ a ∈ (Finset.range (q + 1)).filter (fun a => a.Coprime q),
      ∫ t in (0 : ℝ)..(1 : ℝ),
        ({x : ℝ | |x - (a : ℝ) / (q : ℝ)| ≤
            Task778fce5be2a36f2a59c31a5a_wideWidth n q} ∩ Set.Ioc (0 : ℝ) (1 : ℝ)).indicator
          (fun x => ((↑((ArithmeticFunction.moebius : ℕ → ℤ) q) : ℂ) / (q.totient : ℂ) *
            kernel n (x - (a : ℝ) / (q : ℝ))) ^ 2 * phase (-(n : ℝ) * x)) t

noncomputable def Task778fce5be2a36f2a59c31a5a_model (n : ℕ) : ℂ :=
  Task778fce5be2a36f2a59c31a5a_band n ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊

theorem Task778fce5be2a36f2a59c31a5a_wideWidth_nonneg (n q : ℕ) :
    0 ≤ Task778fce5be2a36f2a59c31a5a_wideWidth n q := by
  unfold Task778fce5be2a36f2a59c31a5a_wideWidth
  positivity

theorem Task778fce5be2a36f2a59c31a5a_wideWidth_antitone (n : ℕ) (hn : 1 ≤ n) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i ≤ j) :
    Task778fce5be2a36f2a59c31a5a_wideWidth n j ≤
      Task778fce5be2a36f2a59c31a5a_wideWidth n i := by
  unfold Task778fce5be2a36f2a59c31a5a_wideWidth
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnum : (0 : ℝ) ≤ (cutoff n : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) := by positivity
  have hden : (i : ℝ) * (n : ℝ) ≤ (j : ℝ) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hij) hnR.le
  exact div_le_div_of_nonneg_left hnum (by positivity) hden

theorem Task778fce5be2a36f2a59c31a5a_kernelMass_nonneg (n : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ kernelMass n b := by
  unfold kernelMass
  apply intervalIntegral.integral_nonneg
  · linarith
  · intro t _
    positivity

theorem Task778fce5be2a36f2a59c31a5a_mass_antitone (n : ℕ) (hn : 1 ≤ n) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i ≤ j) :
    kernelMass n (Task778fce5be2a36f2a59c31a5a_wideWidth n j) ≤
      kernelMass n (Task778fce5be2a36f2a59c31a5a_wideWidth n i) :=
  kernelMass_mono (Task778fce5be2a36f2a59c31a5a_wideWidth_nonneg n j)
    (Task778fce5be2a36f2a59c31a5a_wideWidth_antitone n hn hi hij) n

theorem Task778fce5be2a36f2a59c31a5a_indicator_eq {c W : ℝ} (h1 : 0 < c - W) (h2 : c + W ≤ 1) :
    ({x : ℝ | |x - c| ≤ W} ∩ Set.Ioc (0 : ℝ) (1 : ℝ)) = Set.Icc (c - W) (c + W) := by
  ext t
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ioc]
  constructor
  · rintro ⟨habs, _, _⟩
    rw [abs_le] at habs
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩
    refine ⟨?_, by linarith, by linarith⟩
    rw [abs_le]
    constructor <;> linarith

theorem Task778fce5be2a36f2a59c31a5a_phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem Task778fce5be2a36f2a59c31a5a_phase_nat (k : ℕ) : phase (k : ℝ) = 1 := by
  unfold phase
  have h : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_nat_mul_two_pi_mul_I]

theorem Task778fce5be2a36f2a59c31a5a_kernel_periodic (n : ℕ) (β : ℝ) :
    kernel n (β + 1) = kernel n β := by
  unfold kernel
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_add, Task778fce5be2a36f2a59c31a5a_phase_add, mul_one,
    Task778fce5be2a36f2a59c31a5a_phase_nat, mul_one]

theorem Task778fce5be2a36f2a59c31a5a_eventual_width_fit_aux_pow (k : ℕ) (hk : 20 ≤ k) :
    k ^ 4 + 2 ≤ 2 ^ k := by
  refine Nat.le_induction (m := 20) (motive := fun k _ => k ^ 4 + 2 ≤ 2 ^ k) ?_ ?_ k hk
  · norm_num
  · intro k hk ih
    have h1 : (k + 1) * 6 ≤ k * 7 := by omega
    have h2 : ((k + 1) * 6) ^ 4 ≤ (k * 7) ^ 4 := Nat.pow_le_pow_left h1 4
    rw [Nat.mul_pow, Nat.mul_pow] at h2
    have h3 : k ^ 4 * 7 ^ 4 ≤ k ^ 4 * (2 * 6 ^ 4) :=
      Nat.mul_le_mul_left (k ^ 4) (by norm_num)
    have h4 : (k + 1) ^ 4 * 6 ^ 4 ≤ 2 * k ^ 4 * 6 ^ 4 := by
      calc (k + 1) ^ 4 * 6 ^ 4 ≤ k ^ 4 * 7 ^ 4 := h2
        _ ≤ k ^ 4 * (2 * 6 ^ 4) := h3
        _ = 2 * k ^ 4 * 6 ^ 4 := by ring
    have h5 : (k + 1) ^ 4 ≤ 2 * k ^ 4 := le_of_mul_le_mul_right h4 (by norm_num)
    calc (k + 1) ^ 4 + 2 ≤ 2 * k ^ 4 + 2 := Nat.add_le_add_right h5 2
      _ ≤ 2 * (k ^ 4 + 2) := by omega
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (k + 1) := by rw [pow_succ]; ring

theorem Task778fce5be2a36f2a59c31a5a_eventual_width_fit :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (cutoff n : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) < (n : ℝ) := by
  refine ⟨2 ^ 20, fun n hn => ?_⟩
  have hk : 20 ≤ Nat.log 2 (n + 2) :=
    (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)
  have hk4 : (Nat.log 2 (n + 2)) ^ 4 + 2 ≤ 2 ^ Nat.log 2 (n + 2) :=
    Task778fce5be2a36f2a59c31a5a_eventual_width_fit_aux_pow _ hk
  have hpow : 2 ^ Nat.log 2 (n + 2) ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
  have hcut2 : (cutoff n) ^ 2 ≤ n := by
    dsimp [cutoff]
    rw [← pow_mul]
    norm_num
    omega
  have hcut2R : ((cutoff n : ℝ)) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hcut2
  have hcR : (0 : ℝ) ≤ (cutoff n : ℝ) := by positivity
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    have hn1' : 1 < n := by omega
    exact_mod_cast hn1'
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hhalf : (cutoff n : ℝ) ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
    have h1 : ((cutoff n : ℝ) ^ 2) ^ (1 / 2 : ℝ) = (cutoff n : ℝ) := by
      rw [← Real.rpow_natCast ((cutoff n : ℝ)) 2, ← Real.rpow_mul hcR]
      norm_num [Real.rpow_one]
    rw [← h1]
    exact Real.rpow_le_rpow (by positivity) hcut2R (by norm_num)
  have hsum : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) = (n : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have hlt : (n : ℝ) ^ (2 / 3 : ℝ) < (n : ℝ) := by
    have h2 : (n : ℝ) ^ (2 / 3 : ℝ) < (n : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt hn1 (by norm_num)
    simpa using h2
  calc (cutoff n : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ)
      ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) :=
        mul_le_mul_of_nonneg_right hhalf (by positivity)
    _ = (n : ℝ) ^ (2 / 3 : ℝ) := hsum
    _ < (n : ℝ) := hlt

theorem Task778fce5be2a36f2a59c31a5a_integral_indicator_Icc (a b : ℝ) (f : ℝ → ℂ)
    (hab : a ≤ b) (ha : 0 < a) (hb : b ≤ 1) :
    (∫ t in (0 : ℝ)..(1 : ℝ), (Set.Icc a b).indicator f t) = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le hab]
  rw [setIntegral_indicator measurableSet_Icc]
  have hset : Set.Ioc (0 : ℝ) 1 ∩ Set.Icc a b = Set.Icc a b := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc]
    constructor
    · rintro ⟨_, h2⟩
      exact h2
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by linarith, by linarith⟩, h1, h2⟩
  rw [hset]
  have hae : (Set.Icc a b : Set ℝ) =ᵐ[volume] Set.Ioc a b := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · have hsub : Set.Icc a b \ Set.Ioc a b = ({a} : Set ℝ) := by
        ext t
        simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioc, Set.mem_singleton_iff]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          by_contra hne
          exact h3 ⟨lt_of_le_of_ne h1 (Ne.symm hne), h2⟩
        · rintro rfl
          refine ⟨⟨le_rfl, hab⟩, ?_⟩
          rintro ⟨hlt, _⟩
          linarith
      rw [hsub]
      exact Real.volume_singleton
    · have hsub : Set.Ioc a b \ Set.Icc a b = (∅ : Set ℝ) := by
        ext t
        simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioc, Set.mem_empty_iff_false]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact h3 ⟨le_of_lt h1, h2⟩
        · intro h
          exact absurd h (by simp)
      rw [hsub]
      simp
  exact setIntegral_congr_set hae

theorem Task778fce5be2a36f2a59c31a5a_window_integral (n : ℕ) (c b : ℝ) (z : ℂ) (hb : 0 ≤ b) :
    (∫ t in c - b..c + b, (z * kernel n (t - c)) ^ 2 * phase (-(n : ℝ) * t)) =
      z ^ 2 * phase (-(n : ℝ) * c) * ((kernelMass n b : ℝ) : ℂ) := by
  have ht := intervalIntegral.integral_comp_add_left
    (fun t => (z * kernel n (t - c)) ^ 2 * phase (-(n : ℝ) * t)) (a := -b) (b := b) c
  rw [sub_eq_add_neg, ← ht]
  calc
    _ = ∫ x in -b..b, (z ^ 2 * phase (-(n : ℝ) * c)) * ((‖kernel n x‖ ^ 2 : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp only
      rw [add_sub_cancel_left, mul_add, Task778fce5be2a36f2a59c31a5a_phase_add,
        ← GoldbachExplicitModeledMajor.windowKernelSquare]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
      rfl

theorem Task778fce5be2a36f2a59c31a5a_ram_one_eq_moebius (q : ℕ) :
    ram q 1 = ((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  refine Nat.recOnPosPrimePosCoprime
    (motive := fun q => ram q 1 = ((ArithmeticFunction.moebius q : ℤ) : ℂ)) ?_ ?_ ?_ ?_ q
  · intro p n hp hn
    rw [ArithmeticFunction.moebius_apply_prime_pow hp hn.ne']
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [GoldbachExplicitModeledMajor.ram_primePower p j 1 hp]
    have hnd : ∀ k : ℕ, k ≠ 0 → ¬ p ^ k ∣ 1 := by
      intro k hk h
      have h1 : p ^ k = 1 := Nat.dvd_one.mp h
      have h2 : 1 < p ^ k := Nat.one_lt_pow hk hp.one_lt
      omega
    rw [ite_eq_right (hnd (j + 1) (Nat.succ_ne_zero j))]
    cases j with
    | zero => simp
    | succ k => simp [hnd (k + 1) (Nat.succ_ne_zero k)]
  · simp [ram, ArithmeticFunction.moebius_eq_zero_of_not_squarefree not_squarefree_zero]
  · rw [GoldbachExplicitModeledMajor.ram_one 1, ArithmeticFunction.moebius_apply_one]
    simp
  · intro a b ha hb hab ha' hb'
    rw [GoldbachExplicitModeledMajor.ram_mul (by omega) (by omega) hab 1, ha', hb',
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab]
    push_cast
    ring

theorem Task778fce5be2a36f2a59c31a5a_coefficient_sum_aux_phase_star (x : ℝ) :
    starRingEnd ℂ (phase x) = phase (-x) := by
  unfold phase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem Task778fce5be2a36f2a59c31a5a_coefficient_sum_aux_ram_one (q : ℕ) :
    ram q 1 = ((ArithmeticFunction.moebius : ℕ → ℤ) q : ℂ) := by
  induction q using Nat.recOnPrimeCoprime with
  | zero => simp [ram]
  | prime_pow p j hp =>
    cases j with
    | zero => simp [GoldbachExplicitModeledMajor.ram_one]
    | succ k =>
      have hd (a : ℕ) : ¬ p ^ (a + 1) ∣ 1 := by
        intro ha
        exact (Nat.one_lt_pow (Nat.succ_ne_zero a) hp.one_lt).ne' (Nat.dvd_one.mp ha)
      rw [GoldbachExplicitModeledMajor.ram_primePower p k 1 hp,
        ArithmeticFunction.moebius_apply_prime_pow hp (Nat.succ_ne_zero k),
        ite_eq_right (hd k)]
      cases k with
      | zero => norm_num
      | succ k => simp [hd k]
  | coprime q r hq hr hqr iq ir =>
    rw [GoldbachExplicitModeledMajor.ram_mul (by omega) (by omega) hqr, iq, ir,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hqr, Int.cast_mul]

theorem Task778fce5be2a36f2a59c31a5a_coefficient_sum (n q : ℕ) (hq : 2 ≤ q) :
    (∑ a ∈ (Finset.range (q + 1)).filter (fun a => a.Coprime q),
        ((↑((ArithmeticFunction.moebius : ℕ → ℤ) q) : ℂ) / (q.totient : ℂ)) ^ 2 *
          phase (-(n : ℝ) * ((a : ℝ) / (q : ℝ)))) = coefficient q n := by
  have hset : (Finset.range (q + 1)).filter (fun a => a.Coprime q) =
      (Finset.range q).filter (fun a => a.Coprime q) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨fun ⟨ha, hcop⟩ => ⟨?_, hcop⟩, fun ⟨ha, hcop⟩ => ⟨by omega, hcop⟩⟩
    by_contra hge
    have haq : a = q := by omega
    rw [haq] at hcop
    have h1 : Nat.gcd q q = 1 := hcop.gcd_eq_one
    rw [Nat.gcd_self] at h1
    omega
  have hmain : (∑ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
        phase (-(n : ℝ) * ((a : ℝ) / (q : ℝ)))) = starRingEnd ℂ (ram q n) := by
    unfold ram
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [Task778fce5be2a36f2a59c31a5a_coefficient_sum_aux_phase_star]
    congr 1
    ring
  unfold coefficient
  rw [hset, ← Finset.mul_sum, hmain,
    Task778fce5be2a36f2a59c31a5a_coefficient_sum_aux_ram_one]

theorem Task778fce5be2a36f2a59c31a5a_parseval_kernel (n : ℕ) :
    (∫ t in (0 : ℝ)..(1 : ℝ), ‖kernel n t‖ ^ 2) = (n : ℝ) + 1 := by
  have hpoly : ∀ t : ℝ, GoldbachWindow.poly (n + 1) (fun _ => (1 : ℂ)) t = kernel n t := by
    intro t
    simp only [GoldbachWindow.poly, one_mul]
    rfl
  simp_rw [← hpoly]
  simpa using GoldbachWindow.parseval (n + 1) (fun _ => (1 : ℂ))

theorem Task778fce5be2a36f2a59c31a5a_kernelMass_period_aux_cont (n : ℕ) :
    Continuous (kernel n) := by
  unfold kernel phase
  fun_prop

theorem Task778fce5be2a36f2a59c31a5a_kernelMass_period_aux_shift (f : ℝ → ℝ) (hf : Continuous f)
    (hper : ∀ x : ℝ, f (x + 1) = f x) :
    (∫ x in (-1 : ℝ)..(1 : ℝ), f x) = 2 * ∫ x in (0 : ℝ)..(1 : ℝ), f x := by
  have hshift : (∫ x in (-1 : ℝ)..(0 : ℝ), f (x + 1)) = ∫ x in (0 : ℝ)..(1 : ℝ), f x := by
    rw [intervalIntegral.integral_comp_add_right]
    norm_num
  have hfun : (fun x : ℝ => f (x + 1)) = f := funext hper
  have hneg : (∫ x in (-1 : ℝ)..(0 : ℝ), f x) = ∫ x in (0 : ℝ)..(1 : ℝ), f x := by
    rw [← hshift, hfun]
  have hsplit : (∫ x in (-1 : ℝ)..(1 : ℝ), f x) =
      (∫ x in (-1 : ℝ)..(0 : ℝ), f x) + ∫ x in (0 : ℝ)..(1 : ℝ), f x :=
    (intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _)).symm
  rw [hsplit, hneg]
  ring

theorem Task778fce5be2a36f2a59c31a5a_kernelMass_period (n : ℕ) :
    kernelMass n 1 = 2 * (∫ t in (0 : ℝ)..(1 : ℝ), ‖kernel n t‖ ^ 2) := by
  unfold kernelMass
  refine Task778fce5be2a36f2a59c31a5a_kernelMass_period_aux_shift (fun x => ‖kernel n x‖ ^ 2)
    ((Task778fce5be2a36f2a59c31a5a_kernelMass_period_aux_cont n).norm.pow 2) ?_
  intro x
  rw [Task778fce5be2a36f2a59c31a5a_kernel_periodic n x]

theorem Conjectures.Cuts.Task778fce5be2a36f2a59c31a5a :
    have x1 : ℝ → ℂ := fun (x1 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x1) : ℂ) * Complex.I); have x2 : ℕ → ℕ := fun (x2 : ℕ) => Nat.log (2 : ℕ) (x2 + (2 : ℕ)) ^ (2 : ℕ); have x3 : ℕ → ℕ := fun (x3 : ℕ) => ⌊(↑x3 : ℝ) ^ (1 / 5 : ℝ)⌋₊; have x4 : ℕ → ℂ := fun (x4 : ℕ) => ∑ x5 ∈ Finset.Ioc (x2 x4) (x3 x4), ∑ x6 ∈ Finset.range (x5 + (1 : ℕ)) with x6.Coprime x5, ∫ (x7 : ℝ) in (0 : ℝ)..(1 : ℝ), ({x8 : ℝ | |x8 - (↑x6 : ℝ) / (↑x5 : ℝ)| ≤ (↑(x2 x4) : ℝ) * (↑x4 : ℝ) ^ (1 / 6 : ℝ) / ((↑x5 : ℝ) * (↑x4 : ℝ))} ∩ Set.Ioc (0 : ℝ) (1 : ℝ)).indicator (fun (x8 : ℝ) => ((↑((ArithmeticFunction.moebius : ℕ → ℤ) x5) : ℂ) / (↑x5.totient : ℂ) * ∑ x9 ∈ Finset.range (x4 + (1 : ℕ)), x1 ((↑x9 : ℝ) * (x8 - (↑x6 : ℝ) / (↑x5 : ℝ)))) ^ (2 : ℕ) * x1 (-(↑x4 : ℝ) * x8)) x7; ∀ (x5 : ℝ), (0 : ℝ) < x5 → ∃ (x7 : ℕ), ∀ (x8 : ℕ), x7 ≤ x8 → Even x8 → -(x5 * (↑x8 : ℝ)) ≤ (x4 x8).re := by
  change ∀ (e : ℝ), 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    -(e * (n : ℝ)) ≤ (Task778fce5be2a36f2a59c31a5a_model n).re
  intro e he
  obtain ⟨K₀, hK₀⟩ := GoldbachGRHSignedModel.harmonic_suffix_floor (e / 8) (by positivity)
  obtain ⟨N₁, hN₁⟩ := Task778fce5be2a36f2a59c31a5a_eventual_width_fit
  refine ⟨max (2 ^ K₀ + 1) (max N₁ 4), fun n hn hEven => ?_⟩
  have hnK : 2 ^ K₀ + 1 ≤ n := (le_max_left _ _).trans hn
  have hn1 : N₁ ≤ n := (le_max_left N₁ 4).trans ((le_max_right _ _).trans hn)
  have hn4 : 4 ≤ n := (le_max_right N₁ 4).trans ((le_max_right _ _).trans hn)
  have hnpos : 0 < n := by omega
  have hnone : 1 ≤ n := by omega
  have hcut : K₀ ≤ cutoff n := by
    have hlog : K₀ ≤ Nat.log 2 (n + 2) :=
      (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr (by omega)
    have hl : 1 ≤ Nat.log 2 (n + 2) := Nat.log_pos (by decide) (by omega)
    exact hlog.trans (by dsimp [cutoff]; nlinarith [Nat.mul_le_mul_left (Nat.log 2 (n + 2)) hl])
  have hfit : (cutoff n : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) < (n : ℝ) := hN₁ n hn1
  set B : ℕ := ⌊(n : ℝ) ^ (1 / 5 : ℝ)⌋₊
  set W : ℕ → ℝ := fun q => Task778fce5be2a36f2a59c31a5a_wideWidth n q
  have hW0 : ∀ q, 0 ≤ W q := fun q => Task778fce5be2a36f2a59c31a5a_wideWidth_nonneg n q
  have hWq : ∀ q, 1 ≤ q → W q < 1 / (q : ℝ) := by
    intro q hq1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have h : W q * ((q : ℝ) * (n : ℝ)) = (cutoff n : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) := by
      dsimp [W, Task778fce5be2a36f2a59c31a5a_wideWidth]
      field_simp
    have h2 : W q * ((q : ℝ) * (n : ℝ)) < (n : ℝ) := h ▸ hfit
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [h2]

  have hband : Task778fce5be2a36f2a59c31a5a_band n B =
      ∑ q ∈ Finset.Ioc (cutoff n) B,
        ∑ a ∈ (Finset.range (q + 1)).filter (fun a => a.Coprime q),
          ((↑((ArithmeticFunction.moebius : ℕ → ℤ) q) : ℂ) / (q.totient : ℂ)) ^ 2 *
            phase (-(n : ℝ) * ((a : ℝ) / (q : ℝ))) * ((kernelMass n (W q) : ℝ) : ℂ) := by
    unfold Task778fce5be2a36f2a59c31a5a_band
    apply Finset.sum_congr rfl
    intro q hq
    have hq2 : 2 ≤ q := by
      have := (Finset.mem_Ioc.mp hq).1
      have := cutoff_positive n
      omega
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    apply Finset.sum_congr rfl
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    have hcop : a.Coprime q := ha'.2
    have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with rfl | h
      · have h1 : Nat.gcd 0 q = 1 := hcop.gcd_eq_one
        have h2 : Nat.gcd 0 q = q := Nat.gcd_zero_left q
        omega
      · exact h
    have haq : a ≤ q - 1 := by
      have hle : a ≤ q := by have := Finset.mem_range.mp ha'.1; omega
      have hne : a ≠ q := by
        intro heq
        have h1 : a.gcd q = 1 := hcop.gcd_eq_one
        have h2 : a.gcd q = q := by rw [heq]; exact Nat.gcd_self q
        omega
      omega
    have hc1 : (1 : ℝ) / (q : ℝ) ≤ (a : ℝ) / (q : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast ha1) hqpos.le
    have hc2 : (a : ℝ) / (q : ℝ) ≤ 1 - 1 / (q : ℝ) := by
      have haq' : (a : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast (by omega : a + 1 ≤ q)
      have hmul : (1 - 1 / (q : ℝ)) * (q : ℝ) = (q : ℝ) - 1 := by
        field_simp
      rw [div_le_iff₀ hqpos, hmul]
      linarith
    have hpos : 0 < (a : ℝ) / (q : ℝ) - W q := by
      have := hWq q (by omega)
      linarith
    have hle1 : (a : ℝ) / (q : ℝ) + W q ≤ 1 := by
      have := hWq q (by omega)
      linarith
    rw [Task778fce5be2a36f2a59c31a5a_indicator_eq hpos hle1]
    rw [Task778fce5be2a36f2a59c31a5a_integral_indicator_Icc _ _ _
      (by linarith [hW0 q]) hpos hle1]
    exact Task778fce5be2a36f2a59c31a5a_window_integral n ((a : ℝ) / (q : ℝ)) (W q)
      ((↑((ArithmeticFunction.moebius : ℕ → ℤ) q) : ℂ) / (q.totient : ℂ)) (hW0 q)
  have hre : (Task778fce5be2a36f2a59c31a5a_model n).re =
      ∑ q ∈ Finset.Ioc (cutoff n) B, (coefficient q n).re * kernelMass n (W q) := by
    unfold Task778fce5be2a36f2a59c31a5a_model
    rw [hband, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hq2 : 2 ≤ q := by
      have := (Finset.mem_Ioc.mp hq).1
      have := cutoff_positive n
      omega
    rw [← Finset.sum_mul, Task778fce5be2a36f2a59c31a5a_coefficient_sum n q hq2, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    have him : (coefficient q n).im = 0 := by
      rw [BandTail.coeff_real (by omega : 0 < q) n]
      simp
    rw [him]
    ring
  rw [hre]
  by_cases hB : cutoff n ≤ B
  · have hp : ∀ i ≥ cutoff n, i ≤ B → -(e / 8) ≤ ∑ q ∈ Finset.Ioc (cutoff n) i, (coefficient q n).re := by
      intro i hi hiB
      have h := hK₀ (cutoff n) hcut n i hEven hi
      have hq0 : ∀ q ∈ Finset.Ioc (cutoff n) i, 0 < q := by
        intro q hq
        have := (Finset.mem_Ioc.mp hq).1
        have := cutoff_positive n
        omega
      have hsum : (∑ q ∈ Finset.Ioc (cutoff n) i, (coefficient q n).re) =
          ∑ q ∈ Finset.Ioc (cutoff n) i, BandTail.F n q / (q : ℝ) :=
        Finset.sum_congr rfl (fun q hq => GoldbachGRHSignedModel.coefficient_re_eq n q (hq0 q hq))
      rw [hsum]
      exact h
    have hw := BandTail.weighted_prefix_lower (cutoff n) B (fun q => (coefficient q n).re)
      (fun q => kernelMass n (W q)) (e / 8) hB (by positivity)
      (fun i _ => Task778fce5be2a36f2a59c31a5a_kernelMass_nonneg n (hW0 i))
      (fun i hi => Task778fce5be2a36f2a59c31a5a_mass_antitone n hnone
        (by have := cutoff_positive n; omega) (Nat.le_succ i))
      hp
    have hW1 : W (cutoff n) ≤ 1 := by
      dsimp [W, Task778fce5be2a36f2a59c31a5a_wideWidth]
      have hc : (0 : ℝ) < (cutoff n : ℝ) := by
        have := cutoff_positive n; exact_mod_cast (by omega : 0 < cutoff n)
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      have h6 : (n : ℝ) ^ (1 / 6 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hnone) (by norm_num)
      have h6' : (n : ℝ) ^ (1 / 6 : ℝ) ≤ n := by simpa using h6
      rw [div_le_iff₀ (by positivity)]
      have hmul : (cutoff n : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) ≤ (cutoff n : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left h6' hc.le
      nlinarith
    have hmass : kernelMass n (W (cutoff n)) ≤ 2 * ((n : ℝ) + 1) := by
      calc
        kernelMass n (W (cutoff n)) ≤ kernelMass n 1 := kernelMass_mono (hW0 (cutoff n)) hW1 n
        _ = 2 * (∫ t in (0 : ℝ)..(1 : ℝ), ‖kernel n t‖ ^ 2) :=
          Task778fce5be2a36f2a59c31a5a_kernelMass_period n
        _ = 2 * ((n : ℝ) + 1) := by
          rw [Task778fce5be2a36f2a59c31a5a_parseval_kernel n]
    have hfinal : -(e / 8) * kernelMass n (W (cutoff n)) ≤
        ∑ q ∈ Finset.Ioc (cutoff n) B, (coefficient q n).re * kernelMass n (W q) := by
      simpa [mul_comm] using hw
    have hnn : (1 : ℝ) ≤ n := by exact_mod_cast hnone
    nlinarith [hfinal, hmass, he, hnn]
  · have hempty : Finset.Ioc (cutoff n) B = ∅ := Finset.Ioc_eq_empty (by omega)
    rw [hempty]
    simp only [Finset.sum_empty]
    have : (0 : ℝ) ≤ e * (n : ℝ) := by positivity
    linarith
