import Mathlib
import Conjectures.Goldbach.RhSchoenfeldPsi
import Conjectures.Goldbach.ExplicitPsiSubTheta

/-!
Blueprint for `Conjectures.Cuts.Task3b37bc2419c6ad18e55c6e6b`
(Schoenfeld 1976, Cor. 1: under GRH, `|π x - li x| ≤ √x log x / (8π)` for `x ≥ 4·10^18`).

Route.  The premise gives RH for ζ (modulus 1).  The accepted module
`Conjectures.Goldbach.RhSchoenfeldPsi` does not only prove its final bound
`|ψ x - x| ≤ √x log²x / (8π)`: its exported helpers
`SchoenfeldRH.psi_sub_le_of_RH`, `SchoenfeldRH.sub_psi_le_of_RH` and
`SchoenfeldRH.zeroSumW_le_of_RH` give the sharper parametric estimate
`|ψ n - n| ≤ √n·(log²(√n/π)/(2π) + 3/2) + log²(√n/π)/(2π) + 5/2`  (take `λ = √n ± 1/2`,
so the zero sum is truncated at height `B = √n` and the leading constant is
`log²(√n/π)/(2π) = log²x/(8π)·(1 - 4 log π / log x)²`, i.e. about 10 percent better than
the crude `1/(8π)`).  That slack is what makes the Abel step to π work: the crude bound
alone leaves `1 + 2/log x > 1` of the target, the sharp one leaves about 2 percent.
Then `θ` is reached through `Conjectures.Goldbach.ExplicitPsiSubTheta` (ours), and π through
Mathlib `Chebyshev.primeCounting_eq_theta_div_log_add_integral`.
-/

/-- Sharp pointwise envelope for `|ψ t - t|` under RH, used for `t ≥ 2500`. -/
noncomputable def Task3b37bc2419c6ad18e55c6e6b_psiErr (t : ℝ) : ℝ :=
  (Real.sqrt t + 1) * (Real.log (Real.sqrt t / Real.pi) ^ 2 / (2 * Real.pi) + 3 / 2) + 6

/-- Pointwise envelope for `|θ t - t|` under RH, used for `t ≥ 2500`. -/
noncomputable def Task3b37bc2419c6ad18e55c6e6b_thetaErr (t : ℝ) : ℝ :=
  Task3b37bc2419c6ad18e55c6e6b_psiErr t +
    Real.log 4 * Real.sqrt t + 2 * t ^ (1 / 3 : ℝ) * Real.log t

-- @helper Task3b37bc2419c6ad18e55c6e6b_rh_of_halfplane
theorem Task3b37bc2419c6ad18e55c6e6b_rh_of_halfplane
    (h : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0) : RiemannHypothesis := by
  intro s hzero htriv hs1
  by_contra hre
  rcases lt_or_gt_of_ne hre with hlt | hgt
  swap
  · exact h s hgt hs1 hzero
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hzero
    norm_num at hzero
  have hw : 1 / 2 < (1 - s).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hw1 : 1 - s ≠ 1 := fun h0 => hs0 (by linear_combination -h0)
  have hwn : ∀ n : ℕ, 1 - s ≠ -n := by
    intro n h0
    have := congrArg Complex.re h0
    rw [Complex.neg_re, Complex.natCast_re] at this
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hfe := riemannZeta_one_sub hwn hw1
  rw [sub_sub_cancel, hzero] at hfe
  have hζ : riemannZeta (1 - s) ≠ 0 := h _ hw hw1
  have hΓ : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero hwn
  have hpow : (2 * (Real.pi : ℂ)) ^ (-(1 - s)) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h0 => mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) h0.1
  have hcos : Complex.cos (Real.pi * (1 - s) / 2) = 0 := by
    by_contra hc
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hΓ) hc) hζ
      hfe.symm
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.1 hcos
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hsk : s = -2 * (k : ℂ) := by
    have h3 : (Real.pi : ℂ) * (s + 2 * k) = 0 := by linear_combination -2 * hk
    have h4 := (mul_eq_zero.1 h3).resolve_left hπ
    linear_combination h4
  have hk1 : 1 ≤ k := by
    by_contra hk1
    have hk0 : k ≤ 0 := by omega
    rcases eq_or_lt_of_le hk0 with hk0 | hk0
    · exact hs0 (by simp [hsk, hk0])
    · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      have : s.re = -2 * (k : ℝ) := by simp [hsk]
      linarith
  refine htriv ⟨(k - 1).toNat, ?_⟩
  have hcast : (((k - 1).toNat : ℤ) : ℂ) = ((k - 1 : ℤ) : ℂ) := by
    rw [Int.toNat_of_nonneg (by omega)]
  rw [Int.cast_natCast] at hcast
  rw [hcast, hsk]
  push_cast
  ring
-- @end Task3b37bc2419c6ad18e55c6e6b_rh_of_halfplane

-- @helper Task3b37bc2419c6ad18e55c6e6b_psi_err
theorem Task3b37bc2419c6ad18e55c6e6b_psi_err_aux_nat (hRH : RiemannHypothesis) (n : ℕ) (hn : 2500 ≤ n) :
    |Chebyshev.psi n - (n : ℝ)| ≤
      Real.sqrt n + (Real.sqrt n + 1) *
        (Real.log (Real.sqrt n / Real.pi) ^ 2 / (2 * Real.pi) + 1 / 2) + 4 := by
  have hn' : (2500 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set y := Real.sqrt (n : ℝ)
  have hy : 50 ≤ y := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hy0 : 0 < y := by linarith
  have hyy : y ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  set Z := Real.log (y / Real.pi) ^ 2 / (2 * Real.pi) + 1 / 2
  have hZ0 : 0 ≤ Z := by positivity
  have hWy : 0 ≤ SchoenfeldRH.zeroSumW y := SchoenfeldRH.zeroSumW_nonneg y
  have hZy : y * SchoenfeldRH.zeroSumW y ≤ Z :=
    SchoenfeldRH.zeroSumW_le_of_RH hRH y hy
  have h2 : 2 ≤ n := by omega
  have hUy := SchoenfeldRH.psi_sub_le_of_RH hRH n h2 (y + 1 / 2) (by linarith)
  have hLy := SchoenfeldRH.sub_psi_le_of_RH hRH n h2 (y - 1 / 2) (by linarith)
    (SchoenfeldRH.Large.sqrt_ne n)
  have hsy : Real.sqrt (n : ℝ) = y := rfl
  rw [hsy] at hUy hLy
  have hup : Chebyshev.psi n - (n : ℝ) ≤ y + (y + 1) * Z + 4 := by
    rw [show y + 1 / 2 - 1 / 2 = y by ring] at hUy
    have hd : (n : ℝ) / (y + 1 / 2 - 1) ≤ y + 1 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hm : y * ((y + 1 / 2) * SchoenfeldRH.zeroSumW y) ≤ (y + 1) * Z := by
      have h1 : y * ((y + 1 / 2) * SchoenfeldRH.zeroSumW y) =
          (y + 1 / 2) * (y * SchoenfeldRH.zeroSumW y) := by ring
      rw [h1]
      calc (y + 1 / 2) * (y * SchoenfeldRH.zeroSumW y)
          ≤ (y + 1 / 2) * Z := by gcongr
        _ ≤ (y + 1) * Z := by gcongr; linarith
    linarith
  have hlo : (n : ℝ) - Chebyshev.psi n ≤ y + (y + 1) * Z + 3 := by
    rw [show y - 1 / 2 + 1 / 2 = y by ring] at hLy
    have hd : (n : ℝ) / (y - 1 / 2 + 1) ≤ y := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hm : (y + 1) * ((y - 1 / 2) * SchoenfeldRH.zeroSumW y) ≤ (y + 1) * Z := by
      gcongr
      nlinarith
    linarith
  rw [abs_le]
  have hup' : Chebyshev.psi n - (n : ℝ) ≤
      Real.sqrt n + (Real.sqrt n + 1) *
        (Real.log (Real.sqrt n / Real.pi) ^ 2 / (2 * Real.pi) + 1 / 2) + 4 := by
    dsimp only [y, Z] at hup
    linarith
  have hlo' : (n : ℝ) - Chebyshev.psi n ≤
      Real.sqrt n + (Real.sqrt n + 1) *
        (Real.log (Real.sqrt n / Real.pi) ^ 2 / (2 * Real.pi) + 1 / 2) + 4 := by
    dsimp only [y, Z] at hlo
    linarith
  exact ⟨by linarith, hup'⟩

theorem Task3b37bc2419c6ad18e55c6e6b_psi_err (hRH : RiemannHypothesis) :
    ∀ t : ℝ, 2500 ≤ t →
      |Chebyshev.psi t - t| ≤ Task3b37bc2419c6ad18e55c6e6b_psiErr t := by
  intro t ht
  have ht0 : 0 ≤ t := by linarith
  have hn : 2500 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht)
  have hnx : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
  have hxn : t < ((⌊t⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one t
  have hpsi : Chebyshev.psi t = Chebyshev.psi ⌊t⌋₊ := Chebyshev.psi_eq_psi_coe_floor t
  have h1 := Task3b37bc2419c6ad18e55c6e6b_psi_err_aux_nat hRH ⌊t⌋₊ hn
  have htri : |Chebyshev.psi t - t| ≤ |Chebyshev.psi ⌊t⌋₊ - ((⌊t⌋₊ : ℕ) : ℝ)| + 1 := by
    have hdecomp : Chebyshev.psi t - t =
        (Chebyshev.psi ⌊t⌋₊ - ((⌊t⌋₊ : ℕ) : ℝ)) + (((⌊t⌋₊ : ℕ) : ℝ) - t) := by
      rw [hpsi]; ring
    rw [hdecomp]
    have h := abs_add_le (Chebyshev.psi ⌊t⌋₊ - ((⌊t⌋₊ : ℕ) : ℝ)) (((⌊t⌋₊ : ℕ) : ℝ) - t)
    have h2 : |((⌊t⌋₊ : ℕ) : ℝ) - t| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith
    linarith
  set y := Real.sqrt ((⌊t⌋₊ : ℕ) : ℝ)
  set s := Real.sqrt t
  have hn' : (2500 : ℝ) ≤ ((⌊t⌋₊ : ℕ) : ℝ) := by exact_mod_cast hn
  have hy50 : 50 ≤ y := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith)
  have hys : y ≤ s := Real.sqrt_le_sqrt hnx
  have hlog : Real.log (y / Real.pi) ≤ Real.log (s / Real.pi) :=
    Real.log_le_log (div_pos (by linarith) Real.pi_pos)
      (div_le_div_of_nonneg_right hys Real.pi_pos.le)
  have hlog0 : 0 ≤ Real.log (y / Real.pi) :=
    Real.log_nonneg ((one_le_div Real.pi_pos).mpr (by linarith [Real.pi_lt_four]))
  have hsq : Real.log (y / Real.pi) ^ 2 ≤ Real.log (s / Real.pi) ^ 2 :=
    pow_le_pow_left₀ hlog0 hlog 2
  have hA : Real.log (y / Real.pi) ^ 2 / (2 * Real.pi) ≤
      Real.log (s / Real.pi) ^ 2 / (2 * Real.pi) := by
    have : 0 < 2 * Real.pi := by positivity
    exact div_le_div_of_nonneg_right hsq (by positivity)
  have hA0 : 0 ≤ Real.log (y / Real.pi) ^ 2 / (2 * Real.pi) := by positivity
  have hprod : (y + 1) * (Real.log (y / Real.pi) ^ 2 / (2 * Real.pi)) ≤
      (s + 1) * (Real.log (s / Real.pi) ^ 2 / (2 * Real.pi)) :=
    mul_le_mul (by linarith : y + 1 ≤ s + 1) hA hA0 (by linarith : 0 ≤ s + 1)
  have h1' : |Chebyshev.psi ⌊t⌋₊ - ((⌊t⌋₊ : ℕ) : ℝ)| ≤
      (y + 1) * (Real.log (y / Real.pi) ^ 2 / (2 * Real.pi)) + 3 / 2 * y + 9 / 2 := by
    have heq : y + (y + 1) * (Real.log (y / Real.pi) ^ 2 / (2 * Real.pi) + 1 / 2) + 4 =
        (y + 1) * (Real.log (y / Real.pi) ^ 2 / (2 * Real.pi)) + 3 / 2 * y + 9 / 2 := by ring
    have h1y : |Chebyshev.psi ⌊t⌋₊ - ((⌊t⌋₊ : ℕ) : ℝ)| ≤
        y + (y + 1) * (Real.log (y / Real.pi) ^ 2 / (2 * Real.pi) + 1 / 2) + 4 := h1
    linarith
  unfold Task3b37bc2419c6ad18e55c6e6b_psiErr
  change |Chebyshev.psi t - t| ≤
    (s + 1) * (Real.log (s / Real.pi) ^ 2 / (2 * Real.pi) + 3 / 2) + 6
  have hlin : 3 / 2 * y + 11 / 2 ≤ (s + 1) * (3 / 2) + 6 := by linarith
  have hexp : (s + 1) * (Real.log (s / Real.pi) ^ 2 / (2 * Real.pi) + 3 / 2) =
      (s + 1) * (Real.log (s / Real.pi) ^ 2 / (2 * Real.pi)) + (s + 1) * (3 / 2) := by ring
  rw [hexp]
  linarith
-- @end Task3b37bc2419c6ad18e55c6e6b_psi_err

-- @helper Task3b37bc2419c6ad18e55c6e6b_theta_err
theorem Task3b37bc2419c6ad18e55c6e6b_theta_err (hRH : RiemannHypothesis) :
    ∀ t : ℝ, 2500 ≤ t →
      |Chebyshev.theta t - t| ≤ Task3b37bc2419c6ad18e55c6e6b_thetaErr t := by
  intro t ht
  have h2 : (2 : ℝ) ≤ t := by linarith
  have h := Conjectures.Goldbach.ExplicitPsiSubTheta t h2
  dsimp only at h
  rw [Conjectures.Goldbach.ExplicitPsiSubTheta_aux.psi_sum_eq_chebyshev,
    Conjectures.Goldbach.ExplicitPsiSubTheta_aux.theta_sum_eq_chebyshev] at h
  obtain ⟨h0, h1⟩ := h
  have hpsi := Task3b37bc2419c6ad18e55c6e6b_psi_err hRH t ht
  have heq : Chebyshev.theta t - t =
      (Chebyshev.psi t - t) - (Chebyshev.psi t - Chebyshev.theta t) := by ring
  rw [heq]
  have htri := abs_sub_le (Chebyshev.psi t - t) 0 (Chebyshev.psi t - Chebyshev.theta t)
  simp only [sub_zero, zero_sub, abs_neg] at htri
  rw [abs_of_nonneg h0] at htri
  unfold Task3b37bc2419c6ad18e55c6e6b_thetaErr
  linarith
-- @end Task3b37bc2419c6ad18e55c6e6b_theta_err

-- @helper Task3b37bc2419c6ad18e55c6e6b_theta_integral
theorem Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_abs (t : ℝ) (ht : 2 ≤ t) :
    |Chebyshev.theta t - t| ≤ t := by
  have h1 : Chebyshev.theta t ≤ Real.log 4 * t := Chebyshev.theta_le_log4_mul_x (by linarith)
  have h2 : Real.log 4 ≤ 2 := by
    rw [Real.log_four_eq]
    have := Real.log_two_lt_d9
    linarith
  have h3 : 0 ≤ Chebyshev.theta t := Chebyshev.theta_nonneg t
  have h4 : Real.log 4 * t ≤ 2 * t := mul_le_mul_of_nonneg_right h2 (by linarith)
  rw [abs_le]
  constructor <;> linarith

theorem Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_log4096 :
    8.3176 ≤ Real.log 4096 := by
  have h : Real.log 4096 = 12 * Real.log 2 := by
    rw [show (4096 : ℝ) = 2 ^ (12 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have := Real.log_two_gt_d9
  linarith

theorem Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_logt1 :
    23.5667 ≤ Real.log ((2 : ℝ) ^ (34 : ℕ)) := by
  rw [Real.log_pow]
  push_cast
  have := Real.log_two_gt_d9
  nlinarith

theorem Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_decomp (t : ℝ) :
    Task3b37bc2419c6ad18e55c6e6b_thetaErr t =
      Real.sqrt t *
          (Real.log (Real.sqrt t / Real.pi) ^ 2 / (2 * Real.pi) + 3 / 2 + Real.log 4) +
        (Real.log (Real.sqrt t / Real.pi) ^ 2 / (2 * Real.pi) + 7.5) +
        2 * t ^ (1 / 3 : ℝ) * Real.log t := by
  unfold Task3b37bc2419c6ad18e55c6e6b_thetaErr Task3b37bc2419c6ad18e55c6e6b_psiErr
  ring

theorem Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_L (t : ℝ) (ht : 0 < t) :
    Real.log (Real.sqrt t / Real.pi) = Real.log t / 2 - Real.log Real.pi := by
  rw [Real.log_div (by positivity) (by positivity), Real.log_sqrt (by linarith)]

theorem Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_pieceB (t : ℝ) (ht : (4096 : ℝ) ≤ t) :
    Task3b37bc2419c6ad18e55c6e6b_thetaErr t ≤ 0.325 * Real.sqrt t * Real.log t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hsq : 64 ≤ Real.sqrt t := by
    have h1 : (64 : ℝ) = Real.sqrt 4096 := by
      rw [show (4096 : ℝ) = 64 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h1]
    exact Real.sqrt_le_sqrt ht
  have hu : 8.3176 ≤ Real.log t :=
    Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_log4096.trans
      (Real.log_le_log (by norm_num) ht)
  have hu2 : 69.18 ≤ Real.log t ^ 2 := by nlinarith
  have hc0 : 0 ≤ Real.log Real.pi :=
    (Real.log_pos (by linarith [Real.pi_gt_three] : (1 : ℝ) < Real.pi)).le
  have hc1 : Real.log Real.pi ≤ 2.15 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_d2]
  have hL0 : 0 ≤ Real.log t / 2 - Real.log Real.pi := by linarith
  have hLsq : (Real.log t / 2 - Real.log Real.pi) ^ 2 ≤ Real.log t ^ 2 / 4 := by nlinarith
  have hL : Real.log (Real.sqrt t / Real.pi) ^ 2 ≤ Real.log t ^ 2 / 4 := by
    rw [Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_L t ht0]
    exact hLsq
  have hpi : 3.14 ≤ Real.pi := Real.pi_gt_d2.le
  have h8 : (1 : ℝ) / (2 * Real.pi) ≤ 0.1596 := by
    have h1 : (1 : ℝ) / (2 * Real.pi) ≤ 1 / 6.28 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [Real.pi_gt_d2])
    have h2 : (1 : ℝ) / 6.28 ≤ 0.1596 := by norm_num
    linarith
  have hmain : Real.log (Real.sqrt t / Real.pi) ^ 2 / (2 * Real.pi) ≤
      0.0399 * Real.log t ^ 2 := by
    calc Real.log (Real.sqrt t / Real.pi) ^ 2 / (2 * Real.pi)
        ≤ (Real.log t ^ 2 / 4) / (2 * Real.pi) :=
          div_le_div_of_nonneg_right hL (by positivity)
      _ = Real.log t ^ 2 * (1 / (2 * Real.pi)) / 4 := by ring
      _ ≤ Real.log t ^ 2 * 0.1596 / 4 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left h8 (by positivity)) (by norm_num)
      _ ≤ 0.0399 * Real.log t ^ 2 := by nlinarith
  have hlog4 : Real.log 4 ≤ 1.3864 := by
    rw [Real.log_four_eq]
    have := Real.log_two_lt_d9
    linarith
  have hA : Real.log (Real.sqrt t / Real.pi) ^ 2 / (2 * Real.pi) + 3 / 2 + Real.log 4 ≤
      0.0817 * Real.log t ^ 2 := by
    have : (2.8864 : ℝ) ≤ 0.0418 * Real.log t ^ 2 := by nlinarith
    linarith
  have hB : Real.log (Real.sqrt t / Real.pi) ^ 2 / (2 * Real.pi) + 7.5 ≤
      0.1489 * Real.log t ^ 2 := by
    have : (7.5 : ℝ) ≤ 0.109 * Real.log t ^ 2 := by nlinarith
    linarith
  have h13 : t ^ (1 / 3 : ℝ) ≤ Real.sqrt t := by
    have := Real.rpow_le_rpow_of_exponent_le (x := t) (by linarith : (1 : ℝ) ≤ t)
      (by norm_num : (1 / 3 : ℝ) ≤ 1 / 2)
    rw [← Real.sqrt_eq_rpow] at this
    exact this
  have hC : 2 * t ^ (1 / 3 : ℝ) * Real.log t ≤ 0.2405 * Real.sqrt t * Real.log t ^ 2 := by
    have h1 : 2 * t ^ (1 / 3 : ℝ) * Real.log t ≤ 2 * Real.sqrt t * Real.log t := by
      have := mul_le_mul_of_nonneg_right h13 (by linarith : 0 ≤ Real.log t)
      linarith
    have h2 : (2 : ℝ) ≤ 0.2405 * Real.log t := by nlinarith
    have h3 : 2 * (Real.sqrt t * Real.log t) ≤
        (0.2405 * Real.log t) * (Real.sqrt t * Real.log t) :=
      mul_le_mul_of_nonneg_right h2
        (mul_nonneg (Real.sqrt_nonneg t) (by linarith : 0 ≤ Real.log t))
    linarith
  have hB' : 0.1489 * Real.log t ^ 2 ≤ 0.002327 * Real.sqrt t * Real.log t ^ 2 := by
    have : (0.1489 : ℝ) ≤ 0.002327 * Real.sqrt t := by nlinarith
    have := mul_le_mul_of_nonneg_right this (show (0 : ℝ) ≤ Real.log t ^ 2 by positivity)
    linarith
  have hsum : 0.0817 * Real.sqrt t * Real.log t ^ 2 + 0.1489 * Real.log t ^ 2 +
      0.2405 * Real.sqrt t * Real.log t ^ 2 ≤ 0.325 * Real.sqrt t * Real.log t ^ 2 := by
    linarith
  rw [Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_decomp t]
  have h1 : Real.sqrt t * (Real.log (Real.sqrt t / Real.pi) ^ 2 / (2 * Real.pi) + 3 / 2 +
      Real.log 4) ≤ 0.0817 * Real.sqrt t * Real.log t ^ 2 := by
    have := mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg t)
    linarith
  linarith

theorem Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_pieceC (t : ℝ)
    (ht : (2 : ℝ) ^ (34 : ℕ) ≤ t) :
    Task3b37bc2419c6ad18e55c6e6b_thetaErr t ≤
      Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi) + 0.06 * Real.log t ^ 2 +
        2 * t ^ (1 / 3 : ℝ) * Real.log t := by
  have ht0 : 0 < t := by
    have : (0 : ℝ) < 2 ^ (34 : ℕ) := by norm_num
    linarith
  have hu : 23.5667 ≤ Real.log t :=
    Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_logt1.trans
      (Real.log_le_log (by positivity) ht)
  have hu2 : 555.38 ≤ Real.log t ^ 2 := by nlinarith
  have hc0 : 0 ≤ Real.log Real.pi :=
    (Real.log_pos (by linarith [Real.pi_gt_three] : (1 : ℝ) < Real.pi)).le
  have hc1 : Real.log Real.pi ≤ 2.15 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_lt_d2]
  have hc2 : 1.0986 ≤ Real.log Real.pi := by
    have h := Real.log_le_log (by norm_num) Real.pi_gt_three.le
    have := Real.log_three_gt_d9
    linarith
  have hL0 : 0 ≤ Real.log t / 2 - Real.log Real.pi := by linarith
  have hLsq : (Real.log t / 2 - Real.log Real.pi) ^ 2 ≤ Real.log t ^ 2 / 4 := by nlinarith
  have hL : Real.log (Real.sqrt t / Real.pi) ^ 2 ≤ Real.log t ^ 2 / 4 := by
    rw [Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_L t ht0]
    exact hLsq
  have hlog4 : Real.log 4 ≤ 1.3864 := by
    rw [Real.log_four_eq]
    have := Real.log_two_lt_d9
    linarith
  have hkey : Real.log Real.pi * Real.log t ≥
      (Real.log Real.pi) ^ 2 + 2 * Real.pi * (3 / 2 + Real.log 4) := by
    have h1 : (2 : ℝ) * Real.pi * (3 / 2 + Real.log 4) ≤ 2 * 3.15 * 2.8864 := by
      have ha : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
      have hb : (3 / 2 : ℝ) + Real.log 4 ≤ 2.8864 := by linarith
      have hc : (0 : ℝ) ≤ 2 * Real.pi := by positivity
      have h1' : 2 * Real.pi * (3 / 2 + Real.log 4) ≤ 2 * Real.pi * 2.8864 :=
        mul_le_mul_of_nonneg_left hb hc
      have h2' : 2 * Real.pi * 2.8864 ≤ 2 * 3.15 * 2.8864 := by nlinarith
      linarith
    have h2 : (Real.log Real.pi) ^ 2 ≤ 2.15 ^ 2 := by nlinarith
    have h3 : 1.0986 * 23.5667 ≤ Real.log Real.pi * Real.log t := by
      have := mul_le_mul hc2 hu (by norm_num) hc0
      linarith
    nlinarith
  have hA : Real.log (Real.sqrt t / Real.pi) ^ 2 / (2 * Real.pi) + 3 / 2 + Real.log 4 ≤
      Real.log t ^ 2 / (8 * Real.pi) := by
    rw [Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_L t ht0]
    have h1 : (Real.log t / 2 - Real.log Real.pi) ^ 2 / (2 * Real.pi) + 3 / 2 + Real.log 4 -
        Real.log t ^ 2 / (8 * Real.pi) =
        (4 * (Real.log t / 2 - Real.log Real.pi) ^ 2 +
          8 * Real.pi * (3 / 2 + Real.log 4) - Real.log t ^ 2) / (8 * Real.pi) := by
      field_simp
      ring
    have h2 : 4 * (Real.log t / 2 - Real.log Real.pi) ^ 2 +
        8 * Real.pi * (3 / 2 + Real.log 4) - Real.log t ^ 2 =
        -4 * (Real.log Real.pi * Real.log t - (Real.log Real.pi) ^ 2 -
          2 * Real.pi * (3 / 2 + Real.log 4)) := by ring
    have h3 : (Real.log t / 2 - Real.log Real.pi) ^ 2 / (2 * Real.pi) + 3 / 2 + Real.log 4 -
        Real.log t ^ 2 / (8 * Real.pi) ≤ 0 := by
      rw [h1, h2]
      have h4 : -4 * (Real.log Real.pi * Real.log t - (Real.log Real.pi) ^ 2 -
          2 * Real.pi * (3 / 2 + Real.log 4)) ≤ 0 := by linarith
      exact div_nonpos_of_nonpos_of_nonneg h4 (by positivity)
    linarith
  have h8 : (1 : ℝ) / (2 * Real.pi) ≤ 0.1596 := by
    have h1 : (1 : ℝ) / (2 * Real.pi) ≤ 1 / 6.28 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [Real.pi_gt_d2])
    have h2 : (1 : ℝ) / 6.28 ≤ 0.1596 := by norm_num
    linarith [Real.pi_gt_d2]
  have hmain : Real.log (Real.sqrt t / Real.pi) ^ 2 / (2 * Real.pi) ≤
      0.0399 * Real.log t ^ 2 := by
    calc Real.log (Real.sqrt t / Real.pi) ^ 2 / (2 * Real.pi)
        ≤ (Real.log t ^ 2 / 4) / (2 * Real.pi) :=
          div_le_div_of_nonneg_right hL (by positivity)
      _ = Real.log t ^ 2 * (1 / (2 * Real.pi)) / 4 := by ring
      _ ≤ Real.log t ^ 2 * 0.1596 / 4 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left h8 (by positivity)) (by norm_num)
      _ ≤ 0.0399 * Real.log t ^ 2 := by nlinarith
  have hB : Real.log (Real.sqrt t / Real.pi) ^ 2 / (2 * Real.pi) + 7.5 ≤
      0.06 * Real.log t ^ 2 := by
    have : (7.5 : ℝ) ≤ 0.0201 * Real.log t ^ 2 := by nlinarith
    linarith
  rw [Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_decomp t]
  have h1 : Real.sqrt t * (Real.log (Real.sqrt t / Real.pi) ^ 2 / (2 * Real.pi) + 3 / 2 +
      Real.log 4) ≤ Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi) := by
    calc Real.sqrt t * (Real.log (Real.sqrt t / Real.pi) ^ 2 / (2 * Real.pi) + 3 / 2 +
          Real.log 4)
        ≤ Real.sqrt t * (Real.log t ^ 2 / (8 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hA (Real.sqrt_nonneg t)
      _ = Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi) := by ring
  linarith

theorem Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_sqrt_t1 :
    Real.sqrt ((2 : ℝ) ^ (34 : ℕ)) = 131072 := by
  rw [show (2 : ℝ) ^ (34 : ℕ) = (131072 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_sqrt4096 :
    Real.sqrt 4096 = 64 := by
  rw [show (4096 : ℝ) = 64 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_rpow (x : ℝ) (hx : (1200 : ℝ) ^ 6 ≤ x) :
    x ^ (1 / 3 : ℝ) ≤ Real.sqrt x / 1200 := by
  have hx0 : 0 < x := by
    have : (0 : ℝ) < 1200 ^ 6 := by norm_num
    linarith
  have h6 : (1200 : ℝ) ≤ x ^ (1 / 6 : ℝ) := by
    have h1 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (1200 : ℝ) ^ 6) hx
      (by norm_num : (0 : ℝ) ≤ 1 / 6)
    have h2 : ((1200 : ℝ) ^ 6) ^ (1 / 6 : ℝ) = 1200 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num [Real.rpow_one]
    linarith
  have h3 : x ^ (1 / 3 : ℝ) = Real.sqrt x / x ^ (1 / 6 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx0]
    norm_num
  rw [h3]
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg x) (by norm_num) h6

theorem Task3b37bc2419c6ad18e55c6e6b_theta_integral (hRH : RiemannHypothesis) :
    ∀ x : ℝ, (4 : ℝ) * (10 : ℝ) ^ (18 : ℕ) ≤ x →
      |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
        Real.sqrt x / 12 + (10 : ℝ) ^ (5 : ℕ) := by
  intro x hx
  have hx0 : (4 : ℝ) * 10 ^ 18 ≤ x := by
    have h : (4 : ℝ) * (10 : ℝ) ^ (18 : ℕ) = 4 * 10 ^ 18 := by norm_num
    linarith
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hx4096 : (4096 : ℝ) ≤ x := by linarith
  have hxt1 : (2 : ℝ) ^ (34 : ℕ) ≤ x := by
    have h : (2 : ℝ) ^ (34 : ℕ) = 17179869184 := by norm_num
    linarith
  have hx1200 : (1200 : ℝ) ^ 6 ≤ x := by
    have h : (1200 : ℝ) ^ 6 = 2985984000000000000 := by norm_num
    linarith
  have h4096t1 : (4096 : ℝ) ≤ (2 : ℝ) ^ (34 : ℕ) := by
    have h : (2 : ℝ) ^ (34 : ℕ) = 17179869184 := by norm_num
    linarith
  -- integrability of the integrand on [2, x]
  have hθint : IntervalIntegrable
      (fun t : ℝ => Chebyshev.theta t / (t * Real.log t ^ 2)) MeasureTheory.volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx2).mpr
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have h1int : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / Real.log t ^ 2) MeasureTheory.volume 2 x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have htint : IntervalIntegrable (fun t : ℝ => t / (t * Real.log t ^ 2)) MeasureTheory.volume 2 x := by
    refine IntervalIntegrable.congr (fun t ht => ?_) h1int
    have ht2 : (2 : ℝ) ≤ t := by
      rw [Set.uIoc_of_le hx2] at ht
      exact ht.1.le
    have ht0 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    field_simp
  have hfint : IntervalIntegrable
      (fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) MeasureTheory.volume 2 x := by
    have h : (fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) =
        fun t => Chebyshev.theta t / (t * Real.log t ^ 2) - t / (t * Real.log t ^ 2) := by
      ext t
      ring
    rw [h]
    exact hθint.sub htint
  have hfiA : IntervalIntegrable
      (fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) MeasureTheory.volume 2 4096 := by
    refine hfint.mono_set ?_
    rw [Set.uIcc_of_le hx2, Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4096)]
    intro t ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  have hfiB : IntervalIntegrable
      (fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) MeasureTheory.volume 4096
        ((2 : ℝ) ^ (34 : ℕ)) := by
    refine hfint.mono_set ?_
    rw [Set.uIcc_of_le hx2, Set.uIcc_of_le h4096t1]
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hfiC : IntervalIntegrable
      (fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) MeasureTheory.volume
        ((2 : ℝ) ^ (34 : ℕ)) x := by
    refine hfint.mono_set ?_
    rw [Set.uIcc_of_le hx2, Set.uIcc_of_le hxt1]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hfiBx : IntervalIntegrable
      (fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) MeasureTheory.volume 4096 x := by
    refine hfint.mono_set ?_
    rw [Set.uIcc_of_le hx2, Set.uIcc_of_le hx4096]
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  -- piece A : [2, 4096]
  have hA : |∫ t in (2 : ℝ)..4096, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤ 8600 := by
    have hpt : ∀ t ∈ Set.Icc (2 : ℝ) 4096,
        |(Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤ 2.1 := by
      intro t ht
      have ht2 : (2 : ℝ) ≤ t := ht.1
      have hlog : 0 < Real.log t := Real.log_pos (by linarith)
      have habs := Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_abs t ht2
      have hlog2 : 0.6931 ≤ Real.log t := by
        have h := Real.log_le_log (by norm_num) ht2
        have := Real.log_two_gt_d9
        linarith
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t * Real.log t ^ 2)]
      have h1 : |Chebyshev.theta t - t| / (t * Real.log t ^ 2) ≤ 1 / Real.log t ^ 2 := by
        calc |Chebyshev.theta t - t| / (t * Real.log t ^ 2) ≤ t / (t * Real.log t ^ 2) :=
              div_le_div_of_nonneg_right habs (by positivity)
          _ = 1 / Real.log t ^ 2 := by field_simp
      have h2 : (1 : ℝ) / Real.log t ^ 2 ≤ 2.1 := by
        have h3 : (1 : ℝ) ≤ 2.1 * Real.log t ^ 2 := by nlinarith
        exact (div_le_iff₀ (by positivity)).mpr h3
      linarith
    have hle1 : (∫ t in (2 : ℝ)..4096, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) ≤
        ∫ _t in (2 : ℝ)..4096, (2.1 : ℝ) :=
      intervalIntegral.integral_mono_on (by norm_num) hfiA intervalIntegrable_const
        (fun t ht => (abs_le.mp (hpt t ht)).2)
    have hle2 : (∫ _t in (2 : ℝ)..4096, (-2.1 : ℝ)) ≤
        ∫ t in (2 : ℝ)..4096, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) :=
      intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_const hfiA
        (fun t ht => (abs_le.mp (hpt t ht)).1)
    rw [intervalIntegral.integral_const] at hle1 hle2
    simp only [smul_eq_mul] at hle1 hle2
    rw [abs_le]
    constructor <;> linarith
  -- piece B : [4096, 2^34]
  have hB : |∫ t in (4096 : ℝ)..((2 : ℝ) ^ (34 : ℕ)),
      (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤ 85197 := by
    have hpt : ∀ t ∈ Set.Icc (4096 : ℝ) ((2 : ℝ) ^ (34 : ℕ)),
        |(Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤ 0.325 * t ^ (-1 / 2 : ℝ) := by
      intro t ht
      have ht1 : (4096 : ℝ) ≤ t := ht.1
      have ht0 : 0 < t := by linarith
      have hlog : 0 < Real.log t := Real.log_pos (by linarith)
      have hth := Task3b37bc2419c6ad18e55c6e6b_theta_err hRH t (by linarith)
      have hE := Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_pieceB t ht1
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t * Real.log t ^ 2)]
      have h1 : |Chebyshev.theta t - t| / (t * Real.log t ^ 2) ≤
          0.325 * Real.sqrt t * Real.log t ^ 2 / (t * Real.log t ^ 2) :=
        div_le_div_of_nonneg_right (hth.trans hE) (by positivity)
      have h3 : Real.sqrt t / t = t ^ (-1 / 2 : ℝ) := by
        rw [show (-1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub ht0, Real.rpow_one,
          Real.sqrt_eq_rpow]
      have h4 : 0.325 * Real.sqrt t * Real.log t ^ 2 / (t * Real.log t ^ 2) =
          0.325 * (Real.sqrt t / t) := by
        field_simp
      linarith
    have hI : IntervalIntegrable (fun t : ℝ => (0.325 : ℝ) * t ^ (-1 / 2 : ℝ)) MeasureTheory.volume 4096
        ((2 : ℝ) ^ (34 : ℕ)) :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul 0.325
    have hle1 : (∫ t in (4096 : ℝ)..((2 : ℝ) ^ (34 : ℕ)),
        (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) ≤
        ∫ t in (4096 : ℝ)..((2 : ℝ) ^ (34 : ℕ)), (0.325 : ℝ) * t ^ (-1 / 2 : ℝ) :=
      intervalIntegral.integral_mono_on h4096t1 hfiB hI
        (fun t ht => (abs_le.mp (hpt t ht)).2)
    have hle2 : (∫ t in (4096 : ℝ)..((2 : ℝ) ^ (34 : ℕ)),
        -((0.325 : ℝ) * t ^ (-1 / 2 : ℝ))) ≤
        ∫ t in (4096 : ℝ)..((2 : ℝ) ^ (34 : ℕ)),
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2) :=
      intervalIntegral.integral_mono_on h4096t1 hI.neg hfiB
        (fun t ht => (abs_le.mp (hpt t ht)).1)
    have hint : (∫ t in (4096 : ℝ)..((2 : ℝ) ^ (34 : ℕ)), (0.325 : ℝ) * t ^ (-1 / 2 : ℝ)) =
        0.325 * (2 * (131072 - 64)) := by
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
      have e1 : ((2 : ℝ) ^ (34 : ℕ)) ^ ((-1 / 2 : ℝ) + 1) = 131072 := by
        rw [show ((-1 / 2 : ℝ) + 1) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
          Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_sqrt_t1]
      have e2 : (4096 : ℝ) ^ ((-1 / 2 : ℝ) + 1) = 64 := by
        rw [show ((-1 / 2 : ℝ) + 1) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
          Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_sqrt4096]
      rw [e1, e2]
      norm_num
    rw [hint] at hle1
    have hint2 : (∫ t in (4096 : ℝ)..((2 : ℝ) ^ (34 : ℕ)),
        -((0.325 : ℝ) * t ^ (-1 / 2 : ℝ))) = -(0.325 * (2 * (131072 - 64))) := by
      rw [intervalIntegral.integral_neg, hint]
    rw [hint2] at hle2
    rw [abs_le]
    constructor <;> linarith
  -- piece C : [2^34, x]
  have hC : |∫ t in ((2 : ℝ) ^ (34 : ℕ))..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
      (1 / (4 * Real.pi) + 0.00022) * Real.sqrt x := by
    have hpt : ∀ t ∈ Set.Icc ((2 : ℝ) ^ (34 : ℕ)) x,
        |(Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
          (1 / (8 * Real.pi) + 0.0000005) * t ^ (-1 / 2 : ℝ) + 0.085 * t ^ (-2 / 3 : ℝ) := by
      intro t ht
      have ht1 : (2 : ℝ) ^ (34 : ℕ) ≤ t := ht.1
      have ht0 : 0 < t := by
        have : (0 : ℝ) < 2 ^ (34 : ℕ) := by norm_num
        linarith
      have hlog : 0 < Real.log t := Real.log_pos (by
        have : (1 : ℝ) < 2 ^ (34 : ℕ) := by norm_num
        linarith)
      have hu : 23.5667 ≤ Real.log t :=
        Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_logt1.trans
          (Real.log_le_log (by positivity) ht1)
      have hth := Task3b37bc2419c6ad18e55c6e6b_theta_err hRH t (by
        have : (2500 : ℝ) ≤ 2 ^ (34 : ℕ) := by norm_num
        linarith)
      have hE := Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_pieceC t ht1
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < t * Real.log t ^ 2)]
      have hmain : |Chebyshev.theta t - t| / (t * Real.log t ^ 2) ≤
          (Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi) + 0.06 * Real.log t ^ 2 +
            2 * t ^ (1 / 3 : ℝ) * Real.log t) / (t * Real.log t ^ 2) :=
        div_le_div_of_nonneg_right (hth.trans hE) (by positivity)
      have h3 : Real.sqrt t / t = t ^ (-1 / 2 : ℝ) := by
        rw [show (-1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub ht0, Real.rpow_one,
          Real.sqrt_eq_rpow]
      have hA' : Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi) / (t * Real.log t ^ 2) =
          (1 / (8 * Real.pi)) * t ^ (-1 / 2 : ℝ) := by
        have h4 : Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi) / (t * Real.log t ^ 2) =
            (1 / (8 * Real.pi)) * (Real.sqrt t / t) := by
          field_simp
        rw [h4, h3]
      have hB' : 0.06 * Real.log t ^ 2 / (t * Real.log t ^ 2) ≤ 0.0000005 * t ^ (-1 / 2 : ℝ) := by
        have h4 : 0.06 * Real.log t ^ 2 / (t * Real.log t ^ 2) = 0.06 / t := by
          field_simp
        rw [h4]
        have h5 : t ^ (-1 / 2 : ℝ) * t = Real.sqrt t := by
          have h : t ^ (-1 / 2 : ℝ) * t = t ^ (-1 / 2 : ℝ) * t ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          rw [h, ← Real.rpow_add ht0, show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
            Real.sqrt_eq_rpow]
        have h6 : (131072 : ℝ) ≤ Real.sqrt t := by
          have := Real.sqrt_le_sqrt ht1
          rwa [Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_sqrt_t1] at this
        have h7 : (0.06 : ℝ) ≤ 0.0000005 * t ^ (-1 / 2 : ℝ) * t := by
          have h7' : (0.06 : ℝ) ≤ 0.0000005 * (t ^ (-1 / 2 : ℝ) * t) := by
            rw [h5]
            nlinarith
          linarith
        exact (div_le_iff₀ ht0).mpr h7
      have hC' : 2 * t ^ (1 / 3 : ℝ) * Real.log t / (t * Real.log t ^ 2) ≤
          0.085 * t ^ (-2 / 3 : ℝ) := by
        have h8 : 2 * t ^ (1 / 3 : ℝ) * Real.log t / (t * Real.log t ^ 2) =
            (2 / Real.log t) * (t ^ (1 / 3 : ℝ) / t) := by
          field_simp
        have h9 : t ^ (1 / 3 : ℝ) / t = t ^ (-2 / 3 : ℝ) := by
          rw [show (-2 / 3 : ℝ) = 1 / 3 - 1 by norm_num, Real.rpow_sub ht0, Real.rpow_one]
        rw [h8, h9]
        have h10 : (2 : ℝ) / Real.log t ≤ 0.085 := by
          have h11 : (2 : ℝ) / Real.log t ≤ 2 / 23.5667 :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) hu
          have h12 : (2 : ℝ) / 23.5667 ≤ 0.085 := by norm_num
          linarith
        exact mul_le_mul_of_nonneg_right h10 (by positivity)
      have hsum : (Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi) + 0.06 * Real.log t ^ 2 +
          2 * t ^ (1 / 3 : ℝ) * Real.log t) / (t * Real.log t ^ 2) =
          Real.sqrt t * Real.log t ^ 2 / (8 * Real.pi) / (t * Real.log t ^ 2) +
          0.06 * Real.log t ^ 2 / (t * Real.log t ^ 2) +
          2 * t ^ (1 / 3 : ℝ) * Real.log t / (t * Real.log t ^ 2) := by ring
      linarith
    have hI : IntervalIntegrable (fun t : ℝ =>
        (1 / (8 * Real.pi) + 0.0000005) * t ^ (-1 / 2 : ℝ) + 0.085 * t ^ (-2 / 3 : ℝ))
        MeasureTheory.volume ((2 : ℝ) ^ (34 : ℕ)) x :=
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _).add
        ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _)
    have hle1 : (∫ t in ((2 : ℝ) ^ (34 : ℕ))..x,
        (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) ≤
        ∫ t in ((2 : ℝ) ^ (34 : ℕ))..x,
          ((1 / (8 * Real.pi) + 0.0000005) * t ^ (-1 / 2 : ℝ) + 0.085 * t ^ (-2 / 3 : ℝ)) :=
      intervalIntegral.integral_mono_on hxt1 hfiC hI (fun t ht => (abs_le.mp (hpt t ht)).2)
    have hle2 : (∫ t in ((2 : ℝ) ^ (34 : ℕ))..x,
        -((1 / (8 * Real.pi) + 0.0000005) * t ^ (-1 / 2 : ℝ) + 0.085 * t ^ (-2 / 3 : ℝ))) ≤
        ∫ t in ((2 : ℝ) ^ (34 : ℕ))..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2) :=
      intervalIntegral.integral_mono_on hxt1 hI.neg hfiC
        (fun t ht => (abs_le.mp (hpt t ht)).1)
    have hint : (∫ t in ((2 : ℝ) ^ (34 : ℕ))..x,
        ((1 / (8 * Real.pi) + 0.0000005) * t ^ (-1 / 2 : ℝ) + 0.085 * t ^ (-2 / 3 : ℝ))) ≤
        (1 / (4 * Real.pi) + 0.00022) * Real.sqrt x := by
      rw [intervalIntegral.integral_add
          ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _)
          ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by norm_num)), integral_rpow (Or.inl (by norm_num))]
      have e1 : x ^ ((-1 / 2 : ℝ) + 1) = Real.sqrt x := by
        rw [show ((-1 / 2 : ℝ) + 1) = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
      have e2 : ((2 : ℝ) ^ (34 : ℕ)) ^ ((-1 / 2 : ℝ) + 1) = 131072 := by
        rw [show ((-1 / 2 : ℝ) + 1) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
          Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_sqrt_t1]
      have e3 : x ^ ((-2 / 3 : ℝ) + 1) = x ^ (1 / 3 : ℝ) := by
        rw [show ((-2 / 3 : ℝ) + 1) = 1 / 3 by norm_num]
      have e4 : ((2 : ℝ) ^ (34 : ℕ)) ^ ((-2 / 3 : ℝ) + 1) =
          ((2 : ℝ) ^ (34 : ℕ)) ^ (1 / 3 : ℝ) := by
        rw [show ((-2 / 3 : ℝ) + 1) = 1 / 3 by norm_num]
      have e5 : (0 : ℝ) ≤ ((2 : ℝ) ^ (34 : ℕ)) ^ (1 / 3 : ℝ) :=
        Real.rpow_nonneg (by positivity) _
      have e6 : x ^ (1 / 3 : ℝ) ≤ Real.sqrt x / 1200 :=
        Task3b37bc2419c6ad18e55c6e6b_theta_integral_aux_rpow x hx1200
      rw [e1, e2, e3, e4]
      have f1 : (Real.sqrt x - 131072) / ((-1 / 2 : ℝ) + 1) ≤ 2 * Real.sqrt x := by
        rw [div_le_iff₀ (by norm_num)]
        linarith
      have f2 : (x ^ (1 / 3 : ℝ) - ((2 : ℝ) ^ (34 : ℕ)) ^ (1 / 3 : ℝ)) / ((-2 / 3 : ℝ) + 1) ≤
          3 * (Real.sqrt x / 1200) := by
        rw [div_le_iff₀ (by norm_num)]
        nlinarith
      have ha : (0 : ℝ) ≤ 1 / (8 * Real.pi) :=
        (div_pos one_pos (mul_pos (by norm_num) Real.pi_pos)).le
      have f3 : (1 / (8 * Real.pi) + 0.0000005) *
          ((Real.sqrt x - 131072) / ((-1 / 2 : ℝ) + 1)) ≤
          (1 / (8 * Real.pi) + 0.0000005) * (2 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left f1 (add_nonneg ha (by norm_num))
      have f4 : (0.085 : ℝ) *
          ((x ^ (1 / 3 : ℝ) - ((2 : ℝ) ^ (34 : ℕ)) ^ (1 / 3 : ℝ)) / ((-2 / 3 : ℝ) + 1)) ≤
          0.085 * (3 * (Real.sqrt x / 1200)) := mul_le_mul_of_nonneg_left f2 (by norm_num)
      have f5 : (1 / (8 * Real.pi) + 0.0000005) * 2 + 0.085 * 3 / 1200 ≤
          1 / (4 * Real.pi) + 0.00022 := by
        have : (1 : ℝ) / (8 * Real.pi) * 2 = 1 / (4 * Real.pi) := by ring
        linarith
      have f6 : (1 / (8 * Real.pi) + 0.0000005) * (2 * Real.sqrt x) +
          0.085 * (3 * (Real.sqrt x / 1200)) ≤
          (1 / (4 * Real.pi) + 0.00022) * Real.sqrt x := by
        have g1 : (1 / (8 * Real.pi) + 0.0000005) * (2 * Real.sqrt x) =
            ((1 / (8 * Real.pi) + 0.0000005) * 2) * Real.sqrt x := by ring
        have g2 : 0.085 * (3 * (Real.sqrt x / 1200)) = (0.085 * 3 / 1200) * Real.sqrt x := by ring
        rw [g1, g2]
        have := mul_le_mul_of_nonneg_right f5 (Real.sqrt_nonneg x)
        linarith
      linarith
    have hint2 : (∫ t in ((2 : ℝ) ^ (34 : ℕ))..x,
        -((1 / (8 * Real.pi) + 0.0000005) * t ^ (-1 / 2 : ℝ) + 0.085 * t ^ (-2 / 3 : ℝ))) =
        -(∫ t in ((2 : ℝ) ^ (34 : ℕ))..x,
          ((1 / (8 * Real.pi) + 0.0000005) * t ^ (-1 / 2 : ℝ) + 0.085 * t ^ (-2 / 3 : ℝ))) := by
      rw [intervalIntegral.integral_neg]
    rw [hint2] at hle2
    have hnonneg : (0 : ℝ) ≤ ∫ t in ((2 : ℝ) ^ (34 : ℕ))..x,
        ((1 / (8 * Real.pi) + 0.0000005) * t ^ (-1 / 2 : ℝ) + 0.085 * t ^ (-2 / 3 : ℝ)) := by
      refine intervalIntegral.integral_nonneg hxt1 (fun t ht => ?_)
      have ht0 : (0 : ℝ) ≤ t := by
        have hpos : (0 : ℝ) < 2 ^ (34 : ℕ) := by norm_num
        linarith [ht.1]
      have ha : (0 : ℝ) ≤ 1 / (8 * Real.pi) :=
        (div_pos one_pos (mul_pos (by norm_num) Real.pi_pos)).le
      have hb : (0 : ℝ) ≤ (1 / (8 * Real.pi) + 0.0000005) * t ^ (-1 / 2 : ℝ) :=
        mul_nonneg (add_nonneg ha (by norm_num)) (Real.rpow_nonneg ht0 _)
      have hc : (0 : ℝ) ≤ 0.085 * t ^ (-2 / 3 : ℝ) :=
        mul_nonneg (by norm_num) (Real.rpow_nonneg ht0 _)
      linarith
    rw [abs_le]
    constructor
    · linarith
    · linarith
  -- assemble
  have hsplit : (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) =
      (∫ t in (2 : ℝ)..4096, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) +
        (∫ t in (4096 : ℝ)..((2 : ℝ) ^ (34 : ℕ)),
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) +
        (∫ t in ((2 : ℝ) ^ (34 : ℕ))..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) := by
    calc (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) =
        (∫ t in (2 : ℝ)..4096, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) +
          (∫ t in (4096 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) :=
      (intervalIntegral.integral_add_adjacent_intervals hfiA hfiBx).symm
      _ = (∫ t in (2 : ℝ)..4096, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) +
          (∫ t in (4096 : ℝ)..((2 : ℝ) ^ (34 : ℕ)),
            (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) +
          (∫ t in ((2 : ℝ) ^ (34 : ℕ))..x,
            (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) := by
        rw [(intervalIntegral.integral_add_adjacent_intervals hfiB hfiC).symm]
        ring
  have hfin : (1 : ℝ) / (4 * Real.pi) + 0.00022 ≤ 1 / 12 := by
    have h1 : (1 : ℝ) / (4 * Real.pi) ≤ 1 / 12.56 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [Real.pi_gt_d2])
    have h2 : (1 : ℝ) / 12.56 + 0.00022 ≤ 1 / 12 := by norm_num
    linarith
  rw [hsplit]
  have htri := abs_add_le
    ((∫ t in (2 : ℝ)..4096, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) +
      (∫ t in (4096 : ℝ)..((2 : ℝ) ^ (34 : ℕ)),
        (Chebyshev.theta t - t) / (t * Real.log t ^ 2)))
    (∫ t in ((2 : ℝ) ^ (34 : ℕ))..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
  have htri2 := abs_add_le
    (∫ t in (2 : ℝ)..4096, (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
    (∫ t in (4096 : ℝ)..((2 : ℝ) ^ (34 : ℕ)),
      (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
  have hmain : (1 / (4 * Real.pi) + 0.00022) * Real.sqrt x ≤ (1 / 12) * Real.sqrt x :=
    mul_le_mul_of_nonneg_right hfin (Real.sqrt_nonneg x)
  have h10 : (10 : ℝ) ^ (5 : ℕ) = 100000 := by norm_num
  rw [h10]
  linarith
-- @end Task3b37bc2419c6ad18e55c6e6b_theta_integral

-- @helper Task3b37bc2419c6ad18e55c6e6b_li_two
theorem Task3b37bc2419c6ad18e55c6e6b_li_two :
    |(Real.eulerMascheroniConstant + Real.log (Real.log (2 : ℝ)) +
      ∑' (x4 : ℕ), Real.log (2 : ℝ) ^ (x4 + (1 : ℕ)) /
        (↑(x4 + (1 : ℕ)) * ↑(x4 + (1 : ℕ)).factorial)) - 2 / Real.log 2| ≤ 3 := by
    set x : ℝ := Real.log 2 with hxdef
    have hx0 : 0 < x := by linarith [hxdef, Real.log_two_gt_d9]
    have hx23 : (2 : ℝ) / 3 ≤ x := by linarith [hxdef, Real.log_two_gt_d9]
    have hxhalf : (1 : ℝ) / 2 ≤ x := by linarith [hxdef, Real.log_two_gt_d9]
    have hx1 : x ≤ 1 := by linarith [hxdef, Real.log_two_lt_d9]
    have hll_lo : -1 ≤ Real.log x := by
      have h : Real.log (1 / 2 : ℝ) ≤ Real.log x := Real.log_le_log (by norm_num) hxhalf
      rw [one_div, Real.log_inv] at h
      linarith [hxdef]
    have hll_hi : Real.log x ≤ 0 := by
      have h : Real.log x ≤ Real.log (1 : ℝ) := Real.log_le_log hx0 hx1
      rwa [Real.log_one] at h
    -- the series
    have hg : Summable (fun n : ℕ => x ^ (n + 1) / ((n + 1).factorial : ℝ)) :=
      (summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial x)
    have hfnonneg : ∀ n : ℕ, 0 ≤ x ^ (n + 1) / (↑(n + 1) * ↑(n + 1).factorial) := by
      intro n
      refine div_nonneg (pow_nonneg hx0.le _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have hfle : ∀ n : ℕ, x ^ (n + 1) / (↑(n + 1) * ↑(n + 1).factorial) ≤
        x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
      intro n
      rw [← div_div]
      refine div_le_div_of_nonneg_right (div_le_self (pow_nonneg hx0.le _) ?_) (by positivity)
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hf : Summable (fun n : ℕ => x ^ (n + 1) / (↑(n + 1) * ↑(n + 1).factorial)) :=
      Summable.of_nonneg_of_le hfnonneg hfle hg
    have htsum_g : (∑' n : ℕ, x ^ (n + 1) / ((n + 1).factorial : ℝ)) = 1 := by
      have hexp : Real.exp x = ∑' n : ℕ, x ^ n / (n.factorial : ℝ) := by
        rw [Real.exp_eq_exp_ℝ]
        exact congr_fun (NormedSpace.exp_eq_tsum_div (𝔸 := ℝ)) x
      have h := (Real.summable_pow_div_factorial x).tsum_eq_zero_add
      rw [← hexp] at h
      have h3 : Real.exp x = 1 + ∑' n : ℕ, x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
        simpa using h
      have hex : Real.exp x = 2 := by rw [hxdef, Real.exp_log (by norm_num)]
      rw [hex] at h3
      linarith
    have hS_le : (∑' n : ℕ, x ^ (n + 1) / (↑(n + 1) * ↑(n + 1).factorial)) ≤ 1 := by
      calc (∑' n : ℕ, x ^ (n + 1) / (↑(n + 1) * ↑(n + 1).factorial))
          ≤ ∑' n : ℕ, x ^ (n + 1) / ((n + 1).factorial : ℝ) := hf.tsum_le_tsum hfle hg
        _ = 1 := htsum_g
    have hS_lo : x ≤ ∑' n : ℕ, x ^ (n + 1) / (↑(n + 1) * ↑(n + 1).factorial) := by
      have h := hf.sum_le_tsum {0} (fun i _ => hfnonneg i)
      simpa using h
    have hdiv_hi : 2 / x ≤ 3 := by
      rw [div_le_iff₀ hx0]
      linarith
    have hdiv_lo : (2 : ℝ) ≤ 2 / x := by
      rw [le_div_iff₀ hx0]
      linarith
    rw [abs_le]
    constructor
    · linarith [Real.one_half_lt_eulerMascheroniConstant]
    · linarith [Real.eulerMascheroniConstant_lt_two_thirds]
-- @end Task3b37bc2419c6ad18e55c6e6b_li_two

-- @helper Task3b37bc2419c6ad18e55c6e6b_final_numeric
theorem Task3b37bc2419c6ad18e55c6e6b_final_numeric :
    ∀ x : ℝ, (4 : ℝ) * (10 : ℝ) ^ (18 : ℕ) ≤ x →
      Task3b37bc2419c6ad18e55c6e6b_thetaErr x / Real.log x + Real.sqrt x / 12 + 100003 ≤
        Real.sqrt x * Real.log x / (8 * Real.pi) := by
  intro x hx
  have hxpos : 0 < x := by
    have : (0:ℝ) < 4 * 10 ^ (18:ℕ) := by norm_num
    linarith
  have hlog2lo : (0.6931 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2hi : Real.log 2 < 0.6932 := by linarith [Real.log_two_lt_d9]
  have hlog5lo : (1.6094 : ℝ) < Real.log 5 := by linarith [Real.log_five_gt_d9]
  have hlog5hi : Real.log 5 < 1.6095 := by linarith [Real.log_five_lt_d9]
  have hlog4pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog4 : Real.log 4 ≤ 1.39 := by
    rw [Real.log_four_eq]; linarith
  -- u = log x ≥ 42
  have hu42 : (42:ℝ) ≤ Real.log x := by
    have h1 : Real.log ((4:ℝ) * 10 ^ (18:ℕ)) ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have h2 : Real.log ((4:ℝ) * 10 ^ (18:ℕ)) = 20 * Real.log 2 + 18 * Real.log 5 := by
      have h4 : (4:ℝ) * 10 ^ (18:ℕ) = 2 ^ 20 * 5 ^ 18 := by norm_num
      rw [h4, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
      push_cast; ring
    linarith
  -- s = sqrt x ≥ 2·10^9
  have hs : (2 * 10 ^ 9 : ℝ) ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    have h4 : (4:ℝ) * 10 ^ (18:ℕ) = (2 * 10 ^ 9 : ℝ) ^ 2 := by norm_num
    rw [h4, Real.sqrt_sq (by norm_num)] at h
    exact h
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hspos : 0 < Real.sqrt x := by linarith
  -- bounds on log π
  have hLlo : (1.09:ℝ) ≤ Real.log Real.pi := by
    have h3 : (3:ℝ) < Real.pi := Real.pi_gt_three
    have h := Real.log_le_log (by norm_num) h3.le
    linarith [Real.log_three_gt_d9]
  have hLhi : Real.log Real.pi ≤ 1.17 := by
    have hpi : Real.pi ≤ (16:ℝ) / 5 := by linarith [Real.pi_lt_d2]
    have h := Real.log_le_log Real.pi_pos hpi
    have h2 : Real.log ((16:ℝ) / 5) = 4 * Real.log 2 - Real.log 5 := by
      rw [Real.log_div (by norm_num) (by norm_num), show (16:ℝ) = 4 ^ 2 by norm_num,
        Real.log_pow, Real.log_four_eq]
      push_cast; ring
    linarith
  have hL0 : 0 ≤ Real.log Real.pi := by linarith
  -- log x ≤ sqrt x / 1000
  have hu_up : Real.log x ≤ Real.sqrt x / 1000 := by
    have hlog10hi : Real.log 10 ≤ 2.31 := by
      rw [Real.log_ten_eq]; linarith
    have h1 : Real.log (Real.sqrt x / 1000000) ≤ Real.sqrt x / 1000000 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log (Real.sqrt x / 1000000) =
        Real.log (Real.sqrt x) - 6 * Real.log 10 := by
      rw [Real.log_div (by positivity) (by norm_num), show (1000000:ℝ) = (10:ℝ) ^ (6:ℕ) by norm_num,
        Real.log_pow]
      push_cast; ring
    have h3 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      rw [Real.log_sqrt hxpos.le]; ring
    linarith
  -- x^(1/3) ≤ sqrt x / 1000
  have hx13 : x ^ (1/3 : ℝ) ≤ Real.sqrt x / 1000 := by
    have h18 : (1000:ℝ) ^ (6:ℕ) ≤ x := by
      have h4 : (4:ℝ) * 10 ^ (18:ℕ) = 4 * (1000:ℝ) ^ (6:ℕ) := by norm_num
      linarith
    have hm := Real.rpow_le_rpow (by norm_num) h18 (by norm_num : (0:ℝ) ≤ 1 / 6)
    have heq : ((1000:ℝ) ^ (6:ℕ)) ^ (1 / 6 : ℝ) = 1000 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h6 : (1000:ℝ) ≤ x ^ (1 / 6 : ℝ) := by linarith
    have hsplit : x ^ (1 / 2 : ℝ) = x ^ (1 / 3 : ℝ) * x ^ (1 / 6 : ℝ) := by
      rw [← Real.rpow_add hxpos]; norm_num
    have h13 : 0 ≤ x ^ (1 / 3 : ℝ) := Real.rpow_nonneg hxpos.le _
    rw [Real.sqrt_eq_rpow, hsplit]
    nlinarith
  have hu0 : 0 < Real.log x := by linarith
  have hlog : Real.log (Real.sqrt x / Real.pi) = Real.log x / 2 - Real.log Real.pi := by
    rw [Real.log_div hspos.ne' Real.pi_ne_zero, Real.log_sqrt hxpos.le]
  have hth : 8 * Real.pi * Task3b37bc2419c6ad18e55c6e6b_thetaErr x =
      (Real.sqrt x + 1) * (Real.log x - 2 * Real.log Real.pi) ^ 2 +
      12 * Real.pi * (Real.sqrt x + 1) + 48 * Real.pi +
      8 * Real.pi * Real.log 4 * Real.sqrt x +
      16 * Real.pi * x ^ (1 / 3 : ℝ) * Real.log x := by
    have heq : (Real.sqrt x + 1) * (Real.log x - 2 * Real.log Real.pi) ^ 2 =
        4 * (Real.sqrt x + 1) * (Real.log x / 2 - Real.log Real.pi) ^ 2 := by ring
    rw [heq]
    unfold Task3b37bc2419c6ad18e55c6e6b_thetaErr Task3b37bc2419c6ad18e55c6e6b_psiErr
    rw [hlog]
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  have hbr : 12 * Real.pi + 8 * Real.pi * Real.log 4 +
      (2 / 3 + 16 / 1000) * Real.pi * Real.log x ≤
      4 * Real.log Real.pi * (Real.log x - Real.log Real.pi) - Real.log x / 10 := by
    have hpu : Real.pi * Real.log x ≤ 3.15 * Real.log x :=
      mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_d2]) hu0.le
    have hpl : Real.pi * Real.log 4 ≤ 3.15 * 1.39 := by
      calc Real.pi * Real.log 4 ≤ 3.15 * Real.log 4 :=
            mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_d2]) hlog4pos.le
        _ ≤ 3.15 * 1.39 := by linarith
    have hLu : 1.09 * (Real.log x - 1.17) ≤
        Real.log Real.pi * (Real.log x - Real.log Real.pi) := by
      calc 1.09 * (Real.log x - 1.17)
          ≤ 1.09 * (Real.log x - Real.log Real.pi) := by linarith
        _ ≤ Real.log Real.pi * (Real.log x - Real.log Real.pi) :=
            mul_le_mul_of_nonneg_right hLlo (by linarith)
    have hL2 : Real.log Real.pi ^ 2 ≤ 1.3689 := by nlinarith
    linarith [Real.pi_lt_d2]
  have hfin : Real.sqrt x * Real.log x / 10 ≥
      60 * Real.pi + 800024 * Real.pi * Real.log x +
        (Real.log x - 2 * Real.log Real.pi) ^ 2 := by
    have hq : (Real.log x - 2 * Real.log Real.pi) ^ 2 ≤ Real.log x * Real.log x := by
      nlinarith [hL0, hLhi, hu42]
    have hlin : Real.log x + 2520081 ≤ Real.sqrt x / 10 := by linarith
    have hmul := mul_le_mul_of_nonneg_right hlin hu0.le
    have hp800 : 800024 * Real.pi * Real.log x ≤ 2520076 * Real.log x := by
      have : 800024 * Real.pi ≤ 2520076 := by linarith [Real.pi_lt_d2]
      exact mul_le_mul_of_nonneg_right this hu0.le
    have h60 : 60 * Real.pi ≤ 189 := by linarith [Real.pi_lt_d2]
    linarith
  have hsbr : Real.sqrt x * (12 * Real.pi + 8 * Real.pi * Real.log 4 +
      2 / 3 * Real.pi * Real.log x) + 16 * Real.pi * x ^ (1 / 3 : ℝ) * Real.log x ≤
      Real.sqrt x * (4 * Real.log Real.pi * (Real.log x - Real.log Real.pi) -
        Real.log x / 10) := by
    have hpos : 0 ≤ 16 * Real.pi * Real.log x := by positivity
    have h1 := mul_le_mul_of_nonneg_left hx13 hpos
    have h2 := mul_le_mul_of_nonneg_left hbr hs0
    linarith
  have hkey : 4 * Real.sqrt x * Real.log Real.pi * (Real.log x - Real.log Real.pi) ≥
      12 * Real.pi * (Real.sqrt x + 1) + 48 * Real.pi +
      8 * Real.pi * Real.log 4 * Real.sqrt x +
      16 * Real.pi * x ^ (1 / 3 : ℝ) * Real.log x +
      8 * Real.pi * Real.log x * (Real.sqrt x / 12 + 100003) +
      (Real.log x - 2 * Real.log Real.pi) ^ 2 := by
    linarith
  have hmain : (Task3b37bc2419c6ad18e55c6e6b_thetaErr x / Real.log x + Real.sqrt x / 12 + 100003) *
      (8 * Real.pi * Real.log x) ≤ Real.sqrt x * Real.log x * Real.log x := by
    have hrew : (Task3b37bc2419c6ad18e55c6e6b_thetaErr x / Real.log x + Real.sqrt x / 12 + 100003) *
        (8 * Real.pi * Real.log x) =
        8 * Real.pi * Task3b37bc2419c6ad18e55c6e6b_thetaErr x +
          8 * Real.pi * Real.log x * (Real.sqrt x / 12 + 100003) := by
      have hu0' : Real.log x ≠ 0 := hu0.ne'
      have hp0 : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      ring
    rw [hrew]
    have hid : Real.sqrt x * (Real.log x - 2 * Real.log Real.pi) ^ 2 +
        4 * Real.sqrt x * Real.log Real.pi * (Real.log x - Real.log Real.pi) =
        Real.sqrt x * Real.log x * Real.log x := by ring
    linarith
  have hpos : 0 < 8 * Real.pi * Real.log x := by positivity
  have hfin' : Task3b37bc2419c6ad18e55c6e6b_thetaErr x / Real.log x + Real.sqrt x / 12 + 100003 ≤
      Real.sqrt x * Real.log x * Real.log x / (8 * Real.pi * Real.log x) :=
    (le_div_iff₀ hpos).mpr hmain
  have hdiv : Real.sqrt x * Real.log x * Real.log x / (8 * Real.pi * Real.log x) =
      Real.sqrt x * Real.log x / (8 * Real.pi) := by
    have hp0 : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  linarith
-- @end Task3b37bc2419c6ad18e55c6e6b_final_numeric

-- @helper Task3b37bc2419c6ad18e55c6e6b_log_integral
theorem Task3b37bc2419c6ad18e55c6e6b_log_integral (x : ℝ) (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, (1 : ℝ) / Real.log t) =
      x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) x, HasDerivAt (fun t : ℝ => t / Real.log t)
      (1 / Real.log t - 1 / Real.log t ^ 2) t := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := by
      rw [Set.uIcc_of_le hx] at ht
      exact ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    have h := (hasDerivAt_id' t).div (Real.hasDerivAt_log ht0) hlog
    refine h.congr_deriv ?_
    field_simp
  have hint1 : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / Real.log t)
      MeasureTheory.volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    have ht2 : (2 : ℝ) ≤ t := by
      rw [Set.uIcc_of_le hx] at ht
      exact ht.1
    have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    refine ContinuousAt.continuousWithinAt ?_
    exact continuousAt_const.div (Real.continuousAt_log (by linarith)) hlog
  have hint2 : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / Real.log t ^ 2)
      MeasureTheory.volume 2 x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have hftc : (∫ t in (2 : ℝ)..x, ((1 : ℝ) / Real.log t - 1 / Real.log t ^ 2)) =
      x / Real.log x - 2 / Real.log 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.sub hint2)
  rw [intervalIntegral.integral_sub hint1 hint2] at hftc
  linarith
-- @end Task3b37bc2419c6ad18e55c6e6b_log_integral

theorem Conjectures.Cuts.Task3b37bc2419c6ad18e55c6e6b :
    (∀ (x1 : ℕ) [x2 : NeZero x1] (x3 : DirichletCharacter ℂ x1) (x4 : ℂ), (1 / 2 : ℝ) < x4.re → x3 ≠ (1 : DirichletCharacter ℂ x1) ∨ x4 ≠ (1 : ℂ) → DirichletCharacter.LFunction x3 x4 ≠ (0 : ℂ)) → ∀ (x2 : ℝ), (4 : ℝ) * (10 : ℝ) ^ (18 : ℕ) ≤ x2 → |↑(Finset.filter Nat.Prime (Finset.range (⌊x2⌋₊ + (1 : ℕ)))).card - ((∫ (x4 : ℝ) in (2 : ℝ)..x2, (1 : ℝ) / Real.log x4) + (Real.eulerMascheroniConstant + Real.log (Real.log (2 : ℝ)) + ∑' (x4 : ℕ), Real.log (2 : ℝ) ^ (x4 + (1 : ℕ)) / (↑(x4 + (1 : ℕ)) * ↑(x4 + (1 : ℕ)).factorial)))| ≤ √x2 * Real.log x2 / ((8 : ℝ) * Real.pi) := by
  intro hGRH x hx
  have hx4 : (4 : ℝ) * (10 : ℝ) ^ (18 : ℕ) = 4 * 10 ^ 18 := by norm_num
  have hx2 : (2 : ℝ) ≤ x := by
    have : (2 : ℝ) ≤ 4 * 10 ^ 18 := by norm_num
    linarith
  have hx2500 : (2500 : ℝ) ≤ x := by
    have : (2500 : ℝ) ≤ 4 * 10 ^ 18 := by norm_num
    linarith
  -- the premise at modulus 1 is RH for the Riemann zeta function
  have hhalf : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → riemannZeta s ≠ 0 := by
    intro s hs hs1
    haveI : NeZero (1 : ℕ) := ⟨by norm_num⟩
    have h0 := hGRH 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
    rwa [DirichletCharacter.LFunction_modOne_eq] at h0
  have hRH : RiemannHypothesis := Task3b37bc2419c6ad18e55c6e6b_rh_of_halfplane hhalf
  -- the constant of the logarithmic integral at 2
  set K : ℝ := Real.eulerMascheroniConstant + Real.log (Real.log (2 : ℝ)) +
    ∑' (x4 : ℕ), Real.log (2 : ℝ) ^ (x4 + (1 : ℕ)) /
      (↑(x4 + (1 : ℕ)) * ↑(x4 + (1 : ℕ)).factorial)
  have hK : |K - 2 / Real.log 2| ≤ 3 := Task3b37bc2419c6ad18e55c6e6b_li_two
  -- Abel summation: pi in terms of theta (Mathlib), and the main term by integration by parts
  have hcard : ((Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1))).card : ℝ) =
      (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  have hpi : ((Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1))).card : ℝ) =
      Chebyshev.theta x / Real.log x +
        ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2) := by
    rw [hcard]
    exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2
  have hL : (∫ t in (2 : ℝ)..x, (1 : ℝ) / Real.log t) =
      x / Real.log x - 2 / Real.log 2 + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 :=
    Task3b37bc2419c6ad18e55c6e6b_log_integral x hx2
  have hint1 : IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / (t * Real.log t ^ 2))
      MeasureTheory.volume 2 x := by
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx2).mpr
      (Chebyshev.integrableOn_theta_div_id_mul_log_sq x)
  have hint2 : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / Real.log t ^ 2)
      MeasureTheory.volume 2 x :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have hcomb : (∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * Real.log t ^ 2)) -
      (∫ t in (2 : ℝ)..x, (1 : ℝ) / Real.log t ^ 2) =
      ∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_sub hint1 hint2]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht2 : (2 : ℝ) ≤ t := by
      rw [Set.uIcc_of_le hx2] at ht
      exact ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : Real.log t ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    field_simp
  have hdecomp : ((Finset.filter Nat.Prime (Finset.range (⌊x⌋₊ + 1))).card : ℝ) -
      ((∫ t in (2 : ℝ)..x, (1 : ℝ) / Real.log t) + K) =
      (Chebyshev.theta x - x) / Real.log x +
        (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) -
        (K - 2 / Real.log 2) := by
    rw [hpi, hL, ← hcomb]
    ring
  -- the three error terms
  have hθ : |Chebyshev.theta x - x| ≤ Task3b37bc2419c6ad18e55c6e6b_thetaErr x :=
    Task3b37bc2419c6ad18e55c6e6b_theta_err hRH x hx2500
  have hint : |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
      Real.sqrt x / 12 + (10 : ℝ) ^ (5 : ℕ) :=
    Task3b37bc2419c6ad18e55c6e6b_theta_integral hRH x hx
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hnum := Task3b37bc2419c6ad18e55c6e6b_final_numeric x hx
  have h10 : (10 : ℝ) ^ (5 : ℕ) = 100000 := by norm_num
  have hint' : |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| ≤
      Real.sqrt x / 12 + 100000 := by
    rw [h10] at hint
    linarith
  have hsplit : |(Chebyshev.theta x - x) / Real.log x +
      (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) -
        (K - 2 / Real.log 2)| ≤
      Task3b37bc2419c6ad18e55c6e6b_thetaErr x / Real.log x + Real.sqrt x / 12 + 100003 := by
    have hc : |(Chebyshev.theta x - x) / Real.log x| ≤
        Task3b37bc2419c6ad18e55c6e6b_thetaErr x / Real.log x := by
      rw [abs_div, abs_of_pos hlogx]
      exact div_le_div_of_nonneg_right hθ hlogx.le
    calc |(Chebyshev.theta x - x) / Real.log x +
          (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) -
          (K - 2 / Real.log 2)|
        ≤ |(Chebyshev.theta x - x) / Real.log x +
            (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2))| +
            |K - 2 / Real.log 2| := by
          have := abs_sub_le
            ((Chebyshev.theta x - x) / Real.log x +
              (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)))
            0 (K - 2 / Real.log 2)
          simp only [sub_zero, zero_sub, abs_neg] at this
          linarith
      _ ≤ |(Chebyshev.theta x - x) / Real.log x| +
            |∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2)| +
            |K - 2 / Real.log 2| := by
          have := abs_add_le ((Chebyshev.theta x - x) / Real.log x)
            (∫ t in (2 : ℝ)..x, (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
          linarith
      _ ≤ Task3b37bc2419c6ad18e55c6e6b_thetaErr x / Real.log x +
            (Real.sqrt x / 12 + 100000) + 3 := by
          linarith
      _ = Task3b37bc2419c6ad18e55c6e6b_thetaErr x / Real.log x + Real.sqrt x / 12 + 100003 := by
          ring
  rw [hdecomp]
  linarith
