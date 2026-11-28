import Mathlib
import PEqualNP.Outside.L_goldbach_arc_major_floor
import Conjectures.Goldbach.ExceptionFourSeventhsCountingBridge
import Conjectures.Goldbach.FiniteMajorRescaledIntervalKernel
import Conjectures.Goldbach.FiniteMajorSincMass
import Conjectures.Goldbach.ReflectedMeanSquareEulerTail

-- The kernel approximation and cutoff-sensitive error reuse the argument in PR 4609.

namespace GoldbachRawKernel

open Finset MeasureTheory
open GoldbachMajorArc
open Conjectures.Goldbach.FiniteMajorSincMass_aux (sinc_sq_nonneg sinc_sq_le_one
  sinc_sq_even sinc_sq_integrable)
open scoped Interval

noncomputable section

/-- The rescaled symmetric sinc mass. -/
def profile (h : ℝ) : ℝ :=
  ∫ t in -h..h, Real.sinc (Real.pi*t)^2

theorem profile_bounds (h : ℝ) (hh : 0 ≤ h) : 0 ≤ profile h ∧ profile h ≤ 1 := by
  rcases hh.eq_or_lt with hzero | hpos
  · simp [profile, ← hzero]
  · have hmain := Conjectures.Goldbach.FiniteMajorSincMass h hpos
    exact ⟨hmain.1, hmain.2.1⟩

private theorem profile_eq_twice (h : ℝ) :
    profile h = 2*(∫ t in (0:ℝ)..h, Real.sinc (Real.pi*t)^2) := by
  let f (t : ℝ) := Real.sinc (Real.pi*t)^2
  have hf : Integrable f := sinc_sq_integrable
  have hneg : (∫ t in -h..(0:ℝ), f t) = ∫ t in (0:ℝ)..h, f t := by
    calc
      (∫ t in -h..(0:ℝ), f t) = ∫ t in -h..(0:ℝ), f (-t) := by
        simp only [f, sinc_sq_even]
      _ = _ := by rw [intervalIntegral.integral_comp_neg, neg_zero, neg_neg]
  change (∫ t in -h..h, f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable : IntervalIntegrable f volume (-h) 0)
      (hf.intervalIntegrable : IntervalIntegrable f volume 0 h), hneg, two_mul]

/-- The annular change is twice the mass of the positive interval. -/
theorem profile_sub_eq (h k : ℝ) :
    profile k - profile h = 2*(∫ t in h..k, Real.sinc (Real.pi*t)^2) := by
  let f (t : ℝ) := Real.sinc (Real.pi*t)^2
  have hf : Integrable f := sinc_sq_integrable
  rw [profile_eq_twice k, profile_eq_twice h]
  change 2*(∫ t in (0:ℝ)..k, f t) - 2*(∫ t in (0:ℝ)..h, f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable : IntervalIntegrable f volume 0 h)
      (hf.intervalIntegrable : IntervalIntegrable f volume h k)]
  ring

theorem profile_sub_bounds {h k : ℝ} (hk : h ≤ k) :
    0 ≤ profile k - profile h ∧ profile k - profile h ≤ 2*(k-h) := by
  let f (t : ℝ) := Real.sinc (Real.pi*t)^2
  have hf : Integrable f := sinc_sq_integrable
  rw [profile_sub_eq]
  constructor
  · exact mul_nonneg (by norm_num)
      (intervalIntegral.integral_nonneg hk fun t _ => sinc_sq_nonneg t)
  · have hmono := intervalIntegral.integral_mono_on hk (hf.intervalIntegrable : IntervalIntegrable f volume h k)
      (intervalIntegrable_const (c := (1:ℝ))) (fun t _ => sinc_sq_le_one t)
    have h' : (∫ t in h..k, f t) ≤ k-h := by simpa using hmono
    exact mul_le_mul_of_nonneg_left h' (by norm_num)

private theorem phase_add (u v : ℝ) : phase (u+v) = phase u * phase v := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem shifted_kernel_norm (n : ℕ) (t : ℝ) :
    ‖∑ k ∈ Icc 1 (n+1), phase ((k:ℝ)*t)‖ = ‖kernel n t‖ := by
  have h :
      (∑ k ∈ Icc 1 (n+1), phase ((k:ℝ)*t)) =
        phase t * kernel n t := by
    calc
      _ = ∑ k ∈ range (n+1), phase (((k+1:ℕ):ℝ)*t) := by
        symm
        refine sum_bij' (fun k _ => k+1) (fun k _ => k-1) ?_ ?_ ?_ ?_ ?_
        · intro k hk
          exact mem_Icc.mpr ⟨by omega, by have := mem_range.mp hk; omega⟩
        · intro k hk
          have := mem_Icc.mp hk
          exact mem_range.mpr (by omega)
        · intro k hk
          omega
        · intro k hk
          have := (mem_Icc.mp hk).1
          omega
        · intro k _
          rfl
      _ = _ := by
        rw [kernel, mul_sum]
        apply sum_congr rfl
        intro k _
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm, phase_add]
  rw [h, norm_mul, show ‖phase t‖ = 1 from Complex.norm_exp_ofReal_mul_I _, one_mul]

/-- Compare the published geometric kernel to the same sinc profile at fixed width. -/
theorem kernel_mass_error (n q Q : ℕ) (hn : 0 < n) (hq : 0 < q) :
    |kernelMass n ((Q:ℝ)/((q:ℝ)*(n:ℝ))) - ((n:ℝ)+1)*profile ((Q:ℝ)/(q:ℝ))| ≤
      (16*Real.pi+2)*((Q:ℝ)+1)^2 := by
  let N := n+1
  let K : ℝ := (Q:ℝ)/(q:ℝ)
  let H : ℝ := K*(N:ℝ)/(n:ℝ)
  let b : ℝ := (Q:ℝ)/((q:ℝ)*(n:ℝ))
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnR₁ : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq
  have hqR₁ : 1 ≤ (q:ℝ) := by exact_mod_cast hq
  have hN0 : 0 < N := by dsimp [N]; omega
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast hN0
  have hNcast : (N:ℝ) = (n:ℝ)+1 := by simp [N]
  have hNle : (N:ℝ) ≤ 2*(n:ℝ) := by rw [hNcast]; linarith only [hnR₁]
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hKQ : K ≤ (Q:ℝ) := div_le_self (by positivity) hqR₁
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hHb : H/(N:ℝ) = b := by
    dsimp [H,b,K]
    field_simp [hnR.ne', hqR.ne', hNpos.ne']
  have hHsub : H-K = K/(n:ℝ) := by
    dsimp only [H]
    rw [hNcast]
    field_simp [hnR.ne']
    ring
  have hHK : K ≤ H := sub_nonneg.mp (by rw [hHsub]; positivity)
  have hHle : H ≤ 2*K := by
    apply (div_le_iff₀ hnR).mpr
    calc
      K*(N:ℝ) ≤ K*(2*(n:ℝ)) := mul_le_mul_of_nonneg_left hNle hK0
      _ = _ := by ring
  have hHRQ : H ≤ 2*(Q:ℝ) :=
    hHle.trans (mul_le_mul_of_nonneg_left hKQ (by norm_num))
  have hres := (Conjectures.Goldbach.FiniteMajorRescaledIntervalKernel N H hN0 hH0).2.2
  change |(∫ t in -(H/(N:ℝ))..H/(N:ℝ),
      ‖∑ k ∈ Icc 1 N, phase ((k:ℝ)*t)‖^2)/(N:ℝ) - profile H| ≤ _ at hres
  simp_rw [show ∀ t : ℝ, ‖∑ k ∈ Icc 1 N, phase ((k:ℝ)*t)‖ = ‖kernel n t‖
    from shifted_kernel_norm n] at hres
  rw [hHb] at hres
  change |kernelMass n b/(N:ℝ) - profile H| ≤ 4*Real.pi*H^2/(N:ℝ) at hres
  have he : kernelMass n b/(N:ℝ) - profile H =
      (kernelMass n b - (N:ℝ)*profile H)/(N:ℝ) := by
    field_simp [hNpos.ne']
  rw [he, abs_div, abs_of_pos hNpos] at hres
  have hscaled : |kernelMass n b - (N:ℝ)*profile H| ≤ 4*Real.pi*H^2 :=
    (div_le_div_iff_of_pos_right hNpos).mp hres
  have hscaled' : |kernelMass n b - (N:ℝ)*profile H| ≤ 16*Real.pi*(Q:ℝ)^2 := by
    apply hscaled.trans
    calc
      _ ≤ 4*Real.pi*(2*(Q:ℝ))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 hHRQ 2) (by positivity)
      _ = _ := by ring
  have hProfile : (N:ℝ)*|profile H-profile K| ≤ 4*(Q:ℝ) := by
    have hp := profile_sub_bounds hHK
    have hNdiv : (N:ℝ)/(n:ℝ) ≤ 2 := (div_le_iff₀ hnR).mpr hNle
    rw [abs_of_nonneg hp.1]
    calc
      _ ≤ (N:ℝ)*(2*(H-K)) := mul_le_mul_of_nonneg_left hp.2 hNpos.le
      _ = (2*K)*((N:ℝ)/(n:ℝ)) := by rw [hHsub]; ring
      _ ≤ (2*K)*2 := mul_le_mul_of_nonneg_left hNdiv (by positivity)
      _ = 4*K := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hKQ (by norm_num)
  have htri := abs_sub_le (kernelMass n b) ((N:ℝ)*profile H) ((N:ℝ)*profile K)
  rw [← mul_sub, abs_mul, abs_of_pos hNpos] at htri
  change |kernelMass n b - ((n:ℝ)+1)*profile K| ≤ _
  rw [← hNcast]
  have hsum := htri.trans (add_le_add hscaled' hProfile)
  apply hsum.trans
  have hQ0 : 0 ≤ (Q:ℝ) := by positivity
  have hdiff : (Q:ℝ)^2 ≤ ((Q:ℝ)+1)^2 := by nlinarith only [hQ0]
  have hpi := mul_le_mul_of_nonneg_left hdiff (show 0 ≤ 16*Real.pi by positivity)
  nlinarith only [hpi, sq_nonneg (Q:ℝ)]


end
end GoldbachRawKernel

-- The single-arc estimates and the finite summation below adapt the verified
-- Goldbach major-arc proof in PR 316, released under Apache 2.0.
namespace GoldbachRawError

open GoldbachMajorArc Finset Filter MeasureTheory
open scoped Topology

noncomputable section

private theorem unitMean_norm (q a : ℕ) (hq : 0 < q) : ‖unitMean q a‖ ≤ 1 := by
  let U := (range q).filter (fun r => r.Coprime q)
  have hcard : U.card = q.totient := by
    rw [Nat.totient_eq_card_coprime]
    have h : U = (range q).filter (fun r => q.Coprime r) := by ext k; simp [U, Nat.coprime_comm]
    rw [h]
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  unfold unitMean
  rw [norm_div, Complex.norm_natCast, div_le_one hφ]
  refine (norm_sum_le _ _).trans ?_
  change ∑ r ∈ U, ‖phase ((r : ℝ) * ((a : ℝ) / q))‖ ≤ _
  simp only [phase, Complex.norm_exp_ofReal_mul_I, sum_const, nsmul_eq_mul, mul_one, hcard, le_refl]

private theorem integral_error_bound {n q : ℕ} (hn : 1 ≤ n) (hq : 0 < q) (hQ : q ≤ cutoff n)
    (a : ℕ) {E : ℝ} (hE : 0 ≤ E)
    (hp : prefixError n ((a : ℝ) / q) (unitMean q a) ≤ q * E) :
    (∫ β in -(width n q)..(width n q), modelError n q a β) ≤
      2 * (cutoff n : ℝ) ^ 2 * E * ((1 + 2 * Real.pi) * (Real.log 4 + 2)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hQ' : (q : ℝ) ≤ cutoff n := by exact_mod_cast hQ
  have npos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn'
  have qpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq'
  let B := E * ((1 + 2 * Real.pi) * (cutoff n : ℝ)) * ((Real.log 4 + 2) * (n : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have wpos : 0 ≤ width n q := by unfold width; positivity
  have hlength : width n q ≤ (cutoff n : ℝ) / n := by
    unfold width
    apply div_le_div_of_nonneg_left (by positivity) npos
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right hq' npos.le)
  have hpoint {β : ℝ} (hβ : β ∈ Set.Icc (-(width n q)) (width n q)) :
      modelError n q a β ≤ B := by
    have hp' := squared_arc_error (a := a) hn hq (abs_le.mpr hβ)
    have hscale :
        prefixError n ((a : ℝ) / q) (unitMean q a) * (1 + 2 * Real.pi * ((cutoff n : ℝ) / q)) ≤
        E * ((1 + 2 * Real.pi) * (cutoff n : ℝ)) := by
      calc
        _ ≤ ((q : ℝ) * E) * (1 + 2 * Real.pi * ((cutoff n : ℝ) / q)) :=
          mul_le_mul_of_nonneg_right hp (by positivity)
        _ = E * ((q : ℝ) + 2 * Real.pi * cutoff n) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith only [hQ']) hE
    have hU := unitMean_norm q a hq
    have hcap : Chebyshev.theta n + ‖unitMean q a‖ * (n + 1 : ℕ) ≤ (Real.log 4 + 2) * (n : ℝ) := by
      have hcard := mul_le_mul_of_nonneg_right hU (show 0 ≤ (n : ℝ) + 1 by positivity)
      push_cast
      nlinarith only [Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n), hcard, hn']
    exact hp'.trans (mul_le_mul hscale hcap (by positivity) (by positivity))
  have hc : Continuous (modelError n q a) := by
    unfold modelError integrand primeSum kernel phase
    fun_prop
  calc
    _ ≤ ∫ _β in -(width n q)..(width n q), B :=
      intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
        (by simp) (fun β hβ => hpoint hβ)
    _ = (2 * width n q) * B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    _ ≤ (2 * ((cutoff n : ℝ) / n)) * B :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlength (by norm_num)) hB
    _ = _ := by dsimp [B]; field_simp

/-- The old arc approximation error saves an additional factor of its cutoff. -/
theorem eventually_totalArcError_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, totalArcError n ≤ η * (n : ℝ) / (cutoff n : ℝ) := by
  obtain ⟨M, hM, hpre⟩ := uniform_prefix_error
  let C : ℝ := 4 * ((1 + 2 * Real.pi) * (Real.log 4 + 2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlimit := (envelope_saving M).const_mul (C * 16 ^ 5)
  simp only [mul_zero] at hlimit
  filter_upwards [hpre, eventually_ge_atTop (2 : ℕ), hlimit.eventually_lt_const hη]
    with n hp hn hsmall
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hQ1 : 1 ≤ cutoff n := GoldbachMajorArc.cutoff_positive n
  have hQ' : (1 : ℝ) ≤ cutoff n := by exact_mod_cast hQ1
  have hQpos : 0 < (cutoff n : ℝ) := zero_lt_one.trans_le hQ'
  have hE : 0 ≤ errorEnvelope M n := by unfold errorEnvelope; positivity
  let B : ℝ := 2 * (cutoff n : ℝ) ^ 2 * errorEnvelope M n * ((1 + 2 * Real.pi) * (Real.log 4 + 2))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have htot : totalArcError n ≤ C * (cutoff n : ℝ) ^ 4 * errorEnvelope M n := by
    unfold totalArcError
    calc
      _ ≤ ∑ _q ∈ Icc 1 (cutoff n), (((cutoff n : ℝ) + 1) * B) := by
        refine sum_le_sum fun q hq => ?_
        have hq' := mem_Icc.mp hq
        calc
          _ ≤ ∑ _a ∈ range (q + 1), B := sum_le_sum fun a _ =>
            integral_error_bound hn1 hq'.1 hq'.2 a hE (hp q a hq'.1 hq'.2)
          _ = ((q : ℝ) + 1) * B := by simp
          _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hq'.2 1) hB
      _ = (cutoff n : ℝ) * (((cutoff n : ℝ) + 1) * B) := by simp [Nat.card_Icc]
      _ ≤ (cutoff n : ℝ) * ((2 * (cutoff n : ℝ)) * B) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hB) hQpos.le
      _ = _ := by dsimp [B, C]; ring
  have hpow : (cutoff n : ℝ) ^ 5 ≤ 16 ^ 5 * (Real.log n) ^ 10 := by
    calc
      _ ≤ (16 * (Real.log n) ^ 2) ^ 5 := pow_le_pow_left₀ hQpos.le (cutoff_le_log_sq hn) 5
      _ = _ := by ring
  have hscaled : totalArcError n * (cutoff n : ℝ) / n ≤ η := by
    calc
      _ ≤ (C * (cutoff n : ℝ) ^ 4 * errorEnvelope M n) * (cutoff n : ℝ) / n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htot hQpos.le) hnpos.le
      _ = C * (cutoff n : ℝ) ^ 5 * errorEnvelope M n / n := by ring
      _ ≤ C * (16 ^ 5 * (Real.log n) ^ 10) * errorEnvelope M n / n :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) hE) hnpos.le
      _ = (C * 16 ^ 5) * ((Real.log n) ^ 10 * errorEnvelope M n / n) := by ring
      _ ≤ η := hsmall.le
  exact (le_div_iff₀ hQpos).mpr ((div_le_iff₀ hnpos).mp hscaled)

theorem totalArcError_cutoff_saving (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, totalArcError n ≤ η * (n : ℝ) / (cutoff n : ℝ) :=
  eventually_atTop.mp (eventually_totalArcError_le hη)

end

end GoldbachRawError

namespace GoldbachRawGrowth

open Finset Filter
open scoped BigOperators Topology

/-- A negative total on a subset forces a square-energy lower bound on
the containing set. -/
theorem energy_ge_of_sum_le_neg {ι : Type*} {s t : Finset ι} (hst : s ⊆ t)
    (f : ι → ℝ) {A K : ℝ} (hA : 0 ≤ A) (hcard : (s.card:ℝ) ≤ K)
    (hsum : (∑ n ∈ s, f n) ≤ -A) :
    A^2 ≤ K * ∑ n ∈ t, (f n)^2 := by
  have hK : 0 ≤ K := (Nat.cast_nonneg s.card).trans hcard
  have hs : A ≤ -(∑ n ∈ s, f n) := by linarith only [hsum]
  calc
    A^2 ≤ (∑ n ∈ s, f n)^2 := by
      simpa only [neg_sq] using pow_le_pow_left₀ hA hs 2
    _ ≤ (s.card:ℝ) * ∑ n ∈ s, (f n)^2 := by
      simpa using sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) f
    _ ≤ K * ∑ n ∈ t, (f n)^2 := mul_le_mul hcard
      (sum_le_sum_of_subset_of_nonneg hst (fun _ _ _ => sq_nonneg _))
      (sum_nonneg (fun _ _ => sq_nonneg _)) hK

/-- Every fixed power of the dyadic level is negligible compared to every
positive power of the dyadic scale. -/
theorem eventually_dyadic_log_power_le_pow (d : ℕ) {α η : ℝ}
    (hα : 0 < α) (hη : 0 < η) :
    ∀ᶠ k : ℕ in atTop, (k:ℝ)^d ≤ η * (((2^k:ℕ):ℝ)^α) := by
  have ht : Tendsto (fun k : ℕ => (2:ℝ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hlim := (tendsto_rpow_atTop hα).comp ht
  let D : ℝ := (α*Real.log 2)^d
  have hD : 0 < D := by exact pow_pos (mul_pos hα (Real.log_pos (by norm_num))) _
  have hb := ((Real.isLittleO_pow_log_id_atTop (n:=d)).comp_tendsto hlim).bound
    (mul_pos hη hD)
  filter_upwards [hb] with k hk
  have h₂ : 0 < (2:ℝ)^k := by positivity
  have hx : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have heq : Real.log (((2:ℝ)^k)^α) ^ d = D*((k:ℝ)^d) := by
    rw [Real.log_rpow h₂, Real.log_pow]
    rw [show α*((k:ℝ)*Real.log 2) = (α*Real.log 2)*(k:ℝ) by ring, mul_pow]
  change ‖Real.log (((2:ℝ)^k)^α) ^ d‖ ≤ η*D*‖((2:ℝ)^k)^α‖ at hk
  rw [heq, Real.norm_of_nonneg (mul_nonneg hD.le (pow_nonneg hx _)),
    Real.norm_of_nonneg (Real.rpow_nonneg h₂.le α)] at hk
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  apply le_of_mul_le_mul_left _ hD
  calc
    _ ≤ η*D*((2:ℝ)^k)^α := hk
    _ = _ := by ring

end GoldbachRawGrowth

namespace GoldbachDyadicCoefficient

open Finset Filter MeasureTheory GoldbachMajorArc
open scoped Topology

noncomputable section

def minor (n : ℕ) : ℝ :=
  (∫ t in (0:ℝ)..1, (arcs n)ᶜ.indicator (integrand n) t).re

def convolution (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (n+1), primeWeight p * primeWeight (n-p)

theorem minor_add_major (n : ℕ) :
    minor n + (majorContribution n).re = convolution n := by
  have h : majorContribution n +
      (∫ t in (0:ℝ)..1, (arcs n)ᶜ.indicator (integrand n) t) = (convolution n : ℂ) :=
    Conjectures.Goldbach.FourSevenths.Coefficient n
  simpa only [minor, Complex.add_re, Complex.ofReal_re, add_comm] using congrArg Complex.re h

theorem pow_two_ge_four {k : ℕ} (hk : 2 ≤ k) : 4 ≤ (2^k : ℕ) :=
  Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hk

theorem cutoff_dyadic {k n : ℕ} (hl : 2^k ≤ n) (hu : n ≤ 2*(2^k)-3)
    (hk : 2 ≤ k) : cutoff n = k^2 := by
  have hlog₁ : k ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have h4 := pow_two_ge_four hk
  have hlog₂ : Nat.log 2 (n+2) < k+1 := by
    apply Nat.log_lt_of_lt_pow (by omega)
    rw [pow_succ]
    omega
  rw [cutoff, show Nat.log 2 (n+2)=k by omega]

end
end GoldbachDyadicCoefficient

/-! The coefficient periodicity, progression sums, and norm bound come
from the checked reflected mean-square proof, PR 4435. The affine estimate
generalizes the earlier odd-progression calculation. -/

namespace GoldbachEvenCancel

open Finset

private theorem prefix_eq_remainder {A : Type*} [AddCommMonoid A] (g : ℕ → A)
    (q L : ℕ) (hperiod : ∀ j, g (j+q) = g j)
    (hzero : ∑ j ∈ range q, g j = 0) :
    (∑ j ∈ range L, g j) = ∑ j ∈ range (L % q), g j := by
  have hshift (k j : ℕ) : g (k*q+j) = g j := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, show k*q+q+j = (k*q+j)+q by omega, hperiod, ih]
  have hblocks (k : ℕ) : (∑ j ∈ range (k*q), g j) = 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul, sum_range_add, ih, zero_add]
      simpa only [hshift k] using hzero
  have hL : (L/q)*q + L % q = L := by simpa only [Nat.mul_comm] using Nat.div_add_mod L q
  conv_lhs => rw [← hL, sum_range_add, hblocks, zero_add]
  simp only [hshift]

private theorem affine_smul_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℕ → E) (b D L : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hprefix : ∀ j, ‖∑ i ∈ range j, g i‖ ≤ R) :
    ‖∑ j ∈ range L, (((b : ℝ)+(D : ℝ)*(j : ℝ)+1) • g j)‖ ≤
      ((b : ℝ)+2*(D : ℝ)*(L : ℝ)+1)*R := by
  let f (j : ℕ) : ℝ := (b : ℝ)+(D : ℝ)*(j : ℝ)+1
  let G (j : ℕ) : E := ∑ i ∈ range j, g i
  have hslope (j : ℕ) : f (j+1)-f j = D := by
    unfold f
    push_cast
    ring
  have hende : ‖f (L-1) • G L‖ ≤ ((b : ℝ)+(D : ℝ)*(L : ℝ)+1)*R := by
    have hf : 0 ≤ f (L-1) := by unfold f; positivity
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hf]
    refine mul_le_mul ?_ (hprefix L) (norm_nonneg _) (by positivity)
    have hL : ((L-1 : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.sub_le L 1
    unfold f
    gcongr
  have hrem : ‖∑ j ∈ range (L-1), (D : ℝ) • G (j+1)‖ ≤ (D : ℝ)*(L : ℝ)*R := by
    calc
      _ ≤ ∑ j ∈ range (L-1), ‖(D : ℝ) • G (j+1)‖ := norm_sum_le _ _
      _ ≤ ∑ _j ∈ range (L-1), (D : ℝ)*R := by
        apply sum_le_sum
        intro j _
        rw [norm_smul, Real.norm_natCast]
        exact mul_le_mul_of_nonneg_left (hprefix (j+1)) (Nat.cast_nonneg D)
      _ = ((L-1 : ℕ) : ℝ) * ((D : ℝ)*R) := by simp [sum_const, nsmul_eq_mul]
      _ ≤ (L : ℝ) * ((D : ℝ)*R) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le L 1) (by positivity)
      _ = _ := by ring
  change ‖∑ j ∈ range L, f j • g j‖ ≤ _
  rw [sum_range_by_parts]
  change ‖f (L-1) • G L - ∑ j ∈ range (L-1), (f (j+1)-f j) • G (j+1)‖ ≤ _
  simp_rw [hslope]
  calc
    _ ≤ ‖f (L-1) • G L‖ + ‖∑ j ∈ range (L-1), (D : ℝ) • G (j+1)‖ := norm_sub_le _ _
    _ ≤ ((b : ℝ)+(D : ℝ)*(L : ℝ)+1)*R + (D : ℝ)*(L : ℝ)*R := add_le_add hende hrem
    _ = _ := by ring

theorem coefficient_norm (q n : ℕ) (hq : 0 < q) :
    ‖GoldbachMajorArc.coefficient q n‖ ≤ 1 :=
  ProgressionSums.coefficient_norm q n hq

theorem affine_bound (q b D L : ℕ) (hq : 0 < q) (hD : ¬ q ∣ D) :
    ‖∑ j ∈ range L, (((b+D*j : ℕ) : ℂ)+1)*GoldbachMajorArc.coefficient q (b+D*j)‖ ≤
      ((b : ℝ)+2*(D : ℝ)*(L : ℝ)+1)*(q : ℝ) := by
  let g (j : ℕ) := GoldbachMajorArc.coefficient q (b+D*j)
  have hperiod (j : ℕ) : g (j+q) = g j := by
    change GoldbachMajorArc.coefficient q (b+D*(j+q)) = GoldbachMajorArc.coefficient q (b+D*j)
    rw [show b+D*(j+q) = (b+D*j)+q*D by ring]
    exact ProgressionZero.coefficient_period_mul q (b+D*j) D hq
  have hzero : (∑ j ∈ range q, g j) = 0 := ProgressionZero.coefficient_sum_zero q b D hq hD
  have hprefix (j : ℕ) : ‖∑ i ∈ range j, g i‖ ≤ (q : ℝ) := by
    rw [prefix_eq_remainder g q j hperiod hzero]
    calc
      _ ≤ ∑ i ∈ range (j % q), ‖g i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ range (j % q), (1 : ℝ) :=
        sum_le_sum (fun i _ => coefficient_norm q (b+D*i) hq)
      _ = ((j % q : ℕ) : ℝ) := by simp
      _ ≤ _ := by exact_mod_cast (Nat.mod_lt j hq).le
  have hweight :
      (∑ j ∈ range L, (((b+D*j : ℕ) : ℂ)+1) * GoldbachMajorArc.coefficient q (b+D*j)) =
        ∑ j ∈ range L, (((b : ℝ)+(D : ℝ)*(j : ℝ)+1) • g j) := by
    apply sum_congr rfl
    intro j _
    rw [Complex.real_smul]
    unfold g
    push_cast
    rfl
  rw [hweight]
  exact affine_smul_bound g b D L q (Nat.cast_nonneg q) hprefix

theorem window_bound (X Q D b L : ℕ) (hX : 0 < X) (hb : b ≤ 2*X) (hDL : D*L ≤ 2*X)
    (K : ℕ → ℂ) (hK : ∀ q ∈ (Icc 1 Q).filter (fun q => ¬ q ∣ D), ‖K q‖ ≤ 1) :
    ‖∑ q ∈ (Icc 1 Q).filter (fun q => ¬ q ∣ D), K q *
      (∑ j ∈ range L, (((b+D*j : ℕ) : ℂ)+1)*GoldbachMajorArc.coefficient q (b+D*j))‖ ≤
      8*(X : ℝ)*(Q : ℝ)^2 := by
  let T := (Icc 1 Q).filter (fun q => ¬ q ∣ D)
  let A (q : ℕ) := ∑ j ∈ range L, (((b+D*j : ℕ) : ℂ)+1)*GoldbachMajorArc.coefficient q (b+D*j)
  have hcard : (T.card : ℝ) ≤ Q := by
    exact_mod_cast ((card_filter_le _ _).trans_eq (by simp [Nat.card_Icc]) : T.card ≤ Q)
  have hW : (b : ℝ)+2*(D : ℝ)*(L : ℝ)+1 ≤ 8*(X : ℝ) := by
    have hN : b+2*(D*L)+1 ≤ 8*X := by omega
    have hR : (b : ℝ)+2*((D : ℝ)*(L : ℝ))+1 ≤ 8*(X : ℝ) := by exact_mod_cast hN
    simpa only [mul_assoc] using hR
  change ‖∑ q ∈ T, K q * A q‖ ≤ _
  calc
    _ ≤ ∑ q ∈ T, ‖K q * A q‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ T, 8*(X : ℝ)*(Q : ℝ) := by
      apply sum_le_sum
      intro q hq
      obtain ⟨hqI, hqD⟩ := mem_filter.mp hq
      obtain ⟨hq1, hqQ⟩ := mem_Icc.mp hqI
      have hqR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
      have hA : ‖A q‖ ≤ 8*(X : ℝ)*(q : ℝ) :=
        (affine_bound q b D L hq1 hqD).trans
          (mul_le_mul_of_nonneg_right hW (Nat.cast_nonneg q))
      calc
        ‖K q * A q‖ = ‖K q‖ * ‖A q‖ := norm_mul _ _
        _ ≤ 1*(8*(X : ℝ)*(q : ℝ)) :=
          mul_le_mul (hK q hq) hA (norm_nonneg _) zero_le_one
        _ ≤ _ := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_left hqR (by positivity)
    _ = (T.card : ℝ)*(8*(X : ℝ)*(Q : ℝ)) := by simp [sum_const, nsmul_eq_mul]
    _ ≤ (Q : ℝ)*(8*(X : ℝ)*(Q : ℝ)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

private theorem short_residue_sum (r D a : ℕ) (hr : r ≤ D) :
    (∑ n ∈ range r, if n % D = a then (1 : ℝ) else 0) = if a < r then 1 else 0 := by
  calc
    _ = ∑ n ∈ range r, if n = a then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [Nat.mod_eq_of_lt ((mem_range.mp hn).trans_le hr)]
    _ = _ := by simp

/-- Weighted residue counts on an initial interval differ from their uniform average
by at most a linear boundary error. -/
theorem residue_weight_discrepancy (U D a : ℕ) (hD : 0 < D) (ha : a < D) :
    |(∑ n ∈ (range U).filter (fun n => n % D = a), ((n : ℝ)+1)) -
      (∑ n ∈ range U, ((n : ℝ)+1))/(D : ℝ)| ≤ 2*(U : ℝ)+1 := by
  let g (n : ℕ) : ℝ := (if n % D = a then 1 else 0) - 1/(D : ℝ)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hperiod (j : ℕ) : g (j+D) = g j := by simp [g, Nat.add_mod_right]
  have hzero : (∑ j ∈ range D, g j) = 0 := by
    simp only [g, sum_sub_distrib, short_residue_sum D D a le_rfl, ha, ite_true, sum_const,
      card_range, nsmul_eq_mul]
    field_simp
    ring
  have hprefix (j : ℕ) : ‖∑ i ∈ range j, g i‖ ≤ 1 := by
    have hr : j % D ≤ D := (Nat.mod_lt j hD).le
    rw [prefix_eq_remainder g D j hperiod hzero, Real.norm_eq_abs]
    simp only [g, sum_sub_distrib, short_residue_sum _ D a hr, sum_const, card_range, nsmul_eq_mul]
    have hterm0 : 0 ≤ ((j % D : ℕ) : ℝ) * (1/(D : ℝ)) := by positivity
    have hterm1 : ((j % D : ℕ) : ℝ) * (1/(D : ℝ)) ≤ 1 := by
      rw [mul_one_div, div_le_one hDR]
      exact_mod_cast hr
    split_ifs <;> exact abs_le.mpr ⟨by linarith only [hterm1], by linarith only [hterm0]⟩
  have h := affine_smul_bound g 0 1 U 1 zero_le_one hprefix
  have hterm (j : ℕ) :
      (((0 : ℕ) : ℝ) + ((1 : ℕ) : ℝ)*(j : ℝ)+1) • g j =
        (if j % D = a then (j : ℝ)+1 else 0) - ((j : ℝ)+1)/(D : ℝ) := by
    by_cases hj : j % D = a <;> simp [g, hj, smul_eq_mul] <;> ring
  simp_rw [hterm] at h
  rw [Real.norm_eq_abs, sum_sub_distrib, ← sum_filter, ← sum_div] at h
  simpa using h


theorem residue_weight_Ico_discrepancy (A U D a : ℕ) (hAU : A ≤ U)
    (hD : 0 < D) (ha : a < D) :
    |(∑ n ∈ (Ico A U).filter (fun n => n % D = a), ((n : ℝ)+1)) -
      (∑ n ∈ Ico A U, ((n : ℝ)+1))/(D : ℝ)| ≤ 2*(A : ℝ)+2*(U : ℝ)+2 := by
  let F (j : ℕ) : ℝ := (∑ n ∈ (range j).filter (fun n => n % D = a), ((n : ℝ)+1)) -
    (∑ n ∈ range j, ((n : ℝ)+1))/(D : ℝ)
  have hex :
      (∑ n ∈ (Ico A U).filter (fun n => n % D = a), ((n : ℝ)+1)) -
        (∑ n ∈ Ico A U, ((n : ℝ)+1))/(D : ℝ) = F U - F A := by
    simp only [F, sum_filter, sum_Ico_eq_sub _ hAU]
    ring
  rw [hex]
  calc
    _ ≤ |F U|+|F A| := by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (F U) 0 (F A)
    _ ≤ (2*(U : ℝ)+1)+(2*(A : ℝ)+1) := by
      exact add_le_add (residue_weight_discrepancy U D a hD ha) (residue_weight_discrepancy A D a hD ha)
    _ = _ := by ring

end GoldbachEvenCancel

namespace GoldbachRawModel

open Finset GoldbachMajorArc GoldbachRawKernel

noncomputable section

def kernelScale : ℝ := 16*Real.pi+2

theorem kernelScale_pos : 0 < kernelScale := by
  unfold kernelScale
  positivity

def mass (n Q q : ℕ) : ℝ :=
  ((n:ℝ)+1)*profile ((Q:ℝ)/(q:ℝ))

def profiled (n Q : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 Q, coefficient q n * (mass n Q q : ℂ)

theorem model_profile_error (n Q : ℕ) (hn : 0 < n) (hQ : cutoff n = Q) :
    ‖modeledContribution n-profiled n Q‖ ≤ kernelScale*((Q:ℝ)+1)^3 := by
  rw [modeledContribution, hQ, profiled, ← sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ Icc 1 Q, ‖coefficient q n * (kernelMass n (width n q):ℂ) -
        coefficient q n * (mass n Q q:ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Icc 1 Q, kernelScale*((Q:ℝ)+1)^2 := by
      apply sum_le_sum
      intro q hq
      have hq' : 0 < q := (mem_Icc.mp hq).1
      rw [← mul_sub, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        width, hQ]
      have hk : |kernelMass n ((Q:ℝ)/((q:ℝ)*(n:ℝ)))-mass n Q q| ≤
          kernelScale*((Q:ℝ)+1)^2 := kernel_mass_error n q Q hn hq'
      calc
        _ ≤ 1*(kernelScale*((Q:ℝ)+1)^2) :=
          mul_le_mul (GoldbachEvenCancel.coefficient_norm q n hq') hk (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    _ = (Q:ℝ)*(kernelScale*((Q:ℝ)+1)^2) := by simp [Nat.card_Icc, nsmul_eq_mul]
    _ ≤ ((Q:ℝ)+1)*(kernelScale*((Q:ℝ)+1)^2) := by
      exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg kernelScale_pos.le (sq_nonneg _))
    _ = _ := by ring


end
end GoldbachRawModel

namespace GoldbachEvenProfile

open Finset GoldbachMajorArc GoldbachRawKernel
open scoped Pointwise

noncomputable section

theorem residue_divisibility (n r : ℕ) (hr5 : 5 ≤ r) (hr : r.Prime)
    (hn : n % (6 * r) = 2 * r) : 2 ∣ n ∧ ¬ 3 ∣ n ∧ r ∣ n := by
  have htwo : 2 ∣ 6 * r := dvd_mul_of_dvd_left (by decide) r
  have hthree : 3 ∣ 6 * r := dvd_mul_of_dvd_left (by decide) r
  have hrr : r ∣ 6 * r := dvd_mul_left r 6
  have h2 := (Nat.mod_mod_of_dvd n htwo).symm
  have h3 := (Nat.mod_mod_of_dvd n hthree).symm
  have hR := (Nat.mod_mod_of_dvd n hrr).symm
  rw [hn] at h2 h3 hR
  refine ⟨Nat.dvd_of_mod_eq_zero (h2.trans (Nat.mul_mod_right 2 r)), ?_,
    Nat.dvd_of_mod_eq_zero (hR.trans (Nat.mul_mod_left 2 r))⟩
  intro h
  have hh : 3 ∣ 2 * r := Nat.dvd_of_mod_eq_zero (h3.symm.trans (Nat.mod_eq_zero_of_dvd h))
  rcases Nat.prime_three.dvd_mul.mp hh with hbad | hbad
  · omega
  · have hc := (hr.eq_one_or_self_of_dvd 3 hbad).resolve_left (by decide)
    omega

private theorem restricted_divisors (Q r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hlo : 14 * r ≤ 5 * Q) (hhi : 5 * Q < 15 * r) :
    (Icc 1 Q).filter (fun q => q ∣ 6 * r) = {1, 2, 3, 6, r, 2 * r} := by
  have h6 : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide
  have hpos : 6 * r ≠ 0 := by positivity
  have hdiv : (6 * r).divisors = ({1, 2, 3, 6} : Finset ℕ) * {1, r} := by
    rw [Nat.divisors_mul, h6, hr.divisors]
  ext q
  simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
  constructor
  · rintro ⟨⟨hq1, hqQ⟩, hd⟩
    have hd' := Nat.mem_divisors.mpr ⟨hd, hpos⟩
    rw [hdiv] at hd'
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_mul.mp hd'
    rw [← hab] at hqQ ⊢
    simp only [mem_insert, mem_singleton] at ha hb
    rcases ha with ha | ha | ha | ha <;>
      rcases hb with hb | hb <;>
      simp only [ha, hb, Nat.mul_one, Nat.one_mul, true_or, or_true] at hqQ ⊢ <;> omega
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨⟨by omega, by omega⟩, one_dvd _⟩
    · exact ⟨⟨by omega, by omega⟩, dvd_mul_of_dvd_left (by decide) r⟩
    · exact ⟨⟨by omega, by omega⟩, dvd_mul_of_dvd_left (by decide) r⟩
    · exact ⟨⟨by omega, by omega⟩, dvd_mul_right 6 r⟩
    · exact ⟨⟨by omega, by omega⟩, dvd_mul_left _ 6⟩
    · exact ⟨⟨by omega, by omega⟩, mul_dvd_mul_right (by decide : 2 ∣ 6) r⟩

/-- The terms that survive the modulus cutoff in the progression of interest. -/
theorem restricted_profile_value (n Q r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hlo : 14 * r ≤ 5 * Q) (hhi : 5 * Q < 15 * r)
    (hn : n % (6 * r) = 2 * r) :
    (∑ q ∈ (Icc 1 Q).filter (fun q => q ∣ 6 * r),
      coefficient q n * (profile ((Q:ℝ)/(q:ℝ)):ℂ)).re =
      profile (Q:ℝ) + profile ((Q:ℝ)/2)
        - (profile ((Q:ℝ)/3) + profile ((Q:ℝ)/6))/4
        + (profile ((Q:ℝ)/(r:ℝ)) + profile ((Q:ℝ)/(2*(r:ℝ))))/((r:ℝ)-1) := by
  obtain ⟨hn2, hn3, hnr⟩ := residue_divisibility n r hr5 hr hn
  have hrc2 : Nat.Coprime 2 r :=
    (hr.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))).symm
  have hc2 : coefficient 2 n = 1 := by
    rw [coefficient_prime Nat.prime_two]
    norm_num [localCoefficient, hn2]
  have hc3 : coefficient 3 n = ((-(1/4):ℝ):ℂ) := by
    rw [coefficient_prime Nat.prime_three]
    norm_num [localCoefficient, hn3]
  have hc6 : coefficient 6 n = ((-(1/4):ℝ):ℂ) := by
    rw [show (6:ℕ) = 2*3 by decide,
      coefficient_mul (by decide) (by decide) (by decide : Nat.Coprime 2 3), hc2, hc3, one_mul]
  have hcr : coefficient r n = ((1/((r:ℝ)-1):ℝ):ℂ) := by
    rw [coefficient_prime hr, localCoefficient, ite_eq_left hnr]
  have hc2r : coefficient (2*r) n = ((1/((r:ℝ)-1):ℝ):ℂ) := by
    rw [coefficient_mul (by decide) hr.pos hrc2, hc2, hcr, one_mul]
  have hr6 : r ≠ 6 := by
    intro he
    subst r
    exact (by decide : ¬ Nat.Prime 6) hr
  have h1 : 1 ∉ ({2, 3, 6, r, 2*r} : Finset ℕ) := by simp only [mem_insert, mem_singleton]; omega
  have h2 : 2 ∉ ({3, 6, r, 2*r} : Finset ℕ) := by simp only [mem_insert, mem_singleton]; omega
  have h3 : 3 ∉ ({6, r, 2*r} : Finset ℕ) := by simp only [mem_insert, mem_singleton]; omega
  have h6 : 6 ∉ ({r, 2*r} : Finset ℕ) := by simp only [mem_insert, mem_singleton]; omega
  have hR : r ∉ ({2*r} : Finset ℕ) := by simp only [mem_singleton]; omega
  rw [restricted_divisors Q r hr hr5 hlo hhi, sum_insert h1, sum_insert h2, sum_insert h3,
    sum_insert h6, sum_insert hR, sum_singleton, coefficient_one, hc2, hc3, hc6, hcr, hc2r]
  simp only [one_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re,
    Nat.cast_one, Nat.cast_ofNat, Nat.cast_mul, div_one]
  ring

private theorem profile_term_lower (Q q : ℕ) (hQ : 0 < Q) (hq : 0 < q) :
    1 - 2*(q:ℝ)/(9*(Q:ℝ)) ≤ profile ((Q:ℝ)/(q:ℝ)) := by
  have hQ' : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hm := (Conjectures.Goldbach.FiniteMajorSincMass ((Q:ℝ)/(q:ℝ))
    (div_pos hQ' hq')).2.2
  change 1 - 2/(9*((Q:ℝ)/(q:ℝ))) ≤ profile ((Q:ℝ)/(q:ℝ)) at hm
  have he : 2/(9*((Q:ℝ)/(q:ℝ))) = 2*(q:ℝ)/(9*(Q:ℝ)) := by
    field_simp [hQ'.ne', hq'.ne']
  rwa [he] at hm

/-- Averaging on this progression leaves a positive gap over its full Euler factor. -/
theorem restricted_profile_floor (n Q r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hlo : 14 * r ≤ 5 * Q) (hhi : 5 * Q < 15 * r)
    (hn : n % (6 * r) = 2 * r) :
    3*(r:ℝ)/(2*((r:ℝ)-1)) + 1/(15*(Q:ℝ)) ≤
      (∑ q ∈ (Icc 1 Q).filter (fun q => q ∣ 6*r),
        coefficient q n * (profile ((Q:ℝ)/(q:ℝ)):ℂ)).re := by
  have hQ : 0 < Q := by omega
  have hQr : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hR1 : 0 < (r:ℝ)-1 := sub_pos.mpr (by exact_mod_cast (show 1 < r by omega))
  have hloR : 14*(r:ℝ) ≤ 5*(Q:ℝ) := by exact_mod_cast hlo
  have h1 := profile_term_lower Q 1 hQ (by decide)
  have h2 := profile_term_lower Q 2 hQ (by decide)
  have h3 := (profile_bounds ((Q:ℝ)/3) (by positivity)).2
  have h6 := (profile_bounds ((Q:ℝ)/6) (by positivity)).2
  have hR := profile_term_lower Q r hQ hr.pos
  have h2R := profile_term_lower Q (2*r) hQ (by positivity)
  norm_num [Nat.cast_mul] at h1 h2 h2R
  have hrr :
      (2-2*(r:ℝ)/(3*(Q:ℝ)))/((r:ℝ)-1) ≤
        (profile ((Q:ℝ)/(r:ℝ)) + profile ((Q:ℝ)/(2*(r:ℝ))))/((r:ℝ)-1) := by
    apply div_le_div_of_nonneg_right _ hR1.le
    have he : 2*(r:ℝ)/(3*(Q:ℝ)) =
        2*(r:ℝ)/(9*(Q:ℝ)) + 2*(2*(r:ℝ))/(9*(Q:ℝ)) := by ring
    rw [he]
    linarith only [hR,h2R]
  have h12 : 2 - 2/(3*(Q:ℝ)) ≤ profile (Q:ℝ) + profile ((Q:ℝ)/2) := by
    have he : 2/(3*(Q:ℝ)) = 2/(9*(Q:ℝ)) + 4/(9*(Q:ℝ)) := by ring
    rw [he]
    linarith only [h1,h2]
  rw [restricted_profile_value n Q r hr hr5 hlo hhi hn]
  have hbound :
      3/2 - 2/(3*(Q:ℝ)) + (2-2*(r:ℝ)/(3*(Q:ℝ)))/((r:ℝ)-1) ≤
        profile (Q:ℝ) + profile ((Q:ℝ)/2)
          - (profile ((Q:ℝ)/3) + profile ((Q:ℝ)/6))/4
          + (profile ((Q:ℝ)/(r:ℝ)) + profile ((Q:ℝ)/(2*(r:ℝ))))/((r:ℝ)-1) := by
    linarith only [h12,h3,h6,hrr]
  apply le_trans _ hbound
  apply le_of_sub_nonneg
  have hprod : 0 < 15*(Q:ℝ)*((r:ℝ)-1) := by positivity
  apply (mul_nonneg_iff_of_pos_right hprod).mp
  have he :
      (3/2 - 2/(3*(Q:ℝ)) + (2-2*(r:ℝ)/(3*(Q:ℝ)))/((r:ℝ)-1)
        - (3*(r:ℝ)/(2*((r:ℝ)-1)) + 1/(15*(Q:ℝ)))) * (15*(Q:ℝ)*((r:ℝ)-1)) =
      (15/2)*(Q:ℝ) - 21*(r:ℝ) + 11 := by
    field_simp [hQr.ne', hR1.ne']
    ring
  rw [he]
  linarith only [hloR]

end
end GoldbachEvenProfile

namespace GoldbachEvenPrefix

open Finset Filter GoldbachMajorArc
open scoped Topology

noncomputable section

-- The estimates for small and large initial segments follow the Apache-2.0
-- major-arc source of repository PR 316. We use its class error estimate for
-- arbitrary denominators bounded by sixteen log squared.

private theorem nat_log_two_le {u : ℕ} (hu : 1 ≤ u) :
    (Nat.log 2 u : ℝ) ≤ 2 * Real.log u := by
  have hL : 0 ≤ Real.log u := Real.log_nonneg (by exact_mod_cast hu)
  have h₂ := Real.log_two_gt_d9
  have h := Real.natLog_le_logb u 2
  simp only [Nat.cast_ofNat, Real.logb] at h
  refine h.trans ((div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr ?_)
  nlinarith only [mul_nonneg hL (show 0 ≤ 2 * Real.log 2 - 1 by linarith)]

private theorem class_error_trivial (u q b : ℕ) (hq : 0 < q) :
    |classError (u + 1) q b| ≤ (Real.log 4 + 1) * ((u : ℝ) + 1) := by
  have hw (k : ℕ) : 0 ≤ primeWeight k := by
    unfold primeWeight
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_le)
    · exact le_rfl
  have hmass : classMass (u + 1) q b ≤ Real.log 4 * u := by
    unfold classMass
    calc
      _ ≤ ∑ k ∈ range (u + 1), primeWeight k :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k _ _ => hw k)
      _ = Chebyshev.theta u := by
        rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range, sum_filter]; rfl
      _ ≤ _ := Chebyshev.theta_le_log4_mul_x (by positivity)
  have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hfrac : ((u + 1 : ℕ) : ℝ) / q.totient ≤ (u : ℝ) + 1 := by
    push_cast
    exact div_le_self (by positivity) hφ
  push_cast at hfrac
  have hm : 0 ≤ classMass (u + 1) q b := sum_nonneg (fun k _ => hw k)
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold classError
  split_ifs
  · apply abs_le.mpr
    constructor <;> push_cast <;> nlinarith [show 0 ≤ ((u : ℝ) + 1) / q.totient by positivity,
      mul_nonneg hlog (Nat.cast_nonneg (α := ℝ) u)]
  · rw [sub_zero, abs_of_nonneg hm]
    linarith [Nat.cast_nonneg (α := ℝ) u]

private theorem uniform_class_envelope :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ n : ℕ in atTop, ∀ m q b : ℕ,
      m ≤ n+1 → 0 < q → (q:ℝ) ≤ 16 * (Real.log n)^2 → b < q →
      |classError m q b| ≤ errorEnvelope M n := by
  obtain ⟨M, hM, x₀, hx₀, hAP⟩ := all_class_error 16 4 (by norm_num) (by norm_num)
  refine ⟨M, hM, ?_⟩
  have hlim := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hroot := Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually_ge_atTop 16, hroot.eventually_ge_atTop x₀] with n hL hrootN
  change (16 : ℝ) ≤ Real.log n at hL
  change x₀ ≤ Real.sqrt n at hrootN
  intro m q b hm hq hQ' hb
  have hnL : 0 < Real.log n := by linarith
  have hconst : 0 < Real.log 4 + 1 := by positivity
  have henv : 0 ≤ errorEnvelope M n := by unfold errorEnvelope; positivity
  cases m with
  | zero => simpa [classError, classMass] using henv
  | succ u =>
    have hun : u ≤ n := by omega
    have hun' : (u : ℝ) ≤ n := by exact_mod_cast hun
    by_cases hs : (u : ℝ) < Real.sqrt n
    · refine (class_error_trivial u q b hq).trans ?_
      have hsmall := mul_le_mul_of_nonneg_left (add_le_add hs.le (le_refl (1 : ℝ))) hconst.le
      unfold errorEnvelope
      linarith [show 0 ≤ M * 2 ^ 16 * n / (Real.log n) ^ 16 by positivity,
        show 0 ≤ 32 * (Real.log n) ^ 3 by positivity, show 0 ≤ 2 * Real.sqrt n * Real.log n by positivity]
    · have hsu := le_of_not_gt hs
      have hux : x₀ ≤ (u : ℝ) := hrootN.trans hsu
      have hu1 : (1 : ℝ) < u := hx₀.trans_le hux
      have huL := Real.log_pos hu1
      have hhalf := Real.log_le_log (by linarith : 0 < Real.sqrt n) hsu
      rw [Real.log_sqrt (Nat.cast_nonneg n)] at hhalf
      have hupper := Real.log_le_log (by linarith : 0 < (u : ℝ)) hun'
      have hu8 : 8 ≤ Real.log u := by linarith
      have hl2 := pow_le_pow_left₀ hnL.le (show Real.log n ≤ 2 * Real.log u by linarith) 2
      have h4 : (q : ℝ) ≤ (Real.log u) ^ (4 : ℕ) := by
        nlinarith only [hQ', hl2, mul_nonneg (sq_nonneg (Real.log u))
          (show 0 ≤ (Real.log u) ^ 2 - 64 by nlinarith)]
      have hraw := hAP u q b hux hq (by simpa using h4) hb
      have hrpow : (Real.log u) ^ (-(16 : ℝ)) = 1 / (Real.log u) ^ (16 : ℕ) := by
        rw [Real.rpow_neg huL.le]; norm_num [one_div]
      rw [hrpow, ← div_eq_mul_one_div] at hraw
      have hpow := pow_le_pow_left₀ hnL.le (show Real.log n ≤ 2 * Real.log u by linarith) 16
      rw [mul_pow] at hpow
      have hmain : M * (u : ℝ) / (Real.log u) ^ 16 ≤ M * 2 ^ 16 * n / (Real.log n) ^ 16 := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        calc
          _ ≤ (M * n) * (2 ^ 16 * (Real.log u) ^ 16) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hun' hM.le) hpow (by positivity) (by positivity)
          _ = _ := by ring
      have hNat := (nat_log_two_le (u := u) (by exact_mod_cast hu1.le)).trans
        (mul_le_mul_of_nonneg_left hupper (by norm_num : (0 : ℝ) ≤ 2))
      have hlogq : Real.log q ≤ 16 * (Real.log n) ^ 2 :=
        (Real.log_le_self (Nat.cast_nonneg q)).trans hQ'
      have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
      have herr := mul_le_mul hNat hlogq hlogq0 (by positivity)
      have hsqrt := mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hun') (by norm_num : (0 : ℝ) ≤ 2))
        hupper huL.le (by positivity)
      unfold errorEnvelope
      nlinarith only [hraw, hmain, herr, hsqrt,
        mul_nonneg hconst.le (show 0 ≤ Real.sqrt n + 1 by positivity)]

/-- The bound is uniform in the initial segment length and all denominators through
three times the squared dyadic level. -/
theorem uniform_dyadic_class_error :
    ∀ᶠ k : ℕ in atTop, ∀ u d a : ℕ,
      u ≤ 2 * (2^k : ℕ) → 0 < d → d ≤ 3*k^2 → a < d →
      |classError u d a| ≤ ((2^k : ℕ) : ℝ)/(k:ℝ)^10 := by
  obtain ⟨M, hM, hprefix⟩ := uniform_class_envelope
  have hpow : Tendsto (fun k : ℕ => (2:ℕ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  have hn_lim : Tendsto (fun k : ℕ => 2*(2:ℕ)^k) atTop atTop :=
    tendsto_atTop_mono (fun k => by omega) hpow
  have hsmall := (envelope_saving M).eventually_le_const (by norm_num : (0:ℝ) < 1/2048)
  filter_upwards [eventually_ge_atTop (1:ℕ), hn_lim.eventually hprefix,
    hn_lim.eventually hsmall] with k hk hp hs
  let n : ℕ := 2*(2:ℕ)^k
  have hn : 0 < (n:ℝ) := by dsimp [n]; positivity
  have hkR : 0 < (k:ℝ) := by exact_mod_cast hk
  change (Real.log n)^10 * errorEnvelope M n / (n:ℝ) ≤ 1/2048 at hs
  have hLog : Real.log n = ((k:ℝ)+1)*Real.log 2 := by
    dsimp [n]
    push_cast
    rw [Real.log_mul two_ne_zero (pow_ne_zero _ two_ne_zero), Real.log_pow]
    ring
  have hkL : (k:ℝ) ≤ 2*Real.log n := by
    rw [hLog]
    have hlog2 : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith only [mul_nonneg hkR.le (show 0 ≤ 2*Real.log 2-1 by linarith), hlog2]
  have hL : 0 < Real.log n := by linarith
  have hm0 : 0 ≤ errorEnvelope M n := by unfold errorEnvelope; positivity
  have hBudget : errorEnvelope M n ≤ ((2^k : ℕ) : ℝ)/(k:ℝ)^10 := by
    apply (le_div_iff₀ (pow_pos hkR 10)).2
    have h := (div_le_iff₀ hn).mp hs
    calc
      _ = (k:ℝ)^10 * errorEnvelope M n := by ring
      _ ≤ (2*Real.log n)^10 * errorEnvelope M n :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hkR.le hkL 10) hm0
      _ = (1024:ℝ)*((Real.log n)^10*errorEnvelope M n) := by rw [mul_pow]; ring
      _ ≤ (1024:ℝ)*((1/2048:ℝ)*(n:ℝ)) := mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by dsimp [n]; push_cast; ring
  intro u d a hu hd hdk ha
  have hq : (d:ℝ) ≤ 16*(Real.log n)^2 := by
    have hdkR : (d:ℝ) ≤ 3*(k:ℝ)^2 := by exact_mod_cast hdk
    have hsq := pow_le_pow_left₀ hkR.le hkL 2
    nlinarith only [hdkR, hsq, sq_nonneg (Real.log n)]
  exact (hp u d a (by change u ≤ n at hu; omega) hd hq ha).trans hBudget

/-- Density of the logarithmic prime weight in a single residue class. -/
def density (d a : ℕ) : ℝ := (if a.Coprime d then 1 else 0)/(d.totient:ℝ)

theorem classError_eq (u d a : ℕ) :
    classError u d a = classMass u d a - (u:ℝ)*density d a := by
  unfold classError density
  split_ifs <;> ring

theorem uniform_dyadic_class_mass :
    ∀ᶠ k : ℕ in atTop, ∀ u d a : ℕ,
      u ≤ 2 * (2^k : ℕ) → 0 < d → d ≤ 3*k^2 → a < d →
      |classMass u d a - (u:ℝ)*density d a| ≤ ((2^k : ℕ) : ℝ)/(k:ℝ)^10 := by
  filter_upwards [uniform_dyadic_class_error] with k h
  simpa only [classError_eq] using h

end
end GoldbachEvenPrefix

namespace GoldbachEvenTriangle

open Finset
open scoped BigOperators

noncomputable def classPrefix (m d b : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ k ∈ (range m).filter (fun k => k % d = b), w k

noncomputable def convolution (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (n+1), w i * w (n-i)

noncomputable def triangle (U d a : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ (range U).filter (fun n => n % d = a), convolution w n

def partnerResidue (d a i : ℕ) : ℕ := (a+d-(i % d)) % d

theorem partnerResidue_lt (d a i : ℕ) (hd : 0 < d) : partnerResidue d a i < d :=
  Nat.mod_lt _ hd

private theorem add_mod_eq_iff_partner (d a i j : ℕ) (hd : 0 < d) (ha : a < d) :
    (i+j) % d = a ↔ j % d = partnerResidue d a i := by
  have hsub : i % d ≤ a+d := by have := Nat.mod_lt i hd; omega
  have hc : (partnerResidue d a i : ZMod d) = (a : ZMod d) - (i : ZMod d) := by
    unfold partnerResidue
    rw [ZMod.natCast_mod, Nat.cast_sub hsub, Nat.cast_add, ZMod.natCast_self, add_zero,
      ZMod.natCast_mod]
  calc
    _ ↔ ((i+j:ℕ):ZMod d) = (a : ZMod d) := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha]
    _ ↔ (j : ZMod d) = (partnerResidue d a i : ZMod d) := by
      rw [Nat.cast_add, hc]
      exact eq_sub_iff_add_eq'.symm
    _ ↔ _ := by
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (partnerResidue_lt d a i hd)]

/-- Exchange the indexing of the finite triangle `i+j<U`. -/
private theorem sum_triangle_exchange {M : Type*} [AddCommMonoid M]
    (U : ℕ) (f : ℕ → ℕ → M) :
    (∑ n ∈ range U, ∑ i ∈ range (n+1), f i (n-i)) =
      ∑ i ∈ range U, ∑ j ∈ range (U-i), f i j := by
  rw [sum_sigma', sum_sigma']
  refine sum_bij' (fun (p : Σ _ : ℕ, ℕ) _ => ⟨p.2,p.1-p.2⟩)
    (fun (p : Σ _ : ℕ, ℕ) _ => ⟨p.1+p.2,p.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n,i⟩ hi
    simp only [mem_sigma,mem_range] at hi ⊢
    exact ⟨by omega,by omega⟩
  · rintro ⟨i,j⟩ hj
    simp only [mem_sigma,mem_range] at hj ⊢
    exact ⟨by omega,by omega⟩
  · rintro ⟨n,i⟩ hi
    simp only [mem_sigma,mem_range] at hi
    have hle : i ≤ n := by omega
    simp only [Nat.add_sub_of_le hle]
  · rintro ⟨i,j⟩ _
    simp only [Nat.add_sub_cancel_left]
  · intro _ _
    rfl

/-- The weighted difference coefficient is a single convolution of initial segment
sums after exchanging positions in the triangle. -/
theorem triangle_eq_prefix (U d a : ℕ) (hd : 0 < d) (ha : a < d) (w : ℕ → ℝ) :
    triangle U d a w = ∑ i ∈ range U, w i * classPrefix (U-i) d (partnerResidue d a i) w := by
  classical
  calc
    _ = ∑ n ∈ range U, ∑ i ∈ range (n+1),
        if (i+(n-i)) % d = a then w i*w (n-i) else 0 := by
      rw [triangle, sum_filter]
      apply sum_congr rfl
      intro n _
      unfold convolution
      by_cases hn : n % d = a
      · rw [ite_eq_left hn]
        apply sum_congr rfl
        intro i hi
        have hin : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
        rw [Nat.add_sub_of_le hin, ite_eq_left hn]
      · rw [ite_eq_right hn]
        symm
        apply sum_eq_zero
        intro i hi
        have hin : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
        rw [Nat.add_sub_of_le hin, ite_eq_right hn]
    _ = ∑ i ∈ range U, ∑ j ∈ range (U-i),
        if (i+j) % d = a then w i*w j else 0 :=
      sum_triangle_exchange U (fun i j => if (i+j) % d = a then w i*w j else 0)
    _ = _ := by
      apply sum_congr rfl
      intro i _
      simp only [add_mod_eq_iff_partner d a i _ hd ha]
      rw [← sum_filter, classPrefix, mul_sum]

private theorem weighted_prefix_residues (m d a : ℕ) (hd : 0 < d) (w μ : ℕ → ℝ) :
    (∑ i ∈ range m, w i * μ (partnerResidue d a i)) =
      ∑ b ∈ range d, classPrefix m d b w * μ ((a+d-b) % d) := by
  let g (i : ℕ) := w i * μ (partnerResidue d a i)
  have hmaps : (range m : Set ℕ).MapsTo (fun i => i % d) (range d : Set ℕ) :=
    fun i _ => mem_range.mpr (Nat.mod_lt i hd)
  change (∑ i ∈ range m, g i) = _
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro b _
  rw [classPrefix, sum_mul]
  apply sum_congr rfl
  intro i hi
  simp only [g, partnerResidue, (mem_filter.mp hi).2]

/-- After replacing the inner initial segment by its linear model, exchange
the remaining triangular length and regroup by the first residue. -/
theorem linearized_prefix_eq (U d a : ℕ) (hd : 0 < d) (w μ : ℕ → ℝ) :
    (∑ i ∈ range U, w i * (((U-i:ℕ):ℝ)* μ (partnerResidue d a i))) =
      ∑ t ∈ range U, ∑ b ∈ range d, classPrefix (t+1) d b w * μ ((a+d-b) % d) := by
  calc
    _ = ∑ i ∈ range U, ∑ _j ∈ range (U-i), w i * μ (partnerResidue d a i) := by
      apply sum_congr rfl
      intro i _
      rw [sum_const,nsmul_eq_mul,card_range]
      ring
    _ = ∑ t ∈ range U, ∑ i ∈ range (t+1), w i * μ (partnerResidue d a i) :=
      (sum_triangle_exchange U (fun i _j => w i * μ (partnerResidue d a i))).symm
    _ = _ := sum_congr rfl (fun t _ => weighted_prefix_residues (t+1) d a hd w μ)

/-- Two uniform initial segment approximations give a quantitative estimate for
the weighted convolution on a residue class inside a finite triangle. -/
theorem triangle_prefix_approx (U d a : ℕ) (hd : 0 < d) (ha : a < d) (w μ : ℕ → ℝ)
    (W E : ℝ) (hE : 0 ≤ E) (hw : ∀ i < U, |w i| ≤ W) (hμ : ∀ b < d, |μ b| ≤ 1)
    (hprefix : ∀ m ≤ U, ∀ b < d, |classPrefix m d b w - (m:ℝ)*μ b| ≤ E) :
    |triangle U d a w - (∑ t ∈ range U, ((t:ℝ)+1)) *
      (∑ b ∈ range d, μ b*μ ((a+d-b) % d))| ≤ (U:ℝ)*(W+(d:ℝ))*E := by
  let linear := ∑ i ∈ range U, w i * (((U-i:ℕ):ℝ)* μ (partnerResidue d a i))
  let main := (∑ t ∈ range U, ((t:ℝ)+1)) * (∑ b ∈ range d, μ b*μ ((a+d-b) % d))
  have hfirst : |triangle U d a w - linear| ≤ (U:ℝ)*(W*E) := by
    unfold linear
    rw [triangle_eq_prefix U d a hd ha w, ← sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ range U, |w i * classPrefix (U-i) d (partnerResidue d a i) w -
        w i * (((U-i:ℕ):ℝ)*μ (partnerResidue d a i))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ range U, W*E := by
        apply sum_le_sum
        intro i hi
        rw [← mul_sub, abs_mul]
        exact (mul_le_mul_of_nonneg_left (hprefix _ (Nat.sub_le _ _) _
          (partnerResidue_lt d a i hd)) (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_right (hw i (mem_range.mp hi)) hE)
      _ = _ := by simp
  have hlinear : linear - main = ∑ t ∈ range U, ∑ b ∈ range d,
      (classPrefix (t+1) d b w - ((t:ℝ)+1)* μ b) * μ ((a+d-b) % d) := by
    unfold linear main
    rw [linearized_prefix_eq U d a hd w μ, sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro t _
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro b _
    ring
  have hsecond : |linear-main| ≤ (U:ℝ)*((d:ℝ)*E) := by
    rw [hlinear]
    calc
      _ ≤ ∑ t ∈ range U, |∑ b ∈ range d,
          (classPrefix (t+1) d b w - ((t:ℝ)+1)* μ b) * μ ((a+d-b) % d)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ range U, ∑ _b ∈ range d, E := by
        apply sum_le_sum
        intro t ht
        refine (abs_sum_le_sum_abs _ _).trans ?_
        apply sum_le_sum
        intro b hb
        rw [abs_mul]
        have h := hprefix (t+1) (Nat.succ_le_of_lt (mem_range.mp ht)) b (mem_range.mp hb)
        rw [Nat.cast_add, Nat.cast_one] at h
        simpa only [mul_one] using
          mul_le_mul h (hμ _ (Nat.mod_lt _ hd)) (abs_nonneg _) hE
      _ = _ := by simp
  change |triangle U d a w - main| ≤ _
  calc
    _ = |(triangle U d a w-linear)+(linear-main)| := by congr 1; ring
    _ ≤ |triangle U d a w-linear| + |linear-main| := abs_add_le _ _
    _ ≤ (U:ℝ)*(W*E)+(U:ℝ)*((d:ℝ)*E) := add_le_add hfirst hsecond
    _ = _ := by ring

/-- Subtract the two initial segment triangles to estimate a half-open interval. -/
theorem interval_prefix_approx (L U d a : ℕ) (hLU : L ≤ U) (hd : 0 < d) (ha : a < d)
    (w μ : ℕ → ℝ) (W E : ℝ) (hE : 0 ≤ E)
    (hw : ∀ i < U, |w i| ≤ W) (hμ : ∀ b < d, |μ b| ≤ 1)
    (hprefix : ∀ m ≤ U, ∀ b < d, |classPrefix m d b w - (m:ℝ)*μ b| ≤ E) :
    |(∑ n ∈ (Ico L U).filter (fun n => n % d = a), convolution w n) -
      (∑ t ∈ Ico L U, ((t:ℝ)+1)) * (∑ b ∈ range d, μ b*μ ((a+d-b) % d))| ≤
      ((L:ℝ)+(U:ℝ))*(W+(d:ℝ))*E := by
  let C := ∑ b ∈ range d, μ b*μ ((a+d-b) % d)
  let P (u : ℕ) := (∑ t ∈ range u, ((t:ℝ)+1))*C
  have hu : |triangle U d a w - P U| ≤ (U:ℝ)*(W+(d:ℝ))*E :=
    triangle_prefix_approx U d a hd ha w μ W E hE hw hμ hprefix
  have hl : |triangle L d a w - P L| ≤ (L:ℝ)*(W+(d:ℝ))*E :=
    triangle_prefix_approx L d a hd ha w μ W E hE
      (fun i hi => hw i (hi.trans_le hLU)) hμ
      (fun m hm => hprefix m (hm.trans hLU))
  have hwindow :
      (∑ n ∈ (Ico L U).filter (fun n => n % d = a), convolution w n) =
        triangle U d a w - triangle L d a w := by
    simpa only [triangle, ← sum_filter] using
      sum_Ico_eq_sub (fun n => if n % d = a then convolution w n else 0) hLU
  have hmain :
      (∑ t ∈ Ico L U, ((t:ℝ)+1))*C = P U-P L := by
    rw [sum_Ico_eq_sub _ hLU, sub_mul]
  change |(∑ n ∈ (Ico L U).filter (fun n => n % d = a), convolution w n) -
    (∑ t ∈ Ico L U, ((t:ℝ)+1))*C| ≤ _
  rw [hwindow,hmain]
  calc
    _ = |(triangle U d a w - P U) - (triangle L d a w - P L)| := by
      congr 1
      ring
    _ ≤ |triangle U d a w - P U| + |triangle L d a w - P L| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (triangle U d a w - P U) (-(triangle L d a w - P L))
    _ ≤ (U:ℝ)*(W+(d:ℝ))*E+(L:ℝ)*(W+(d:ℝ))*E := add_le_add hu hl
    _ = _ := by ring

end GoldbachEvenTriangle

namespace GoldbachEvenResidues

open Finset

/-- Mean prime weight in a residue class modulo `d`. -/
noncomputable def density (d i : ℕ) : ℝ :=
  if i.Coprime d then (d.totient : ℝ)⁻¹ else 0

theorem density_eq_div (d i : ℕ) :
    density d i = (if i.Coprime d then 1 else 0) / (d.totient : ℝ) := by
  unfold density
  by_cases h : i.Coprime d
  · simp only [ite_eq_left h, one_div]
  · simp only [ite_eq_right h, zero_div]

theorem density_nonneg (d i : ℕ) : 0 ≤ density d i := by
  unfold density
  split <;> positivity

theorem density_le_one (d i : ℕ) (hd : 0 < d) : density d i ≤ 1 := by
  unfold density
  split
  · have hφ : 0 < d.totient := Nat.totient_pos.mpr hd
    exact (inv_le_one₀ (by exact_mod_cast hφ)).mpr
      (by exact_mod_cast Nat.succ_le_of_lt hφ)
  · norm_num

private theorem coprime_six_iff (n : ℕ) :
    n.Coprime 6 ↔ n % 6 = 1 ∨ n % 6 = 5 := by
  have hm : n % 6 < 6 := Nat.mod_lt _ (by decide)
  change n.gcd 6 = 1 ↔ _
  rw [Nat.gcd_comm n 6, Nat.gcd_rec 6 n]
  interval_cases n % 6 <;> decide

private theorem prime_coprime_six {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    r.Coprime 6 := by
  apply hr.coprime_iff_not_dvd.mpr
  intro h
  have h' : r ∣ 2 * 3 := h
  rcases hr.dvd_mul.mp h' with h' | h'
  · have := Nat.le_of_dvd (by decide : 0 < 2) h'
    omega
  · have := Nat.le_of_dvd (by decide : 0 < 3) h'
    omega

private theorem coprime_pair_six {i j r : ℕ} (hr : r.Coprime 6)
    (h : i + j ≡ 2 * r [MOD 6]) :
    i.Coprime 6 ∧ j.Coprime 6 ↔ i % 6 = r % 6 := by
  have hr' := (coprime_six_iff r).mp hr
  have hi := Nat.mod_lt i (by decide : 0 < 6)
  have hj := Nat.mod_lt j (by decide : 0 < 6)
  change (i + j) % 6 = (2 * r) % 6 at h
  rw [Nat.add_mod, Nat.mul_mod 2 r 6] at h
  rw [coprime_six_iff i, coprime_six_iff j]
  omega

private theorem complementary_pair {r i : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    (hi : i < 6 * r) :
    i.Coprime (6 * r) ∧ ((2 * r + 6 * r - i) % (6 * r)).Coprime (6 * r) ↔
      i % 6 = r % 6 ∧ ¬ r ∣ i := by
  let j := (2 * r + 6 * r - i) % (6 * r)
  change i.Coprime (6 * r) ∧ j.Coprime (6 * r) ↔ _
  have hd6 : 6 ∣ 6 * r := dvd_mul_right 6 r
  have hdr : r ∣ 6 * r := dvd_mul_left r 6
  have hsum : i + j ≡ 2 * r [MOD 6 * r] := by
    change (i + j) % (6 * r) = (2 * r) % (6 * r)
    rw [show (i + j) % (6 * r) = (i + (2 * r + 6 * r - i)) % (6 * r) from
      Nat.add_mod_mod _ _ _]
    rw [show i + (2 * r + 6 * r - i) = 2 * r + 6 * r by omega]
    exact Nat.add_mod_right _ _
  have hsumr : r ∣ i + j := (hsum.dvd_iff hdr).mpr (dvd_mul_left r 2)
  have hrpair (t : ℕ) : t.Coprime r ↔ ¬ r ∣ t :=
    Nat.coprime_comm.trans hr.coprime_iff_not_dvd
  have h6 := coprime_pair_six (prime_coprime_six hr h5) (hsum.of_dvd hd6)
  simp only [Nat.coprime_mul_iff_right, hrpair]
  constructor
  · rintro ⟨⟨hi6, hir⟩, ⟨hj6, _⟩⟩
    exact ⟨h6.mp ⟨hi6, hj6⟩, hir⟩
  · rintro ⟨hm, hir⟩
    obtain ⟨hi6, hj6⟩ := h6.mpr hm
    exact ⟨⟨hi6, hir⟩, ⟨hj6, fun hjr => hir ((Nat.dvd_add_iff_left hjr).mpr hsumr)⟩⟩

private def candidates (r : ℕ) : Finset ℕ :=
  (range (6 * r)).filter (fun i => i % 6 = r % 6)

private theorem candidates_card (r : ℕ) : (candidates r).card = r := by
  let f : ℕ ↪ ℕ := ⟨fun j => 6 * j + r % 6, fun i j h => by
    change 6 * i + r % 6 = 6 * j + r % 6 at h
    omega⟩
  have hclass : candidates r = (range r).map f := by
    ext i
    simp only [candidates, mem_filter, mem_range, mem_map]
    constructor
    · rintro ⟨hi, hm⟩
      refine ⟨i / 6, by omega, ?_⟩
      change 6 * (i / 6) + r % 6 = i
      have hh := Nat.mod_add_div i 6
      omega
    · rintro ⟨j, hj, rfl⟩
      change 6 * j + r % 6 < 6 * r ∧ (6 * j + r % 6) % 6 = r % 6
      omega
  rw [hclass, card_map, card_range]

private theorem divisible_candidate {r i : ℕ} (hr : r.Prime) (h5 : 5 ≤ r)
    (hi : i ∈ candidates r) (hd : r ∣ i) : i = r := by
  obtain ⟨j, rfl⟩ := hd
  obtain ⟨hi, hh⟩ := mem_filter.mp hi
  have hj : j < 6 := (Nat.mul_lt_mul_left hr.pos).mp
    (by simpa only [Nat.mul_comm 6 r] using mem_range.mp hi)
  have hm : r * j ≡ r * 1 [MOD 6] := by
    simpa only [Nat.ModEq, Nat.mul_one] using hh
  have hcancel : j ≡ 1 [MOD 6] :=
    Nat.ModEq.cancel_left_of_coprime (prime_coprime_six hr h5).symm hm
  have he : j = 1 := by
    change j % 6 = 1 % 6 at hcancel
    rw [Nat.mod_eq_of_lt hj] at hcancel
    exact hcancel
  simp [he]

private theorem pair_card {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    ((range (6 * r)).filter (fun i =>
      i.Coprime (6 * r) ∧ ((2 * r + 6 * r - i) % (6 * r)).Coprime (6 * r))).card =
      r - 1 := by
  have hclass : (range (6 * r)).filter (fun i =>
      i.Coprime (6 * r) ∧ ((2 * r + 6 * r - i) % (6 * r)).Coprime (6 * r)) =
      (candidates r).erase r := by
    ext i
    constructor
    · intro hi
      obtain ⟨hir, hi⟩ := mem_filter.mp hi
      obtain ⟨hmod, hnd⟩ := (complementary_pair hr h5 (mem_range.mp hir)).mp hi
      exact mem_erase.mpr ⟨fun h => hnd (h ▸ dvd_refl r), mem_filter.mpr ⟨hir, hmod⟩⟩
    · intro hi
      obtain ⟨hne, hclass⟩ := mem_erase.mp hi
      obtain ⟨hir, hmod⟩ := mem_filter.mp hclass
      exact mem_filter.mpr ⟨hir, (complementary_pair hr h5 (mem_range.mp hir)).mpr
        ⟨hmod, fun hd => hne (divisible_candidate hr h5 hclass hd)⟩⟩
  have hmem : r ∈ candidates r := mem_filter.mpr
    ⟨mem_range.mpr (by omega), rfl⟩
  rw [hclass, card_erase_of_mem hmem, candidates_card]

/-- The convolution of the residue densities at the target class `2r mod 6r`. -/
theorem pair_mass (r : ℕ) (hr : r.Prime) (h5 : 5 ≤ r) :
    ((6 * r : ℕ) : ℝ) * (∑ i ∈ range (6 * r),
      density (6 * r) i * density (6 * r) ((2 * r + 6 * r - i) % (6 * r))) =
      3 * (r : ℝ) / (2 * ((r : ℝ) - 1)) := by
  have hs : (∑ i ∈ range (6 * r),
      density (6 * r) i * density (6 * r) ((2 * r + 6 * r - i) % (6 * r))) =
      ∑ i ∈ range (6 * r), if i.Coprime (6 * r) ∧
        ((2 * r + 6 * r - i) % (6 * r)).Coprime (6 * r)
        then (((6 * r).totient : ℝ)⁻¹)^2 else 0 := by
    apply sum_congr rfl
    intro i _
    unfold density
    by_cases h₁ : i.Coprime (6 * r)
    · by_cases h₂ : ((2 * r + 6 * r - i) % (6 * r)).Coprime (6 * r)
      · rw [ite_eq_left h₁, ite_eq_left h₂, ite_eq_left (And.intro h₁ h₂), pow_two]
      · have h : ¬ (i.Coprime (6 * r) ∧
            ((2 * r + 6 * r - i) % (6 * r)).Coprime (6 * r)) := fun h => h₂ h.2
        rw [ite_eq_right h₂, ite_eq_right h, mul_zero]
    · have h : ¬ (i.Coprime (6 * r) ∧
          ((2 * r + 6 * r - i) % (6 * r)).Coprime (6 * r)) := fun h => h₁ h.1
      rw [ite_eq_right h₁, ite_eq_right h, zero_mul]
  have hφ : Nat.totient 6 = 2 := by decide
  have hr1 : (1 : ℝ) < r := by exact_mod_cast (show 1 < r by omega)
  rw [hs, ← sum_filter, sum_const, nsmul_eq_mul, pair_card hr h5,
    Nat.totient_mul (prime_coprime_six hr h5).symm, hφ, Nat.totient_prime hr]
  push_cast [Nat.cast_sub (by omega : 1 ≤ r)]
  field_simp
  ring

end GoldbachEvenResidues

namespace GoldbachEvenWindows

open Finset Filter
open scoped Topology

private theorem exists_prime_range (K : ℕ) :
    ∃ k r : ℕ, K ≤ k ∧ r.Prime ∧ 5 ≤ r ∧ 14 * r ≤ 5 * k ^ 2 ∧ 5 * k ^ 2 < 15 * r := by
  obtain ⟨r, hr, hprime⟩ := Nat.exists_infinite_primes (max 1201 (K ^ 2))
  have hrLarge : 1201 ≤ r := (le_max_left _ _).trans hr
  have hrK : K ^ 2 ≤ r := (le_max_right _ _).trans hr
  let u := 14 * r / 5
  let s := Nat.sqrt u
  let k := s + 1
  have hsu : s ^ 2 ≤ u := Nat.sqrt_le' u
  have huk : u < k ^ 2 := Nat.lt_succ_sqrt' u
  have hLo : 14 * r ≤ 5 * k ^ 2 := by dsimp only [u] at huk; omega
  have hsR : 5 * s ^ 2 ≤ 14 * r := by dsimp only [u] at hsu; omega
  have hsR' : s ^ 2 ≤ 3 * r := by omega
  have hsize : 20 * s ≤ r := by
    by_contra h
    have hh : r < 20 * s := by omega
    have hsq := Nat.mul_self_lt_mul_self hh
    have hrSq := Nat.mul_lt_mul_of_pos_right (show 1200 < r by omega) hprime.pos
    nlinarith only [hsR', hsq, hrSq]
  have hdiff : 10 * s + 5 < r := by omega
  have hHi : 5 * k ^ 2 < 15 * r := by
    calc
      _ = 5 * s ^ 2 + 10 * s + 5 := by dsimp only [k]; ring
      _ < _ := by omega
  have hKsq : K ^ 2 ≤ k ^ 2 := by omega
  have hk : K ≤ k := (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp hKsq
  exact ⟨k, r, hk, hprime, by omega, hLo, hHi⟩

private theorem eventually_dyadic_large : ∀ᶠ k : ℕ in atTop, 12 * k ^ 2 ≤ 2 ^ k := by
  have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 2
    (by norm_num : (1 : ℝ) < 2)).bound (show (0 : ℝ) < 1 / 12 by norm_num)
  filter_upwards [h] with k hk
  change ‖(k : ℝ) ^ 2‖ ≤ (1 / 12 : ℝ) * ‖(2 : ℝ) ^ k‖ at hk
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hk
  exact_mod_cast (show 12 * (k : ℝ) ^ 2 ≤ (2 : ℝ) ^ k by linarith only [hk])

/-- A prime lies in the designated portion of the exact dyadic cutoff at arbitrarily large levels. -/
theorem exists_prime_level (K : ℕ) :
    ∃ k r : ℕ, K ≤ k ∧ r.Prime ∧ 5 ≤ r ∧ 14 * r ≤ 5 * k ^ 2 ∧
      5 * k ^ 2 < 15 * r ∧ 4 * (6 * r) ≤ 2 ^ k := by
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp eventually_dyadic_large
  obtain ⟨k, r, hk, hprime, hr, hlo, hhi⟩ := exists_prime_range (max K K₀)
  have hk₀ := (le_max_right K K₀).trans hk
  have hQ := hK₀ k hk₀
  exact ⟨k, r, (le_max_left K K₀).trans hk, hprime, hr, hlo, hhi, by omega⟩

/-- The exact progression of even targets inside the single-cutoff dyadic window. -/
def window (X r : ℕ) : Finset ℕ :=
  (Icc X (2 * X - 3)).filter (fun n => n % (6 * r) = 2 * r)

theorem mem_window {X r n : ℕ} :
    n ∈ window X r ↔ X ≤ n ∧ n ≤ 2 * X - 3 ∧ n % (6 * r) = 2 * r := by
  simp only [window, mem_filter, mem_Icc, and_assoc]

theorem window_even {X r n : ℕ} (hn : n ∈ window X r) : Even n := by
  have heq := Nat.mod_add_div n (6 * r)
  rw [(mem_window.mp hn).2.2] at heq
  refine ⟨r + 3 * r * (n / (6 * r)), ?_⟩
  calc
    n = 2 * r + 6 * r * (n / (6 * r)) := heq.symm
    _ = _ := by ring

private def first (X D a : ℕ) : ℕ :=
  a + D * (X / D + if a < X % D then 1 else 0)

private theorem first_properties (X D a : ℕ) (hD : 0 < D) (ha : a < D) :
    X ≤ first X D a ∧ first X D a < X + D ∧ first X D a % D = a := by
  have hrem := Nat.mod_lt X hD
  have hdiv := Nat.mod_add_div X D
  have hmod : first X D a % D = a := by
    rw [first, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  refine ⟨?_, ?_, hmod⟩
  · by_cases h : a < X % D
    · simp only [first, ite_eq_left h, Nat.mul_add, Nat.mul_one]
      omega
    · simp only [first, ite_eq_right h, add_zero]
      omega
  · by_cases h : a < X % D
    · simp only [first, ite_eq_left h, Nat.mul_add, Nat.mul_one]
      omega
    · simp only [first, ite_eq_right h, add_zero]
      omega

private theorem first_le {X D a n : ℕ} (hX : X ≤ n) (hmod : n % D = a) : first X D a ≤ n := by
  have hD₀ : X / D ≤ n / D := Nat.div_le_div_right hX
  have hXd := Nat.mod_add_div X D
  have hnd := Nat.mod_add_div n D
  rw [hmod] at hnd
  have hquot : X / D + (if a < X % D then 1 else 0) ≤ n / D := by
    by_cases h : a < X % D
    · rw [ite_eq_left h]
      by_contra hn
      have he : n / D = X / D := by omega
      rw [he] at hnd
      omega
    · simpa only [ite_eq_right h, add_zero] using hD₀
  calc
    _ ≤ a + D * (n / D) := Nat.add_le_add_left (Nat.mul_le_mul_left D hquot) _
    _ = n := hnd

/-- The even progression is an affine image, with length bounded above and below. -/
theorem window_affine {X r Q : ℕ} (hr : 0 < r) (hQ : 0 < Q)
    (hDr : 6 * r ≤ 3 * Q) (hX : 4 * (6 * r) ≤ X) :
    ∃ b : ℕ, X ≤ b ∧ b ≤ 2 * X ∧ 0 < (window X r).card ∧
      (6 * r) * (window X r).card ≤ 2 * X ∧
      window X r = (range (window X r).card).image (fun j => b + (6 * r) * j) ∧
      (X : ℝ) / (6 * (Q : ℝ)) ≤ ((window X r).card : ℝ) := by
  let D := 6 * r
  let a := 2 * r
  let b := first X D a
  let U := 2 * X - 3
  let L := (U - b) / D + 1
  change D ≤ 3 * Q at hDr
  change 4 * D ≤ X at hX
  have hD : 0 < D := by dsimp only [D]; omega
  have ha : a < D := by dsimp only [a, D]; omega
  have hU : U = 2 * X - 3 := rfl
  have ⟨hbX, hbD, hbMod⟩ : X ≤ b ∧ b < X + D ∧ b % D = a := first_properties X D a hD ha
  have hbU : b ≤ U := by omega
  have hImage : window X r = (range L).image (fun j => b + D * j) := by
    apply Finset.ext
    intro m
    constructor
    · intro hm
      obtain ⟨hmX, hmU, hmMod⟩ := mem_window.mp hm
      have hmU' : m ≤ U := hmU
      have hmMod' : m % D = a := hmMod
      have hbm : b ≤ m := first_le hmX hmMod'
      have hq : b / D ≤ m / D := Nat.div_le_div_right hbm
      let j := m / D - b / D
      have hB : a + D * (b / D) = b := by
        calc
          a + D * (b / D) = b % D + D * (b / D) := congrArg (fun z => z + D * (b / D)) hbMod.symm
          _ = b := Nat.mod_add_div b D
      have hM : a + D * (m / D) = m := by
        calc
          a + D * (m / D) = m % D + D * (m / D) := congrArg (fun z => z + D * (m / D)) hmMod'.symm
          _ = m := Nat.mod_add_div m D
      have he : b + D * j = m := by
        calc
          _ = (a + D * (b / D)) + D * j := congrArg (fun z => z + D * j) hB.symm
          _ = a + D * (b / D + j) := by ring
          _ = a + D * (m / D) := by rw [show b / D + j = m / D from Nat.add_sub_of_le hq]
          _ = m := hM
      have hj : j ≤ (U - b) / D := by
        apply (Nat.le_div_iff_mul_le hD).mpr
        rw [Nat.mul_comm j D]
        omega
      exact mem_image.mpr ⟨j, mem_range.mpr (Nat.lt_succ_of_le hj), he⟩
    · intro hm
      obtain ⟨j, hj, rfl⟩ := mem_image.mp hm
      have hj' : j ≤ (U - b) / D := Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hjD : D * j ≤ U - b := by
        rw [Nat.mul_comm D j]
        exact (Nat.le_div_iff_mul_le hD).mp hj'
      have hEnd : b + D * j ≤ U := by omega
      exact mem_window.mpr ⟨hbX.trans (Nat.le_add_right _ _), hEnd,
        by simpa only [Nat.add_mul_mod_self_left, D, a] using hbMod⟩
  have hinj : Function.Injective (fun j : ℕ => b + D * j) := by
    intro j l h
    exact Nat.eq_of_mul_eq_mul_left hD (Nat.add_left_cancel h)
  have hcard : (window X r).card = L := by
    rw [hImage, card_image_of_injective _ hinj, card_range]
  have hLpos : 0 < L := Nat.succ_pos _
  have hDL : D * L = D * ((U - b) / D) + D := by dsimp only [L]; rw [Nat.mul_add, Nat.mul_one]
  have hquo : D * ((U - b) / D) ≤ U - b := by
    simpa only [Nat.mul_comm D] using Nat.div_mul_le_self (U - b) D
  have hDLhi : D * L ≤ 2 * X := by omega
  have hRem := Nat.mod_lt (U - b) hD
  have hDecomp := Nat.mod_add_div (U - b) D
  have hDLlo : U - b < D * L := by omega
  have hHalf : X ≤ 2 * (D * L) := by omega
  have hBound : X ≤ (6 * Q) * L := hHalf.trans (calc
    _ = (2 * D) * L := by ring
    _ ≤ _ := Nat.mul_le_mul_right L (by omega))
  have hBoundReal : (X : ℝ) ≤ (6 * (Q : ℝ)) * (L : ℝ) := by exact_mod_cast hBound
  have hSize : (X : ℝ) / (6 * (Q : ℝ)) ≤ (L : ℝ) :=
    (div_le_iff₀ (by positivity)).mpr (by simpa only [mul_comm (L : ℝ)] using hBoundReal)
  refine ⟨b, hbX, hbU.trans (Nat.sub_le ..), ?_, ?_, ?_, ?_⟩
  · simpa only [hcard] using hLpos
  · simpa only [hcard] using hDLhi
  · conv_lhs => rw [hImage]
    rw [hcard]
  · simpa only [hcard] using hSize

end GoldbachEvenWindows

namespace GoldbachEvenControls

open Filter GoldbachMajorArc GoldbachRawModel GoldbachDyadicCoefficient
open scoped Topology

/-- The errors for the major model, the periodic remainder, and the two
residue initial segment comparisons fit inside the positive margin for large levels. -/
theorem eventually_small_errors :
    ∀ᶠ k : ℕ in atTop,
      let X : ℕ := 2^k
      let Q : ℕ := k^2
      16 ≤ k ∧ 2*Q^2 < X ∧
        kernelScale*((Q:ℝ)+1)^3 ≤ (X:ℝ)/(120*(Q:ℝ)) ∧
        8*(X:ℝ)*(Q:ℝ)^2 ≤ (X:ℝ)^2/(720*(Q:ℝ)^2) ∧
        16*(X:ℝ) ≤ (X:ℝ)^2/(720*(Q:ℝ)^2) ∧
        20*(X:ℝ)^2/(k:ℝ)^8 ≤ (X:ℝ)^2/(720*(Q:ℝ)^2) := by
  let B := 20000*(kernelScale+1)
  have hB : 0 < B := by dsimp [B]; linarith only [kernelScale_pos]
  have hB₁ : (20000:ℝ) ≤ B := by dsimp [B]; linarith only [kernelScale_pos]
  have hBₖ : 960*kernelScale ≤ B := by dsimp [B]; linarith only [kernelScale_pos]
  have hg := GoldbachRawGrowth.eventually_dyadic_log_power_le_pow 8
    (α := 1) (η := B⁻¹) (by norm_num) (inv_pos.mpr hB)
  filter_upwards [eventually_ge_atTop (16:ℕ),hg] with k hk hg'
  dsimp only
  simp only [Real.rpow_one] at hg'
  let X : ℕ := 2^k
  let Q : ℕ := k^2
  have hkR : (16:ℝ) ≤ k := by exact_mod_cast hk
  have hkP : 0 < (k:ℝ) := by linarith only [hkR]
  have hk₁ : (1:ℝ) ≤ k := by linarith only [hkR]
  have hXpos : 0 < (X:ℝ) := by dsimp [X]; positivity
  have hQ : (Q:ℝ) = (k:ℝ)^2 := by simp [Q]
  have hQ₂ : (Q:ℝ)^2 = (k:ℝ)^4 := by rw [hQ]; ring
  have hQpos : 0 < (Q:ℝ) := by rw [hQ]; positivity
  have hQplus : (Q:ℝ)+1 ≤ 2*(k:ℝ)^2 := by
    rw [hQ]
    nlinarith only [hk₁, sq_nonneg ((k:ℝ)-1)]
  have h48 : (k:ℝ)^4 ≤ (k:ℝ)^8 :=
    pow_le_pow_right₀ hk₁ (by decide)
  have hBig : B*(k:ℝ)^8 ≤ X := by
    have h := hg'
    change (k:ℝ)^8 ≤ B⁻¹*(X:ℝ) at h
    rw [inv_mul_eq_div] at h
    simpa only [mul_comm] using (le_div_iff₀ hB).mp h
  have hBase : 20000*(k:ℝ)^8 ≤ X :=
    (mul_le_mul_of_nonneg_right hB₁ (by positivity)).trans hBig
  refine ⟨hk,?_,?_,?_,?_,?_⟩
  · have hL : (2:ℝ)*(Q:ℝ)^2 < X := by
      rw [hQ₂]
      nlinarith only [h48,hBase,pow_pos hkP 8]
    exact_mod_cast hL
  · apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<120) hQpos)).mpr
    calc
      _ ≤ kernelScale*(2*(k:ℝ)^2)^3*(120*(Q:ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hQplus 3) kernelScale_pos.le
      _ = (960*kernelScale)*(k:ℝ)^8 := by rw [hQ]; ring
      _ ≤ B*(k:ℝ)^8 := mul_le_mul_of_nonneg_right hBₖ (by positivity)
      _ ≤ _ := hBig
  · apply (le_div_iff₀ (by positivity : 0 < 720*(Q:ℝ)^2)).mpr
    have hBounds : 5760*(k:ℝ)^8 ≤ X := by
      nlinarith only [hBase,pow_nonneg hkP.le 8]
    calc
      _ = (X:ℝ)*(5760*(k:ℝ)^8) := by rw [hQ₂]; ring
      _ ≤ (X:ℝ)*(X:ℝ) := mul_le_mul_of_nonneg_left hBounds hXpos.le
      _ = _ := by ring
  · apply (le_div_iff₀ (by positivity : 0 < 720*(Q:ℝ)^2)).mpr
    have hBounds : 11520*(k:ℝ)^4 ≤ X := by
      nlinarith only [h48,hBase,pow_nonneg hkP.le 8]
    calc
      _ = (X:ℝ)*(11520*(k:ℝ)^4) := by rw [hQ₂]; ring
      _ ≤ (X:ℝ)*(X:ℝ) := mul_le_mul_of_nonneg_left hBounds hXpos.le
      _ = _ := by ring
  · apply (div_le_div_iff₀ (pow_pos hkP 8) (by positivity : 0 < 720*(Q:ℝ)^2)).mpr
    have hₖ4 : (14400:ℝ) ≤ (k:ℝ)^4 := by
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 16) hkR 4
      norm_num at h
      linarith only [h]
    have hh := mul_le_mul_of_nonneg_right hₖ4 (pow_nonneg hkP.le 4)
    calc
      _ = (X:ℝ)^2*(14400*(k:ℝ)^4) := by rw [hQ₂]; ring
      _ ≤ (X:ℝ)^2*((k:ℝ)^4*(k:ℝ)^4) := mul_le_mul_of_nonneg_left hh (sq_nonneg _)
      _ = _ := by ring

theorem primeWeight_le_level {k i : ℕ} (hk : 1 ≤ k) (hi : i ≤ 2*2^k) :
    |primeWeight i| ≤ 2*(k:ℝ) := by
  by_cases hp : i.Prime
  · rw [primeWeight, ite_eq_left hp, abs_of_nonneg]
    · have hLog : Real.log (i:ℝ) ≤ Real.log (2*(2:ℝ)^k) := by
        apply Real.log_le_log
        · exact_mod_cast hp.pos
        · exact_mod_cast hi
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hLog
      have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
      norm_num at h2
      have hm := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k : 0 ≤ (k:ℝ))
      have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
      linarith only [hLog,h2,hm,hkR]
    · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · simp [primeWeight, hp]

end GoldbachEvenControls

namespace GoldbachEvenFull

open Finset GoldbachMajorArc

noncomputable section

def slice (X D a : ℕ) : Finset ℕ :=
  (Icc X (2*X-3)).filter (fun n => n % D=a)

def linearWeight (s : Finset ℕ) : ℝ := ∑ n ∈ s, ((n:ℝ)+1)

def baseFactor (r : ℕ) : ℝ := 3*(r:ℝ)/(2*((r:ℝ)-1))

theorem baseFactor_bounds {r : ℕ} (hr : 5 ≤ r) : 0 ≤ baseFactor r ∧ baseFactor r ≤ 2 := by
  have hR : (5:ℝ) ≤ r := by exact_mod_cast hr
  have hpos : 0 < 2*((r:ℝ)-1) := by linarith only [hR]
  unfold baseFactor
  exact ⟨div_nonneg (by positivity) hpos.le,
    (div_le_iff₀ hpos).mpr (by linarith only [hR])⟩

private theorem slice_eq {X D a : ℕ} (hX : 2 ≤ X) :
    slice X D a = (Ico X (2*X-2)).filter (fun n => n % D=a) := by
  ext n
  simp only [slice, mem_filter, mem_Icc, mem_Ico]
  omega

/-- The full prime convolution in a dyadic residue slice is bounded by its
local-density main term and the two uniform residue errors. -/
theorem full_window_upper (k r : ℕ) (hk : 2 ≤ k) (hr : 5 ≤ r)
    (hDsmall : 6*r ≤ 3*k^2) (μ : ℕ → ℝ)
    (hμ : ∀ b < 6*r, |μ b| ≤ 1)
    (hpair : ((6*r:ℕ):ℝ) * (∑ b ∈ range (6*r), μ b * μ ((2*r+6*r-b)%(6*r))) =
      baseFactor r)
    (hprefix : ∀ u ≤ 2*(2^k:ℕ), ∀ b < 6*r,
      |GoldbachEvenTriangle.classPrefix u (6*r) b primeWeight -
        (u:ℝ)*μ b| ≤ (((2^k:ℕ):ℝ)/(k:ℝ)^10)) :
    let X : ℕ := 2^k
    let S := slice X (6*r) (2*r)
    (∑ n ∈ S, GoldbachDyadicCoefficient.convolution n) ≤
      baseFactor r * linearWeight S + 20*(X:ℝ)^2/(k:ℝ)^8+16*(X:ℝ) := by
  dsimp only
  let X : ℕ := 2^k
  let U : ℕ := 2*X-2
  let D : ℕ := 6*r
  let a : ℕ := 2*r
  let E : ℝ := (X:ℝ)/(k:ℝ)^10
  let T := linearWeight (Ico X U)
  let S := slice X D a
  let H := linearWeight S
  have hX4 : 4 ≤ X := GoldbachDyadicCoefficient.pow_two_ge_four hk
  have hXpos : 0 < (X:ℝ) := by dsimp [X]; positivity
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : 0 < (k:ℝ) := by linarith only [hkR]
  have hD : 0 < D := by dsimp [D]; omega
  have ha : a < D := by dsimp [D,a]; omega
  have hDp : 0 < (D:ℝ) := by exact_mod_cast hD
  have hU : U ≤ 2*X := by dsimp [U]; omega
  have hXU : X ≤ U := by dsimp [U]; omega
  have hUR : (U:ℝ) ≤ 2*(X:ℝ) := by exact_mod_cast hU
  have hXr4 : (4:ℝ) ≤ X := by exact_mod_cast hX4
  have hS : S = (Ico X U).filter (fun n => n % D=a) := slice_eq (by omega)
  let σ := ∑ b ∈ range D, μ b * μ ((a+D-b)%D)
  have hσ : σ = baseFactor r/(D:ℝ) := by
    apply (eq_div_iff hDp.ne').mpr
    rw [mul_comm]
    exact hpair
  have hT := GoldbachEvenTriangle.interval_prefix_approx X U D a hXU hD ha
    primeWeight μ (2*(k:ℝ)) E (by dsimp [E]; positivity)
    (fun i hi => GoldbachEvenControls.primeWeight_le_level (by omega) ((Nat.le_of_lt hi).trans hU))
    hμ (fun m hm b hb => hprefix m (hm.trans hU) b hb)
  change |(∑ n ∈ (Ico X U).filter (fun n => n % D=a), GoldbachDyadicCoefficient.convolution n) -
    T*σ| ≤ ((X:ℝ)+(U:ℝ))*(2*(k:ℝ)+(D:ℝ))*E at hT
  rw [← hS,hσ] at hT
  have hDiff := GoldbachEvenCancel.residue_weight_Ico_discrepancy X U D a hXU hD ha
  change |linearWeight ((Ico X U).filter (fun n => n % D=a)) - T/(D:ℝ)| ≤
    2*(X:ℝ)+2*(U:ℝ)+2 at hDiff
  rw [← hS] at hDiff
  have hT_H : T/(D:ℝ) ≤ H + 8*(X:ℝ) := by
    have ha := (abs_le.mp hDiff).1
    change -(2*(X:ℝ)+2*(U:ℝ)+2) ≤ H - T/(D:ℝ) at ha
    linarith only [ha,hUR,hXr4]
  obtain ⟨hB0,hB2⟩ := baseFactor_bounds hr
  have hCenter : T*(baseFactor r/(D:ℝ)) ≤ baseFactor r*H+16*(X:ℝ) := by
    calc
      _ = baseFactor r*(T/(D:ℝ)) := by ring
      _ ≤ baseFactor r*(H+8*(X:ℝ)) := mul_le_mul_of_nonneg_left hT_H hB0
      _ = baseFactor r*H+baseFactor r*(8*(X:ℝ)) := by ring
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_right hB2 (by positivity : 0 ≤ 8*(X:ℝ))
        linarith only [h]
  have hDreal : (D:ℝ) ≤ 3*(k:ℝ)^2 := by exact_mod_cast hDsmall
  have hkTwo : (k:ℝ) ≤ (k:ℝ)^2 := by
    nlinarith only [hkR,sq_nonneg ((k:ℝ)-2)]
  have hErr : ((X:ℝ)+(U:ℝ))*(2*(k:ℝ)+(D:ℝ))*E ≤ 20*(X:ℝ)^2/(k:ℝ)^8 := by
    calc
      _ ≤ (4*(X:ℝ))*(5*(k:ℝ)^2)*E := by
        apply mul_le_mul_of_nonneg_right _ (by dsimp [E]; positivity)
        exact mul_le_mul (by linarith only [hXpos,hUR]) (by linarith only [hDreal,hkTwo])
          (by positivity) (by positivity)
      _ = _ := by
        dsimp [E]
        field_simp [hkpos.ne']; ring
  have hTriangle := (abs_le.mp hT).2
  change (∑ n ∈ S, GoldbachDyadicCoefficient.convolution n) ≤
    baseFactor r*H + 20*(X:ℝ)^2/(k:ℝ)^8+16*(X:ℝ)
  linarith only [hTriangle,hErr,hCenter]

end
end GoldbachEvenFull

namespace GoldbachEvenMajor

open Finset GoldbachMajorArc GoldbachRawKernel GoldbachRawModel GoldbachEvenFull

noncomputable section

def selected (Q D : ℕ) : Finset ℕ := (Icc 1 Q).filter (fun q => q ∣ D)

def nondivisors (Q D : ℕ) : Finset ℕ := (Icc 1 Q).filter (fun q => ¬q ∣ D)

def remainder (n Q D : ℕ) : ℂ :=
  ∑ q ∈ nondivisors Q D, coefficient q n * (mass n Q q : ℂ)

private theorem profiled_re (n Q D : ℕ) :
    (profiled n Q).re = ((n:ℝ)+1) *
      (∑ q ∈ selected Q D, coefficient q n * (profile ((Q:ℝ)/(q:ℝ)):ℂ)).re +
      (remainder n Q D).re := by
  have hSplit : profiled n Q =
      (∑ q ∈ selected Q D, coefficient q n * (mass n Q q : ℂ)) +
        remainder n Q D := by
    exact (sum_filter_add_sum_filter_not (Icc 1 Q) (fun q => q ∣ D)
      (fun q => coefficient q n * (mass n Q q : ℂ))).symm
  have hMass : (∑ q ∈ selected Q D, coefficient q n * (mass n Q q : ℂ)) =
      ((n:ℂ)+1)*(∑ q ∈ selected Q D, coefficient q n * (profile ((Q:ℝ)/(q:ℝ)):ℂ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro q _
    simp only [mass, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
    ring
  rw [hSplit,hMass]
  simp [Complex.mul_re,Complex.add_re]

private theorem remainder_sum_affine (X Q D b L : ℕ) (hX : 0 < X) (hb : b ≤ 2*X)
    (hDL : D*L ≤ 2*X) :
    ‖∑ j ∈ range L, remainder (b+D*j) Q D‖ ≤ 8*(X:ℝ)*(Q:ℝ)^2 := by
  unfold remainder
  rw [sum_comm]
  let K (q : ℕ) : ℂ := (profile ((Q:ℝ)/(q:ℝ)):ℂ)
  have hK (q : ℕ) (_ : q ∈ nondivisors Q D) : ‖K q‖ ≤ 1 := by
    obtain ⟨h0,h1⟩ := profile_bounds ((Q:ℝ)/(q:ℝ)) (by positivity)
    simpa only [K,Complex.norm_real,Real.norm_of_nonneg h0] using h1
  have hSum (q : ℕ) :
      ∑ j ∈ range L, coefficient q (b+D*j) * (mass (b+D*j) Q q : ℂ) =
        K q * (∑ j ∈ range L, (((b+D*j : ℕ):ℂ)+1) * coefficient q (b+D*j)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    simp only [K,mass,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one]
    ring
  simp_rw [hSum]
  exact GoldbachEvenCancel.window_bound X Q D b L hX hb hDL K hK

theorem pointwise_major_lower (n X Q r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hlo : 14*r ≤ 5*Q) (hhi : 5*Q < 15*r) (hX : X ≤ n)
    (hResidue : n % (6*r)=2*r) (hCut : cutoff n=Q) (hSep : 2*Q^2 < X)
    (hArc : totalArcError n ≤ (n:ℝ)/(120*(Q:ℝ)))
    (hKernel : kernelScale*((Q:ℝ)+1)^3 ≤ (X:ℝ)/(120*(Q:ℝ))) :
    ((n:ℝ)+1)*(baseFactor r + 1/(20*(Q:ℝ))) + (remainder n Q (6*r)).re ≤
      (majorContribution n).re := by
  have hQ : 0 < (Q:ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hN : 0 < n := hSep.pos.trans_le hX
  have hSep' : 2*(cutoff n)^2<n := by rw [hCut]; exact hSep.trans_le hX
  have hXn : (X:ℝ) ≤ n := by exact_mod_cast hX
  have hP : ‖profiled n Q-modeledContribution n‖ ≤ (X:ℝ)/(120*(Q:ℝ)) := by
    rw [norm_sub_rev]
    exact (model_profile_error n Q hN hCut).trans hKernel
  have hA : ‖modeledContribution n-majorContribution n‖ ≤ (n:ℝ)/(120*(Q:ℝ)) := by
    rw [norm_sub_rev]
    exact (major_error hSep').trans hArc
  have hNorm : ‖profiled n Q-majorContribution n‖ ≤ ((n:ℝ)+1)/(60*(Q:ℝ)) := by
    calc
      _ = ‖(profiled n Q-modeledContribution n)+
          (modeledContribution n-majorContribution n)‖ := by congr 1; ring
      _ ≤ ‖profiled n Q-modeledContribution n‖+
          ‖modeledContribution n-majorContribution n‖ := norm_add_le _ _
      _ ≤ (X:ℝ)/(120*(Q:ℝ))+(n:ℝ)/(120*(Q:ℝ)) := add_le_add hP hA
      _ = ((X:ℝ)+n)/(120*(Q:ℝ)) := (add_div _ _ _).symm
      _ ≤ ((n:ℝ)+n+2)/(120*(Q:ℝ)) :=
        div_le_div_of_nonneg_right (by linarith only [hXn]) (by positivity)
      _ = _ := by field_simp [hQ.ne']; ring
  have hRe := (Complex.re_le_norm (profiled n Q-majorContribution n)).trans hNorm
  rw [Complex.sub_re,profiled_re n Q (6*r)] at hRe
  have hLower := GoldbachEvenProfile.restricted_profile_floor n Q r hr hr5 hlo hhi hResidue
  change baseFactor r + 1/(15*(Q:ℝ)) ≤
    (∑ q ∈ selected Q (6*r), coefficient q n * (profile ((Q:ℝ)/(q:ℝ)):ℂ)).re at hLower
  have hLower' := mul_le_mul_of_nonneg_left hLower (by positivity : 0 ≤ (n:ℝ)+1)
  have hAdjust : ((n:ℝ)+1)*(baseFactor r + 1/(15*(Q:ℝ))) - ((n:ℝ)+1)/(60*(Q:ℝ)) =
      ((n:ℝ)+1)*(baseFactor r + 1/(20*(Q:ℝ))) := by
    field_simp [hQ.ne']
    ring
  linarith only [hRe,hLower',hAdjust]

theorem major_window_lower (X Q r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r)
    (hlo : 14*r ≤ 5*Q) (hhi : 5*Q < 15*r) (hX : 0 < X) (hSep : 2*Q^2<X)
    (hImage : ∃ b, b≤2*X ∧ (6*r)*(slice X (6*r) (2*r)).card≤2*X ∧
      slice X (6*r) (2*r) =
        (range (slice X (6*r) (2*r)).card).image (fun j => b+(6*r)*j))
    (hCut : ∀ n ∈ slice X (6*r) (2*r), cutoff n=Q)
    (hArc : ∀ n ∈ slice X (6*r) (2*r), totalArcError n ≤ (n:ℝ)/(120*(Q:ℝ)))
    (hKernel : kernelScale*((Q:ℝ)+1)^3 ≤ (X:ℝ)/(120*(Q:ℝ))) :
    let S := slice X (6*r) (2*r)
    (baseFactor r + 1/(20*(Q:ℝ)))*linearWeight S - 8*(X:ℝ)*(Q:ℝ)^2 ≤
      ∑ n ∈ S, (majorContribution n).re := by
  dsimp only
  let S := slice X (6*r) (2*r)
  let D : ℕ := 6*r
  obtain ⟨b,hb,hDL,hS⟩ := hImage
  have hD : 0 < D := by dsimp [D]; omega
  have hI : Function.Injective (fun j : ℕ => b+D*j) := by
    intro i j heq
    exact Nat.eq_of_mul_eq_mul_left hD (Nat.add_left_cancel heq)
  have hR : ‖∑ n ∈ S, remainder n Q D‖ ≤ 8*(X:ℝ)*(Q:ℝ)^2 := by
    have hS' : S = (range S.card).image (fun j => b+D*j) := hS
    have hsum : (∑ n ∈ S, remainder n Q D) =
        ∑ j ∈ range S.card, remainder (b+D*j) Q D := by
      calc
        _ = ∑ n ∈ (range S.card).image (fun j => b+D*j), remainder n Q D :=
          sum_congr hS' (fun n _ => rfl)
        _ = _ := sum_image hI.injOn
    rw [hsum]
    exact remainder_sum_affine X Q D b S.card hX hb hDL
  have hRe : - (8*(X:ℝ)*(Q:ℝ)^2) ≤ ∑ n ∈ S, (remainder n Q D).re := by
    have hh := (neg_le_abs (∑ n ∈ S, remainder n Q D).re).trans
      ((Complex.abs_re_le_norm _).trans hR)
    rw [Complex.re_sum] at hh
    linarith only [hh]
  have hbound := sum_le_sum (s:=S) (fun n hn => pointwise_major_lower n X Q r hr hr5 hlo hhi
    (mem_Icc.mp (mem_filter.mp hn).1).1 (mem_filter.mp hn).2
    (hCut n hn) hSep (hArc n hn) hKernel)
  have hProdSum :
      (∑ n ∈ S, ((n:ℝ)+1)*(baseFactor r+1/(20*(Q:ℝ)))) =
        (baseFactor r+1/(20*(Q:ℝ)))*linearWeight S := by
    rw [linearWeight,mul_sum]
    exact sum_congr rfl (fun n _ => mul_comm _ _)
  rw [sum_add_distrib,hProdSum] at hbound
  change (baseFactor r+1/(20*(Q:ℝ)))*linearWeight S +
    (∑ n ∈ S, (remainder n Q D).re) ≤ ∑ n ∈ S, (majorContribution n).re at hbound
  linarith only [hbound,hRe]

end
end GoldbachEvenMajor

namespace GoldbachEvenContradiction

open Filter Finset
open scoped Topology

/-- A sufficiently negative sum on a sequence of even subsets contradicts the
frozen mean-square estimate for the negative part. -/
theorem not_even_energy (minor : ℕ → ℝ) {b : ℝ} (hb : 0 < b)
    (hneg : ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ ∃ s : Finset ℕ,
      s ⊆ (Icc (2^k) (2*2^k)).filter Even ∧
        (∑ n ∈ s, minor n) ≤ -b*(((2^k:ℕ):ℝ)^2)/(k:ℝ)^4) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ T : ℕ, 0 < C ∧ ∀ X : ℕ, T ≤ X →
      (∑ n ∈ (Icc X (2*X)).filter Even, (max 0 (-minor n))^2) ≤ C*(X:ℝ)^(18/7+ε)) := by
  intro h
  obtain ⟨C,T,hC,hupper⟩ := h (1/7) (by norm_num)
  have hη : 0 < b^2/(4*C) := by positivity
  have hgrowth := GoldbachRawGrowth.eventually_dyadic_log_power_le_pow 8
    (α := 2/7) (η := b^2/(4*C)) (by norm_num) hη
  have ht : Tendsto (fun k : ℕ => (2:ℕ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1:ℕ)).and ((ht.eventually_ge_atTop T).and hgrowth))
  obtain ⟨k,hkK,s,hs,hMin⟩ := hneg K
  obtain ⟨hk,hT,hsmall⟩ := hK k hkK
  let X : ℕ := 2^k
  let f (n : ℕ) := -max 0 (-minor n)
  have hf (n : ℕ) : f n ≤ minor n := by
    dsimp only [f]
    linarith only [le_max_right (0:ℝ) (-minor n)]
  have hsNeg : (∑ n ∈ s, f n) ≤ -b*(X:ℝ)^2/(k:ℝ)^4 :=
    (sum_le_sum fun n _ => hf n).trans hMin
  have hXpos : 0 < X := pow_pos (by decide : 0 < (2:ℕ)) k
  have hX : 0 < (X:ℝ) := by exact_mod_cast hXpos
  have hkR : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hcard : (s.card:ℝ) ≤ 2*(X:ℝ) := by
    have hnat : s.card ≤ 2*X := calc
      _ ≤ (Icc X (2*X)).card := card_le_card (hs.trans (filter_subset Even _))
      _ = 2*X+1-X := Nat.card_Icc X (2*X)
      _ ≤ 2*X := by omega
    exact_mod_cast hnat
  have hlower := GoldbachRawGrowth.energy_ge_of_sum_le_neg hs f
    (A := b*(X:ℝ)^2/(k:ℝ)^4) (by positivity) hcard
    (by simpa only [neg_mul, neg_div] using hsNeg)
  have hup : (∑ n ∈ (Icc X (2*X)).filter Even, (f n)^2) ≤ C*(X:ℝ)^(19/7:ℝ) := by
    simpa only [f,neg_sq,show (18/7+(1/7):ℝ) = 19/7 by norm_num] using hupper X hT
  have hbnd : (b^2*(X:ℝ)^4)/(k:ℝ)^8 ≤ 2*(X:ℝ)*(C*(X:ℝ)^(19/7:ℝ)) := by
    simpa only [div_pow,mul_pow,← pow_mul,show 2*2 = (4:ℕ) by decide,show 4*2=(8:ℕ) by decide] using
      hlower.trans (mul_le_mul_of_nonneg_left hup (by positivity : 0 ≤ 2*(X:ℝ)))
  have hbad : b^2*(X:ℝ)^4 ≤ (b^2/2)*(X:ℝ)^4 := calc
    _ ≤ 2*(X:ℝ)*(C*(X:ℝ)^(19/7:ℝ))*(k:ℝ)^8 :=
      (div_le_iff₀ (pow_pos hkR 8)).mp hbnd
    _ ≤ 2*(X:ℝ)*(C*(X:ℝ)^(19/7:ℝ))*(b^2/(4*C)*(X:ℝ)^(2/7:ℝ)) := by
      exact mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = (b^2/2)*((X:ℝ)^(1:ℝ)*(X:ℝ)^(19/7:ℝ)*(X:ℝ)^(2/7:ℝ)) := by
      rw [Real.rpow_one]
      field_simp [hC.ne']
      ring
    _ = _ := by
      rw [← Real.rpow_add hX, ← Real.rpow_add hX]
      norm_num
  have hpos : 0 < b^2*(X:ℝ)^4 := by positivity
  linarith only [hbad,hpos]

end GoldbachEvenContradiction

namespace GoldbachEvenEndgame

open Filter Finset
open GoldbachMajorArc GoldbachDyadicCoefficient GoldbachRawModel GoldbachEvenFull
open scoped Topology

/-- On arbitrarily large dyadic windows, the residue slice gives a
signed minor sum of size at least a constant times X squared over Q squared. -/
theorem negative_slices (K : ℕ) : ∃ k : ℕ, K ≤ k ∧ ∃ s : Finset ℕ,
    s ⊆ (Icc (2^k) (2*2^k)).filter Even ∧
      (∑ n ∈ s, minor n) ≤ -(1/240:ℝ)*(((2^k:ℕ):ℝ)^2)/(k:ℝ)^4 := by
  obtain ⟨N,hArcError⟩ := GoldbachRawError.totalArcError_cutoff_saving (1/120) (by norm_num)
  have ht : Tendsto (fun k : ℕ => (2:ℕ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.mp
    (GoldbachEvenControls.eventually_small_errors.and
      (GoldbachEvenPrefix.uniform_dyadic_class_mass.and (ht.eventually_ge_atTop N)))
  obtain ⟨k,r,hk,hr,hr5,hlo,hhi,hXlarge⟩ := GoldbachEvenWindows.exists_prime_level (max K K₀)
  obtain ⟨hResource,hPrefix,hN⟩ := hK₀ k ((le_max_right K K₀).trans hk)
  obtain ⟨hk16,hSep,hKern,hRem,hDiscrep,hTriangle⟩ := hResource
  let X : ℕ := 2^k
  let Q : ℕ := k^2
  let D : ℕ := 6*r
  let S := slice X D (2*r)
  let H := linearWeight S
  have hXpos : 0 < X := pow_pos (by decide : 0 < (2:ℕ)) k
  have hXR : 0 < (X:ℝ) := by exact_mod_cast hXpos
  have hQpos : 0 < Q := by dsimp [Q]; positivity
  have hQR : 0 < (Q:ℝ) := by exact_mod_cast hQpos
  have hDpos : 0 < D := by dsimp [D]; omega
  have hDr : D ≤ 3*Q := by dsimp [D,Q]; omega
  have hRpos : 0 < r := by omega
  have hgeom := GoldbachEvenWindows.window_affine (X:=X) (r:=r) (Q:=Q) hRpos hQpos hDr hXlarge
  obtain ⟨a,_,ha,_,hDL,hAff,hL⟩ := hgeom
  have hImage : S = (range S.card).image (fun j => a+D*j) := hAff
  have hsub : S ⊆ (Icc X (2*X)).filter Even := by
    intro n hn
    have hs : n ∈ GoldbachEvenWindows.window X r := hn
    have ⟨hl,hu,_⟩ := GoldbachEvenWindows.mem_window.mp hs
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hl,hu.trans (Nat.sub_le _ _)⟩,
      GoldbachEvenWindows.window_even hs⟩
  have hCut (n : ℕ) (hn : n ∈ S) : cutoff n = Q := by
    have hs : n ∈ GoldbachEvenWindows.window X r := hn
    obtain ⟨hl,hu,_⟩ := GoldbachEvenWindows.mem_window.mp hs
    exact cutoff_dyadic hl hu (by omega)
  have hArc (n : ℕ) (hn : n ∈ S) : totalArcError n ≤ (n:ℝ)/(120*(Q:ℝ)) := by
    have hs : n ∈ GoldbachEvenWindows.window X r := hn
    have hsmall := hArcError n (hN.trans (GoldbachEvenWindows.mem_window.mp hs).1)
    calc
      _ ≤ (1/120:ℝ)*(n:ℝ)/(cutoff n:ℝ) := hsmall
      _ = _ := by rw [hCut n hn]; field_simp [hQR.ne']
  have hMajor :
      (baseFactor r+1/(20*(Q:ℝ)))*H - 8*(X:ℝ)*(Q:ℝ)^2 ≤
        ∑ n ∈ S, (majorContribution n).re :=
    GoldbachEvenMajor.major_window_lower X Q r hr hr5 hlo hhi hXpos hSep
      ⟨a,ha,hDL,hImage⟩ hCut hArc hKern
  let μ := GoldbachEvenResidues.density D
  have hMu (b : ℕ) (_ : b < D) : |μ b| ≤ 1 := by
    rw [abs_of_nonneg (GoldbachEvenResidues.density_nonneg D b)]
    exact GoldbachEvenResidues.density_le_one D b hDpos
  have hP (u : ℕ) (hu : u ≤ 2*X) (b : ℕ) (hb : b < D) :
      |GoldbachEvenTriangle.classPrefix u D b primeWeight - (u:ℝ)*μ b| ≤
        (X:ℝ)/(k:ℝ)^10 := by
    change |classMass u D b - (u:ℝ)*GoldbachEvenResidues.density D b| ≤ _
    rw [GoldbachEvenResidues.density_eq_div]
    exact hPrefix u D b hu hDpos hDr hb
  have hFull :
      (∑ n ∈ S, convolution n) ≤ baseFactor r*H+20*(X:ℝ)^2/(k:ℝ)^8+16*(X:ℝ) :=
    full_window_upper k r (by omega) hr5 hDr μ hMu
      (GoldbachEvenResidues.pair_mass r hr hr5) hP
  have hWeight : (X:ℝ)^2/(6*(Q:ℝ)) ≤ H := by
    calc
      _ = (X:ℝ)*((X:ℝ)/(6*(Q:ℝ))) := by ring
      _ ≤ (X:ℝ)*(S.card:ℝ) := mul_le_mul_of_nonneg_left hL hXR.le
      _ = ∑ _n ∈ S, (X:ℝ) := by simp [nsmul_eq_mul,mul_comm]
      _ ≤ H := by
        apply sum_le_sum
        intro n hn
        have hs : n ∈ GoldbachEvenWindows.window X r := hn
        have hh : (X:ℝ) ≤ n := by exact_mod_cast (GoldbachEvenWindows.mem_window.mp hs).1
        linarith only [hh]
  have hSlack : (X:ℝ)^2/(720*(Q:ℝ)^2) ≤ H/(120*(Q:ℝ)) := by
    calc
      _ = ((X:ℝ)^2/(6*(Q:ℝ)))/(120*(Q:ℝ)) := by field_simp [hQR.ne']; ring
      _ ≤ _ := div_le_div_of_nonneg_right hWeight (by positivity)
  have h1 := hRem.trans hSlack
  have h2 := hDiscrep.trans hSlack
  have h3 := hTriangle.trans hSlack
  have hCoef : (baseFactor r+1/(20*(Q:ℝ)))*H =
      baseFactor r*H+H/(20*(Q:ℝ)) := by ring
  rw [hCoef] at hMajor
  have hBalance : H/(20*(Q:ℝ))-3*(H/(120*(Q:ℝ))) = H/(40*(Q:ℝ)) := by
    field_simp [hQR.ne']
    ring
  have hSum : (∑ n ∈ S, minor n)+(∑ n ∈ S, (majorContribution n).re) = ∑ n ∈ S, convolution n := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n _
    exact minor_add_major n
  have hNeg : (∑ n ∈ S, minor n) ≤ -(H/(40*(Q:ℝ))) := by
    linarith only [hFull,hMajor,h1,h2,h3,hBalance,hSum]
  refine ⟨k,(le_max_left K K₀).trans hk,S,hsub,hNeg.trans ?_⟩
  calc
    _ ≤ -(((X:ℝ)^2/(6*(Q:ℝ)))/(40*(Q:ℝ))) :=
      neg_le_neg (div_le_div_of_nonneg_right hWeight (by positivity))
    _ = _ := by
      have hkr : (k:ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      simp only [X,Q,Nat.cast_pow]
      field_simp [hkr]
      ring

end GoldbachEvenEndgame


namespace GoldbachTailContradiction

open Filter Finset
open scoped Topology

/-- The tail-restricted form of the frozen mean-square estimate: the same
contradiction, since the negative dyadic slices occur at arbitrarily large levels. -/
theorem not_even_energy_tail (minor : ℕ → ℝ) {b : ℝ} (hb : 0 < b)
    (hneg : ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ ∃ s : Finset ℕ,
      s ⊆ (Icc (2^k) (2*2^k)).filter Even ∧
        (∑ n ∈ s, minor n) ≤ -b*(((2^k:ℕ):ℝ)^2)/(k:ℝ)^4) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∃ T : ℕ, 0 < C ∧ ∀ X : ℕ, T ≤ X → 10 ^ (12 : ℕ) < X →
      (∑ n ∈ (Icc X (2*X)).filter Even, (max 0 (-minor n))^2) ≤ C*(X:ℝ)^(18/7+ε)) := by
  intro h
  obtain ⟨C,T,hC,hupper⟩ := h (1/7) (by norm_num)
  have hη : 0 < b^2/(4*C) := by positivity
  have hgrowth := GoldbachRawGrowth.eventually_dyadic_log_power_le_pow 8
    (α := 2/7) (η := b^2/(4*C)) (by norm_num) hη
  have ht : Tendsto (fun k : ℕ => (2:ℕ)^k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by decide)
  obtain ⟨K,hK⟩ := eventually_atTop.mp
    ((eventually_ge_atTop (1:ℕ)).and
      ((ht.eventually_ge_atTop T).and ((ht.eventually_ge_atTop (10 ^ (12 : ℕ) + 1)).and hgrowth)))
  obtain ⟨k,hkK,s,hs,hMin⟩ := hneg K
  obtain ⟨hk,hT,hTail,hsmall⟩ := hK k hkK
  let X : ℕ := 2^k
  let f (n : ℕ) := -max 0 (-minor n)
  have hf (n : ℕ) : f n ≤ minor n := by
    dsimp only [f]
    linarith only [le_max_right (0:ℝ) (-minor n)]
  have hsNeg : (∑ n ∈ s, f n) ≤ -b*(X:ℝ)^2/(k:ℝ)^4 :=
    (sum_le_sum fun n _ => hf n).trans hMin
  have hXpos : 0 < X := pow_pos (by decide : 0 < (2:ℕ)) k
  have hX : 0 < (X:ℝ) := by exact_mod_cast hXpos
  have hkR : 0 < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hcard : (s.card:ℝ) ≤ 2*(X:ℝ) := by
    have hnat : s.card ≤ 2*X := calc
      _ ≤ (Icc X (2*X)).card := card_le_card (hs.trans (filter_subset Even _))
      _ = 2*X+1-X := Nat.card_Icc X (2*X)
      _ ≤ 2*X := by omega
    exact_mod_cast hnat
  have hlower := GoldbachRawGrowth.energy_ge_of_sum_le_neg hs f
    (A := b*(X:ℝ)^2/(k:ℝ)^4) (by positivity) hcard
    (by simpa only [neg_mul, neg_div] using hsNeg)
  have hup : (∑ n ∈ (Icc X (2*X)).filter Even, (f n)^2) ≤ C*(X:ℝ)^(19/7:ℝ) := by
    simpa only [f,neg_sq,show (18/7+(1/7):ℝ) = 19/7 by norm_num] using hupper X hT hTail
  have hbnd : (b^2*(X:ℝ)^4)/(k:ℝ)^8 ≤ 2*(X:ℝ)*(C*(X:ℝ)^(19/7:ℝ)) := by
    simpa only [div_pow,mul_pow,← pow_mul,show 2*2 = (4:ℕ) by decide,show 4*2=(8:ℕ) by decide] using
      hlower.trans (mul_le_mul_of_nonneg_left hup (by positivity : 0 ≤ 2*(X:ℝ)))
  have hbad : b^2*(X:ℝ)^4 ≤ (b^2/2)*(X:ℝ)^4 := calc
    _ ≤ 2*(X:ℝ)*(C*(X:ℝ)^(19/7:ℝ))*(k:ℝ)^8 :=
      (div_le_iff₀ (pow_pos hkR 8)).mp hbnd
    _ ≤ 2*(X:ℝ)*(C*(X:ℝ)^(19/7:ℝ))*(b^2/(4*C)*(X:ℝ)^(2/7:ℝ)) := by
      exact mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = (b^2/2)*((X:ℝ)^(1:ℝ)*(X:ℝ)^(19/7:ℝ)*(X:ℝ)^(2/7:ℝ)) := by
      rw [Real.rpow_one]
      field_simp [hC.ne']
      ring
    _ = _ := by
      rw [← Real.rpow_add hX, ← Real.rpow_add hX]
      norm_num
  have hpos : 0 < b^2*(X:ℝ)^4 := by positivity
  linarith only [hbad,hpos]

end GoldbachTailContradiction

open scoped Topology in
set_option maxHeartbeats 900000 in
theorem Conjectures.Cuts.Taskcbb2f0daf81df14a7059ce82_is_false : ¬ (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log (↑x1 : ℝ) else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x2) : ℂ) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x4 x6) : ℂ) * x2 ((↑x6 : ℝ) * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - (↑x8 : ℝ) / (↑x7 : ℝ)| ≤ (↑(x4 x5) : ℝ) / ((↑x7 : ℝ) * (↑x5 : ℝ))}; have x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-(↑x6 : ℝ) * x7); have x7 : ℕ → ℂ := fun (x7 : ℕ) => ∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x7).indicator (x6 x7) x8; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (∫ (x9 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x8)ᶜ.indicator (x6 x8) x9).re; ∀ (x9 : ℝ), (0 : ℝ) < x9 → ∃ (x11 : ℝ) (x12 : ℕ), (0 : ℝ) < x11 ∧ ∀ (x13 : ℕ), x12 ≤ x13 → (10 : ℕ) ^ (12 : ℕ) < x13 → ∑ x16 ∈ Finset.Icc x13 ((2 : ℕ) * x13) with Even x16, Max.max (0 : ℝ) (-x8 x16) ^ (2 : ℕ) ≤ x11 * (↑x13 : ℝ) ^ ((18 / 7 : ℝ) + x9)) := by
  exact GoldbachTailContradiction.not_even_energy_tail GoldbachDyadicCoefficient.minor
    (b := 1/240) (by norm_num) GoldbachEvenEndgame.negative_slices

open GoldbachRawKernel GoldbachRawError GoldbachRawGrowth GoldbachDyadicCoefficient GoldbachEvenCancel GoldbachRawModel GoldbachEvenProfile GoldbachEvenPrefix GoldbachEvenTriangle GoldbachEvenResidues GoldbachEvenWindows GoldbachEvenControls GoldbachEvenFull GoldbachEvenMajor GoldbachEvenContradiction GoldbachEvenEndgame GoldbachTailContradiction in
theorem Conjectures.Cuts.Refutef5308c683655359a9049a31d : ¬ (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log (↑x1 : ℝ) else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x2) : ℂ) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x4 x6) : ℂ) * x2 ((↑x6 : ℝ) * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - (↑x8 : ℝ) / (↑x7 : ℝ)| ≤ (↑(x4 x5) : ℝ) / ((↑x7 : ℝ) * (↑x5 : ℝ))}; have x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-(↑x6 : ℝ) * x7); have x7 : ℕ → ℂ := fun (x7 : ℕ) => ∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x7).indicator (x6 x7) x8; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (∫ (x9 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x8)ᶜ.indicator (x6 x8) x9).re; ∀ (x9 : ℝ), (0 : ℝ) < x9 → ∃ (x11 : ℝ) (x12 : ℕ), (0 : ℝ) < x11 ∧ ∀ (x13 : ℕ), x12 ≤ x13 → (10 : ℕ) ^ (12 : ℕ) < x13 → ∑ x16 ∈ Finset.Icc x13 ((2 : ℕ) * x13) with Even x16, Max.max (0 : ℝ) (-x8 x16) ^ (2 : ℕ) ≤ x11 * (↑x13 : ℝ) ^ ((18 / 7 : ℝ) + x9)) := by
  first
  | exact GoldbachEvenMajor.remainder_sum_affine
  | exact GoldbachEvenCancel.prefix_eq_remainder
  | exact Conjectures.Cuts.Taskcbb2f0daf81df14a7059ce82_is_false
  | exact GoldbachTailContradiction.not_even_energy_tail
  | exact GoldbachEvenEndgame.negative_slices
  | exact GoldbachEvenContradiction.not_even_energy
  | exact GoldbachEvenMajor.major_window_lower
  | exact GoldbachEvenMajor.pointwise_major_lower
  | exact GoldbachEvenMajor.profiled_re
  | exact GoldbachEvenFull.full_window_upper
  | exact GoldbachEvenFull.slice_eq
  | exact GoldbachEvenFull.baseFactor_bounds
