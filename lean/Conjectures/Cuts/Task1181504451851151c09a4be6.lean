import Mathlib
import PEqualNP.Outside.L_goldbach_proper_power_correction

/-!
# Cut `L-goldbach-cut-1181504451851151c09a4be6`

Premise 2/2 of a cut of `L-goldbach-cut-756d10db76cd43da7f0162e7`.

For every dyadic scale `N = 2 ^ k`, the cells `[N / 2 + j * H, N / 2 + (j + 1) * H)`
of length `H = 2 ^ (k - k / 4)`, for `j < 2 ^ (k / 4 - 3)`, carry a von Mangoldt
correlation whose excess over the prime-only logarithmic correlation is at most
`N / 1000`.

The excess is a sum of nonnegative terms, and the whole range `0 ≤ n ≤ N` already
has total excess bounded by `C √N (log N) ^ 3` (the accepted lemma
`L-goldbach-proper-power-correction`), which is below `N / 1000` once `N` is a
large power of two.
-/

open Finset
open scoped BigOperators

namespace Conjectures.Cuts.Task1181504451851151c09a4be6_aux

noncomputable def w (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0

noncomputable def corr (N k : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt k * ArithmeticFunction.vonMangoldt (N - k) - w k * w (N - k)

theorem sum_range_mul_sum_range (g : ℕ → ℝ) (C H : ℕ) :
    ∑ a ∈ Finset.range C, ∑ b ∈ Finset.range H, g (a * H + b) =
      ∑ k ∈ Finset.range (C * H), g k := by
  induction C with
  | zero => simp
  | succ C ih =>
    rw [Finset.sum_range_succ, ih, Nat.succ_mul, Finset.sum_range_add]

theorem sum_cell (g : ℕ → ℝ) (base H C : ℕ) :
    ∑ a ∈ Finset.range C, ∑ b ∈ Finset.range H, g (base + a * H + b) =
      ∑ k ∈ Finset.range (C * H), g (base + k) := by
  simpa only [Nat.add_assoc] using sum_range_mul_sum_range (fun k => g (base + k)) C H

theorem w_nonneg (k : ℕ) : 0 ≤ w k := by
  dsimp [w]
  split_ifs
  · exact Real.log_natCast_nonneg k
  · exact le_refl 0

theorem w_le_mangoldt (k : ℕ) : w k ≤ ArithmeticFunction.vonMangoldt k := by
  dsimp [w]
  by_cases hk : Nat.Prime k
  · simp [hk, ArithmeticFunction.vonMangoldt_apply_prime hk]
  · simp [hk, ArithmeticFunction.vonMangoldt_nonneg]

theorem corr_nonneg (N k : ℕ) : 0 ≤ corr N k := by
  have h1 : 0 ≤ ArithmeticFunction.vonMangoldt k - w k := by linarith [w_le_mangoldt k]
  have h2 : 0 ≤ ArithmeticFunction.vonMangoldt (N - k) - w (N - k) := by
    linarith [w_le_mangoldt (N - k)]
  have h3 : 0 ≤ ArithmeticFunction.vonMangoldt (N - k) := ArithmeticFunction.vonMangoldt_nonneg
  have h4 : 0 ≤ w k := w_nonneg k
  have key : corr N k =
      (ArithmeticFunction.vonMangoldt k - w k) * ArithmeticFunction.vonMangoldt (N - k) +
        w k * (ArithmeticFunction.vonMangoldt (N - k) - w (N - k)) := by
    dsimp [corr]; ring
  rw [key]
  exact add_nonneg (mul_nonneg h1 h3) (mul_nonneg h4 h2)

theorem pow_dom (K : ℝ) (_hK : 0 ≤ K) (x : ℕ)
    (hx : Nat.ceil (2985984 * K) + 10000 ≤ x) :
    K * (x : ℝ) ^ 3 ≤ (2 : ℝ) ^ ((x : ℝ) / 2) := by
  have hx12 : 12 ≤ x := by omega
  have hKx : 2985984 * K ≤ (x : ℝ) := by
    have h1 : (Nat.ceil (2985984 * K) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast (by omega : Nat.ceil (2985984 * K) ≤ x)
    have h2 : 2985984 * K ≤ (Nat.ceil (2985984 * K) : ℝ) := Nat.le_ceil _
    linarith
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hxcube : (x : ℝ) ≤ (x : ℝ) ^ 3 := by
    have heq : (x : ℝ) ^ 3 = (x : ℝ) * (x : ℝ) * (x : ℝ) := by ring
    have h2 : (x : ℝ) ≤ (x : ℝ) * (x : ℝ) := by nlinarith
    have h3 : (x : ℝ) * (x : ℝ) ≤ (x : ℝ) * (x : ℝ) * (x : ℝ) := by nlinarith
    linarith
  have hfloor : ((x / 12 : ℕ) : ℝ) ≤ (x : ℝ) / 12 := by
    have h := Nat.div_mul_le_self x 12
    have hc : ((x / 12 * 12 : ℕ) : ℝ) = ((x / 12 : ℕ) : ℝ) * 12 := by push_cast; ring
    have h2 : ((x / 12 : ℕ) : ℝ) * 12 ≤ (x : ℝ) := by
      rw [← hc]; exact_mod_cast h
    linarith
  have hlt : (x : ℝ) / 12 < ((x / 12 : ℕ) : ℝ) + 1 := by
    have hxle : x ≤ 12 * (x / 12) + 11 := by
      have h := Nat.div_add_mod x 12
      have hmod : x % 12 < 12 := Nat.mod_lt x (by norm_num)
      omega
    have hc : ((12 * (x / 12) + 11 : ℕ) : ℝ) = ((x / 12 : ℕ) : ℝ) * 12 + 11 := by
      push_cast; ring
    have h2 : (x : ℝ) ≤ ((x / 12 : ℕ) : ℝ) * 12 + 11 := by rw [← hc]; exact_mod_cast hxle
    linarith
  have hp1 : ((x / 12 : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ ((x / 12 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    have h2 : (x / 12 : ℕ) + 1 ≤ 2 ^ (x / 12) := Nat.lt_two_pow_self
    exact_mod_cast h2
  have hrpow : (2 : ℝ) ^ ((x / 12 : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((x : ℝ) / 12) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
  have h12 : (x : ℝ) / 12 ≤ (2 : ℝ) ^ ((x : ℝ) / 12) := by linarith
  have hpow6 : ((2 : ℝ) ^ ((x : ℝ) / 12)) ^ (6 : ℕ) = (2 : ℝ) ^ ((x : ℝ) / 2) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((x : ℝ) / 12)) 6, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hcub : ((x : ℝ) / 12) ^ (6 : ℕ) ≤ (2 : ℝ) ^ ((x : ℝ) / 2) := by
    rw [← hpow6]
    exact pow_le_pow_left₀ (by positivity) h12 6
  have hmul : K ≤ (x : ℝ) ^ 3 / 2985984 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  calc
    K * (x : ℝ) ^ 3 ≤ ((x : ℝ) ^ 3 / 2985984) * (x : ℝ) ^ 3 := by
      exact mul_le_mul_of_nonneg_right hmul (by positivity)
    _ = ((x : ℝ) / 12) ^ (6 : ℕ) := by ring
    _ ≤ (2 : ℝ) ^ ((x : ℝ) / 2) := hcub

end Conjectures.Cuts.Task1181504451851151c09a4be6_aux

open Conjectures.Cuts.Task1181504451851151c09a4be6_aux

theorem Conjectures.Cuts.Task1181504451851151c09a4be6 :
    ∃ (x1 : ℕ),   ∀ x2 ≥ x1,     have x4 : ℕ := (2 : ℕ) ^ x2;     have x5 : ℕ := (2 : ℕ) ^ (x2 - x2 / (4 : ℕ));     have x6 : ℕ := (2 : ℕ) ^ (x2 / (4 : ℕ) - (3 : ℕ));     have x7 : ℕ → ℕ → ℕ := fun (x7 x8 : ℕ) => x4 / (2 : ℕ) + x7 * x5 + x8;     have x8 : ℕ → ℝ := fun (x8 : ℕ) => if Nat.Prime x8 then Real.log ↑x8 else (0 : ℝ);     ∑ x9 ∈ Finset.range x6, ∑ x10 ∈ Finset.range x5, ArithmeticFunction.vonMangoldt (x7 x9 x10) * ArithmeticFunction.vonMangoldt (x4 - x7 x9 x10) - ∑ x9 ∈ Finset.range x6, ∑ x10 ∈ Finset.range x5, x8 (x7 x9 x10) * x8 (x4 - x7 x9 x10) ≤ ↑x4 / (1000 : ℝ) := by
  obtain ⟨C0, hC0pos, hmain⟩ := PEqualNP.Outside.L_goldbach_proper_power_correction
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Nat.ceil (2985984 * (1000 * C0 * (Real.log 2) ^ 3)) + 10000, ?_⟩
  intro x2 hx2
  dsimp only
  set N : ℕ := 2 ^ x2
  set H : ℕ := 2 ^ (x2 - x2 / 4)
  set C : ℕ := 2 ^ (x2 / 4 - 3)
  simp only [← Finset.sum_sub_distrib]
  change (∑ a ∈ Finset.range C, ∑ b ∈ Finset.range H,
      corr N (N / 2 + a * H + b)) ≤ (N : ℝ) / 1000
  have hx12 : 12 ≤ x2 := by omega
  have hCH : C * H = 2 ^ (x2 - 3) := by
    dsimp [C, H]
    rw [← pow_add]
    congr 1
    omega
  have hNeq : N = 8 * 2 ^ (x2 - 3) := by
    dsimp [N]
    have h : x2 = (x2 - 3) + 3 := by omega
    conv_lhs => rw [h]
    rw [pow_add]
    ring
  have hhalf : N / 2 = 4 * 2 ^ (x2 - 3) := by
    rw [hNeq]
    omega
  have hcell : ∀ k ∈ Finset.range (C * H), N / 2 + k ≤ N := by
    intro k hk
    have hk' : k < 2 ^ (x2 - 3) := by rw [← hCH]; exact Finset.mem_range.mp hk
    rw [hhalf, hNeq]
    omega
  have himage : (Finset.range (C * H)).image (fun k => N / 2 + k) ⊆
      Finset.range (N + 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hj, rfl⟩
    have := hcell j hj
    exact Finset.mem_range.mpr (by omega)
  have hsum_le : (∑ k ∈ Finset.range (C * H), corr N (N / 2 + k)) ≤
      ∑ k ∈ Finset.range (N + 1), corr N k := by
    calc
      (∑ k ∈ Finset.range (C * H), corr N (N / 2 + k))
          = ∑ k ∈ (Finset.range (C * H)).image (fun k => N / 2 + k), corr N k := by
            rw [Finset.sum_image]
            intro a _ b _ hab
            dsimp only at hab
            omega
      _ ≤ ∑ k ∈ Finset.range (N + 1), corr N k :=
            Finset.sum_le_sum_of_subset_of_nonneg himage
              (fun k _ _ => corr_nonneg N k)
  have hN2 : 2 ≤ N := by
    rw [hNeq]
    calc
      2 ≤ 8 * 1 := by omega
      _ ≤ 8 * 2 ^ (x2 - 3) := Nat.mul_le_mul_left 8 Nat.one_le_two_pow
  have hD := hmain N hN2
  dsimp only at hD
  have hfin : (∑ k ∈ Finset.range (N + 1), corr N k) ≤
      C0 * Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 3 := by
    have hD2 := hD.2
    rw [← Finset.sum_sub_distrib] at hD2
    simpa only [corr, w] using hD2
  have hNpow : (N : ℝ) = (2 : ℝ) ^ (x2 : ℝ) := by
    dsimp [N]
    rw [Real.rpow_natCast, Nat.cast_pow]
    norm_num
  have hsq : Real.sqrt ((N : ℝ)) = (2 : ℝ) ^ ((x2 : ℝ) / 2) := by
    rw [hNpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  have hlog : Real.log ((N : ℝ)) = (x2 : ℝ) * Real.log 2 := by
    dsimp [N]
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have hsq2 : (2 : ℝ) ^ ((x2 : ℝ) / 2) * (2 : ℝ) ^ ((x2 : ℝ) / 2) = (N : ℝ) := by
    rw [← Real.rpow_add (by norm_num), hNpow]
    congr 1
    ring
  have h2pos : 0 ≤ (2 : ℝ) ^ ((x2 : ℝ) / 2) := by positivity
  calc
    (∑ a ∈ Finset.range C, ∑ b ∈ Finset.range H, corr N (N / 2 + a * H + b))
        = ∑ k ∈ Finset.range (C * H), corr N (N / 2 + k) := sum_cell (corr N) (N / 2) H C
    _ ≤ ∑ k ∈ Finset.range (N + 1), corr N k := hsum_le
    _ ≤ C0 * Real.sqrt (N : ℝ) * (Real.log (N : ℝ)) ^ 3 := hfin
    _ ≤ (N : ℝ) / 1000 := by
        rw [hsq, hlog]
        have hK := pow_dom (1000 * C0 * (Real.log 2) ^ 3) (by positivity) x2 hx2
        have hstep : (1000 * C0 * (Real.log 2) ^ 3 * (x2 : ℝ) ^ 3) *
            (2 : ℝ) ^ ((x2 : ℝ) / 2) ≤
            (2 : ℝ) ^ ((x2 : ℝ) / 2) * (2 : ℝ) ^ ((x2 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hK h2pos
        calc
          C0 * (2 : ℝ) ^ ((x2 : ℝ) / 2) * ((x2 : ℝ) * Real.log 2) ^ 3
              = ((1000 * C0 * (Real.log 2) ^ 3 * (x2 : ℝ) ^ 3) *
                  (2 : ℝ) ^ ((x2 : ℝ) / 2)) / 1000 := by ring
          _ ≤ ((2 : ℝ) ^ ((x2 : ℝ) / 2) * (2 : ℝ) ^ ((x2 : ℝ) / 2)) / 1000 :=
              div_le_div_of_nonneg_right hstep (by norm_num)
          _ = (N : ℝ) / 1000 := by rw [hsq2]
