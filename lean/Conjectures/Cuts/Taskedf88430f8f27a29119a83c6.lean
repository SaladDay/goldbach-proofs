import Mathlib

/-!
Initial-segment restriction of the dyadic type-II matrix minor-arc integral.

For every even `n ≤ 10^12` the major-arc set `x6 n` contains the whole interval
`[0,1]`: by Dirichlet's approximation theorem every `t ∈ [0,1]` has a reduced
fraction `a/q` with `q ≤ ⌊n^(1/3)⌋` and `|t - a/q| ≤ 1/(q ⌊n^(1/3)⌋)`, and the
arc radius `256 ⌊n^(1/3)⌋ (log₂(n+2))^2 / (q n)` dominates `1/(q ⌊n^(1/3)⌋)`
because `n ≤ 256 ⌊n^(1/3)⌋^2 (log₂(n+2))^2` on the whole initial segment
(`n^(1/3) ≤ 64` for `n < 2^18`, and `log₂(n+2) ≥ 18`, `n^(1/3) ≤ 10^4` above).
Hence the minor-arc indicator vanishes on `[0,1]`, the integral is exactly `0`,
and the claimed `ε n` bound holds for every `ε > 0`.  For `n = 0` the
coefficient sums are empty.  Adapted from the reflection idea of
Conjectures.Cuts.Task8681b110dfc0625ae26222ac.
-/

open Finset Set

namespace Conjectures.Cuts.Taskedf88430f8f27a29119a83c6_aux

private lemma bucket (t : ℝ) (N : ℕ) (hN : 1 ≤ N) (k₁ k₂ : ℕ)
    (h : ⌊Int.fract ((k₁:ℝ)*t) * N⌋₊ = ⌊Int.fract ((k₂:ℝ)*t) * N⌋₊) :
    |Int.fract ((k₂:ℝ)*t) - Int.fract ((k₁:ℝ)*t)| ≤ 1/N := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hA' : ((⌊Int.fract ((k₁:ℝ)*t) * N⌋₊ : ℕ) : ℝ) ≤ Int.fract ((k₁:ℝ)*t)*N := by
    exact_mod_cast Nat.floor_le (show 0 ≤ Int.fract ((k₁:ℝ)*t)*N by positivity)
  have hB' : Int.fract ((k₁:ℝ)*t)*N < ((⌊Int.fract ((k₁:ℝ)*t) * N⌋₊ : ℕ) : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (Int.fract ((k₁:ℝ)*t)*N)
  have hC' : ((⌊Int.fract ((k₂:ℝ)*t) * N⌋₊ : ℕ) : ℝ) ≤ Int.fract ((k₂:ℝ)*t)*N := by
    exact_mod_cast Nat.floor_le (show 0 ≤ Int.fract ((k₂:ℝ)*t)*N by positivity)
  have hD' : Int.fract ((k₂:ℝ)*t)*N < ((⌊Int.fract ((k₂:ℝ)*t) * N⌋₊ : ℕ) : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (Int.fract ((k₂:ℝ)*t)*N)
  rw [h] at hA' hB'
  rw [abs_le]
  constructor
  · have hx : Int.fract ((k₁:ℝ)*t) - Int.fract ((k₂:ℝ)*t) ≤ 1/N := by
      rw [le_div_iff₀ hNpos]; nlinarith
    linarith
  · rw [le_div_iff₀ hNpos]
    nlinarith

/-- Pigeonhole form of Dirichlet's approximation theorem. -/
lemma dirichlet_int (t : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ N ∧ ∃ a : ℤ, |(q:ℝ)*t - a| ≤ 1/N := by
  classical
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  let f : ℕ → ℕ := fun k => ⌊Int.fract ((k:ℝ)*t) * N⌋₊
  have hf : ∀ k ∈ range (N+1), f k ∈ range N := by
    intro k _
    have h1 : Int.fract ((k:ℝ)*t) * N < N := by
      have := Int.fract_lt_one ((k:ℝ)*t)
      nlinarith
    have h2 : 0 ≤ Int.fract ((k:ℝ)*t) * N := by positivity
    simp only [f, Finset.mem_range, Nat.floor_lt h2]
    exact h1
  obtain ⟨k₁, hk₁, k₂, hk₂, hne, hfEq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simp) hf
  have hk₁' : k₁ ≤ N := by simpa using hk₁
  have hk₂' : k₂ ≤ N := by simpa using hk₂
  have hmain := abs_le.mp (bucket t N hN k₁ k₂ hfEq)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨k₂ - k₁, by omega, by omega, ⌊(k₂:ℝ)*t⌋ - ⌊(k₁:ℝ)*t⌋, ?_⟩
    have hsub : ((k₂ - k₁ : ℕ) : ℝ) = (k₂:ℝ) - (k₁:ℝ) := Nat.cast_sub (le_of_lt hlt)
    have e1 := Int.self_sub_fract ((k₂:ℝ)*t)
    have e2 := Int.self_sub_fract ((k₁:ℝ)*t)
    rw [hsub]
    push_cast
    rw [abs_le]
    constructor <;> linarith [hmain.1, hmain.2]
  · refine ⟨k₁ - k₂, by omega, by omega, ⌊(k₁:ℝ)*t⌋ - ⌊(k₂:ℝ)*t⌋, ?_⟩
    have hsub : ((k₁ - k₂ : ℕ) : ℝ) = (k₁:ℝ) - (k₂:ℝ) := Nat.cast_sub (le_of_lt hgt)
    have e1 := Int.self_sub_fract ((k₁:ℝ)*t)
    have e2 := Int.self_sub_fract ((k₂:ℝ)*t)
    rw [hsub]
    push_cast
    rw [abs_le]
    constructor <;> linarith [hmain.1, hmain.2]

private lemma proj_dist (q : ℕ) (t : ℝ) (a : ℤ)
    (hqt0 : (0:ℝ) ≤ (q:ℝ)*t) (hqt1 : (q:ℝ)*t ≤ (q:ℝ)) :
    |(q:ℝ)*t - ((max 0 (min a (q:ℤ)) : ℤ):ℝ)| ≤ |(q:ℝ)*t - (a:ℝ)| := by
  have hq0 : (0:ℤ) ≤ (q:ℤ) := by omega
  rcases le_or_gt a (q:ℤ) with h1 | h1
  · rcases le_or_gt 0 a with h2 | h2
    · have e : max 0 (min a (q:ℤ)) = a := by rw [min_eq_left h1, max_eq_right h2]
      rw [e]
    · have e : max 0 (min a (q:ℤ)) = 0 := by rw [min_eq_left h1, max_eq_left (le_of_lt h2)]
      have h2' : (a:ℝ) < 0 := by exact_mod_cast h2
      rw [e]
      push_cast
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  · have e : max 0 (min a (q:ℤ)) = (q:ℤ) := by rw [min_eq_right (le_of_lt h1), max_eq_right hq0]
    have h1' : (q:ℝ) ≤ (a:ℝ) := by exact_mod_cast (le_of_lt h1)
    rw [e]
    push_cast
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- Dirichlet's approximation theorem in lowest terms, for `t ∈ [0,1]`. -/
lemma dirichlet (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (N : ℕ) (hN : 1 ≤ N) :
    ∃ q a : ℕ, 1 ≤ q ∧ q ≤ N ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a:ℝ)/(q:ℝ)| ≤ 1/((q:ℝ)*(N:ℝ)) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have h1N : (1:ℝ)/N ≤ 1 := by
    rw [div_le_one hNpos]; exact_mod_cast hN
  obtain ⟨q, hq1, hqN, a, ha⟩ := dirichlet_int t N hN
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq1
  have hqt0 : (0:ℝ) ≤ (q:ℝ)*t := by positivity
  have hqt1 : (q:ℝ)*t ≤ (q:ℝ) := by nlinarith
  have ha' := proj_dist q t a hqt0 hqt1
  have hadist : |(q:ℝ)*t - ((max 0 (min a (q:ℤ)) : ℤ):ℝ)| ≤ 1/N := le_trans ha' ha
  have hlow : (0:ℤ) ≤ max 0 (min a (q:ℤ)) := le_max_left _ _
  have hhigh : max 0 (min a (q:ℤ)) ≤ (q:ℤ) := by
    have hq0 : (0:ℤ) ≤ (q:ℤ) := by omega
    exact max_le hq0 (min_le_right _ _)
  set A : ℕ := (max 0 (min a (q:ℤ))).toNat
  have hA : (A:ℤ) = max 0 (min a (q:ℤ)) := Int.toNat_of_nonneg hlow
  have hA' : (A:ℝ) = ((max 0 (min a (q:ℤ)) : ℤ):ℝ) := by exact_mod_cast hA
  have hAq : A ≤ q := by omega
  have hdist : |t - (A:ℝ)/(q:ℝ)| ≤ 1/((q:ℝ)*(N:ℝ)) := by
    have heq : t - (A:ℝ)/(q:ℝ) = ((q:ℝ)*t - (A:ℝ))/(q:ℝ) := by field_simp
    rw [heq, abs_div, abs_of_pos hqpos, hA']
    have hstep : |(q:ℝ)*t - ((max 0 (min a (q:ℤ)) : ℤ):ℝ)| / (q:ℝ) ≤ (1/N)/(q:ℝ) := by
      rw [div_le_div_iff₀ hqpos hqpos]
      nlinarith [hadist]
    refine le_trans hstep ?_
    rw [div_div, mul_comm]
  set d : ℕ := Nat.gcd A q
  have hdA : d ∣ A := Nat.gcd_dvd_left A q
  have hdq : d ∣ q := Nat.gcd_dvd_right A q
  have hdpos : 0 < d := (Nat.gcd_ne_zero_right (show q ≠ 0 by omega)).bot_lt
  have hdqle : d ≤ q := Nat.le_of_dvd hq1 hdq
  refine ⟨q / d, A / d, Nat.div_pos hdqle hdpos, le_trans (Nat.div_le_self q d) hqN,
    Nat.div_le_div_right hAq, ?_, ?_⟩
  · exact Nat.coprime_div_gcd_div_gcd hdpos
  · have hAeq : (A:ℝ) = ((A/d : ℕ):ℝ) * (d:ℝ) := by
      exact_mod_cast (Nat.div_mul_cancel hdA).symm
    have hqeq : (q:ℝ) = ((q/d : ℕ):ℝ) * (d:ℝ) := by
      exact_mod_cast (Nat.div_mul_cancel hdq).symm
    have hd0 : (d:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
    have hval : ((A/d : ℕ):ℝ)/((q/d : ℕ):ℝ) = (A:ℝ)/(q:ℝ) := by
      rw [hAeq, hqeq]; field_simp
    rw [hval]
    have hqd : (q:ℝ) = ((q/d : ℕ):ℝ) * (d:ℝ) := hqeq
    have hq'pos : (0:ℝ) < ((q/d : ℕ):ℝ) := by
      have : 0 < q / d := Nat.div_pos hdqle hdpos
      exact_mod_cast this
    have hqdle : ((q/d : ℕ):ℝ) ≤ (q:ℝ) := by exact_mod_cast Nat.div_le_self q d
    refine le_trans hdist ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

private lemma rpow_third (x : ℝ) (hx : 0 ≤ x) : (x ^ (1/3:ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- On the initial segment `n ≤ 10^12` the Farey radius `256 ⌊n^(1/3)⌋ (log₂(n+2))^2`
dominates `n / ⌊n^(1/3)⌋`. -/
lemma radius_bound (n : ℕ) (hn1 : 1 ≤ n) (hn : n ≤ 10 ^ 12) :
    (n:ℝ) ≤ 256 * ((⌊(n:ℝ) ^ (1/3:ℝ)⌋₊ : ℕ) : ℝ) ^ 2 *
      ((Nat.log 2 (n + 2) : ℕ) : ℝ) ^ 2 := by
  set Q : ℕ := ⌊(n:ℝ) ^ (1/3:ℝ)⌋₊
  set L : ℕ := Nat.log 2 (n + 2)
  have hn0 : (0:ℝ) ≤ (n:ℝ) := by positivity
  have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
  have hQ1 : (n:ℝ) ^ (1/3:ℝ) < (Q:ℝ) + 1 := Nat.lt_floor_add_one _
  have hQ2 : (1:ℝ) ≤ (n:ℝ) ^ (1/3:ℝ) := Real.one_le_rpow hn1' (by norm_num)
  have hQpos : 1 ≤ Q := Nat.le_floor hQ2
  have hQ3 : (n:ℝ) ^ (1/3:ℝ) ≤ 2 * (Q:ℝ) := by
    have : (1:ℝ) ≤ (Q:ℝ) := by exact_mod_cast hQpos
    linarith
  have hQ4 : ((n:ℝ) ^ (1/3:ℝ)) ^ 2 ≤ (2 * (Q:ℝ)) ^ 2 := by
    nlinarith
  have hQ5 : ((n:ℝ) ^ (1/3:ℝ)) ^ 2 = (n:ℝ) ^ (2/3:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]
    norm_num
  have hQ6 : (n:ℝ) ^ (2/3:ℝ) ≤ 4 * (Q:ℝ) ^ 2 := by linarith
  have hcube := rpow_third (n:ℝ) hn0
  have hsplit : (n:ℝ) = (n:ℝ) ^ (2/3:ℝ) * (n:ℝ) ^ (1/3:ℝ) := by
    rw [← Real.rpow_add (by linarith)]
    norm_num
  have hkey : (n:ℝ) ^ (1/3:ℝ) ≤ 64 * ((L:ℝ) ^ 2) := by
    rcases le_or_gt n (2 ^ 18 - 2) with hsmall | hbig
    · have hL : 1 ≤ L := Nat.log_pos (by norm_num) (by omega)
      have hL' : (1:ℝ) ≤ (L:ℝ) ^ 2 := by
        have : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
        nlinarith
      have hnle : (n:ℝ) ≤ 64 ^ 3 := by
        have : n ≤ 64 ^ 3 := by omega
        exact_mod_cast this
      have hthird : (n:ℝ) ^ (1/3:ℝ) ≤ 64 := by
        by_contra hlt
        push_neg at hlt
        have h3 := pow_lt_pow_left₀ hlt (by norm_num : (0:ℝ) ≤ 64) (by norm_num : (3:ℕ) ≠ 0)
        linarith
      nlinarith
    · have hL : 18 ≤ L := by
        apply Nat.le_log_of_pow_le (by norm_num)
        omega
      have hL' : (324:ℝ) ≤ (L:ℝ) ^ 2 := by
        have : (18:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
        nlinarith
      have hnle : (n:ℝ) ≤ (10 ^ 4) ^ 3 := by
        have : n ≤ (10 ^ 4) ^ 3 := by omega
        exact_mod_cast this
      have hthird : (n:ℝ) ^ (1/3:ℝ) ≤ 10 ^ 4 := by
        by_contra hlt
        push_neg at hlt
        have h3 := pow_lt_pow_left₀ hlt (by norm_num : (0:ℝ) ≤ 10 ^ 4) (by norm_num : (3:ℕ) ≠ 0)
        linarith
      nlinarith
  calc (n:ℝ) = (n:ℝ) ^ (2/3:ℝ) * (n:ℝ) ^ (1/3:ℝ) := hsplit
    _ ≤ (n:ℝ) ^ (2/3:ℝ) * (64 * ((L:ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg hn0 _)
    _ ≤ (4 * (Q:ℝ) ^ 2) * (64 * ((L:ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hQ6 (by positivity)
    _ = 256 * (Q:ℝ) ^ 2 * ((L:ℝ) ^ 2) := by ring

end Conjectures.Cuts.Taskedf88430f8f27a29119a83c6_aux

theorem Conjectures.Cuts.Taskedf88430f8f27a29119a83c6 : have x1 : ℝ → ℂ := fun (x1 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x1) : ℂ) * Complex.I); have x2 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x2 : ℕ) (x3 : ℕ → ℝ) (x4 : ℝ) => ∑ x5 ∈ Finset.range (x2 + (1 : ℕ)), (↑(x3 x5) : ℂ) * x1 ((↑x5 : ℝ) * x4); have x3 : ℕ → ℕ := fun (x3 : ℕ) => Nat.log (2 : ℕ) (x3 + (2 : ℕ)) ^ (2 : ℕ); have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊(↑x4 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x5 : ℕ → ℕ := fun (x5 : ℕ) => (256 : ℕ) * x4 x5 * x3 x5; have x6 : ℕ → Set ℝ := fun (x6 : ℕ) => {x7 : ℝ | ∃ (x8 : ℕ) (x9 : ℕ), (1 : ℕ) ≤ x8 ∧ x8 ≤ x4 x6 ∧ x9 ≤ x8 ∧ x9.Coprime x8 ∧ |x7 - (↑x9 : ℝ) / (↑x8 : ℝ)| ≤ (↑(x5 x6) : ℝ) / ((↑x8 : ℝ) * (↑x6 : ℝ))}; have x7 : ArithmeticFunction ℝ := ArithmeticFunction.vonMangoldt; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (↑((ArithmeticFunction.moebius : ℕ → ℤ) x8) : ℝ); have x9 : ℕ → ℕ := fun (x9 : ℕ) => ⌊(↑x9 : ℝ) ^ (1 / 16 : ℝ)⌋₊; have x10 : ℕ → ℕ := fun (x10 : ℕ) => ⌊(↑x10 : ℝ) ^ (1 / 4 : ℝ)⌋₊; have x11 : ℕ → ℕ := fun (x11 : ℕ) => ⌊(↑x11 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x12 : ℕ → ℕ := fun (x12 : ℕ) => ⌊(↑x12 : ℝ) ^ (2 / 3 : ℝ)⌋₊; have x13 : ℕ → ℕ → ℝ := fun (x13 x14 : ℕ) => ∑ x15 ∈ x14.divisors with x10 x13 < x15 ∧ x15 ≤ x11 x13 ∧ x9 x13 < x14 / x15, (∑ x16 ∈ x15.divisors with x9 x13 < x16, x8 x16) * (x7 : ℕ → ℝ) (x14 / x15); have x14 : ℕ → ℕ → ℝ := fun (x14 x15 : ℕ) => ∑ x16 ∈ x15.divisors with x11 x14 < x16 ∧ x16 ≤ x12 x14 ∧ x9 x14 < x15 / x16, (∑ x17 ∈ x16.divisors with x9 x14 < x17, x8 x17) * (x7 : ℕ → ℝ) (x15 / x16); have x15 : ℕ → (ℕ → ℝ) → (ℕ → ℝ) → ℂ := fun (x15 : ℕ) (x16 x17 : ℕ → ℝ) => ∫ (x18 : ℝ) in (0 : ℝ)..(1 : ℝ), (x6 x15)ᶜ.indicator (fun (x19 : ℝ) => x2 x15 x16 x19 * x2 x15 x17 x19 * x1 (-(↑x15 : ℝ) * x19)) x18; ∀ (x16 : ℝ), (0 : ℝ) < x16 → ∀ x18 ≤ (10 : ℕ) ^ (12 : ℕ), Even x18 → ‖x15 x18 (x13 x18) (x14 x18)‖ ≤ x16 * (↑x18 : ℝ) := by
  intro e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 J ε hε n hn hEven
  have hzero : (J n (e13 n) (e14 n)) = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · have h13 : e13 0 0 = 0 := by
        simp [e13, e10, e11]
      have h2 : ∀ t : ℝ, e2 0 (e13 0) t = 0 := by
        intro t
        have hsum : e2 0 (e13 0) t = (↑(e13 0 0) : ℂ) * e1 ((0:ℝ) * t) := by
          simp [e2]
        rw [hsum, h13]
        simp
      have hpt : ∀ x : ℝ, e2 0 (e13 0) x * e2 0 (e14 0) x * e1 (-(0:ℝ) * x) = 0 := by
        intro x
        rw [h2 x]
        simp
      show (∫ t in (0:ℝ)..1, (e6 0)ᶜ.indicator
        (fun x => e2 0 (e13 0) x * e2 0 (e14 0) x * e1 (-(0:ℝ) * x)) t) = 0
      have hfun : (fun t : ℝ => (e6 0)ᶜ.indicator
          (fun x => e2 0 (e13 0) x * e2 0 (e14 0) x * e1 (-(0:ℝ) * x)) t) = fun _ => (0:ℂ) := by
        funext t
        by_cases ht : t ∈ (e6 0)ᶜ
        · rw [Set.indicator_of_mem ht, hpt t]
        · rw [Set.indicator_of_notMem ht]
      rw [hfun]
      exact intervalIntegral.integral_zero
    · have hQ : 1 ≤ e4 n := by
        have h1 : (1:ℝ) ≤ (n:ℝ) ^ (1/3:ℝ) :=
          Real.one_le_rpow (by exact_mod_cast hn1) (by norm_num)
        exact Nat.le_floor h1
      have hmem : ∀ t ∈ Icc (0:ℝ) 1, t ∈ e6 n := by
        intro t ht
        obtain ⟨q, a, hq1, hqQ, haq, hcop, hdist⟩ :=
          Conjectures.Cuts.Taskedf88430f8f27a29119a83c6_aux.dirichlet t ht.1 ht.2 (e4 n) hQ
        refine ⟨q, a, hq1, hqQ, haq, hcop, ?_⟩
        have hR := Conjectures.Cuts.Taskedf88430f8f27a29119a83c6_aux.radius_bound n hn1 hn
        have h5 : ((e5 n : ℕ):ℝ) = 256 * ((e4 n : ℕ):ℝ) * ((Nat.log 2 (n+2) : ℕ):ℝ)^2 := by
          unfold e5 e3
          push_cast
          ring
        have hqpos : (0:ℝ) < q := by exact_mod_cast hq1
        have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn1
        have hQpos : (0:ℝ) < ((e4 n : ℕ):ℝ) := by exact_mod_cast hQ
        have hR' : (q:ℝ) * (n:ℝ) ≤ (q:ℝ) *
            (256 * ((e4 n : ℕ):ℝ)^2 * ((Nat.log 2 (n+2) : ℕ):ℝ)^2) :=
          mul_le_mul_of_nonneg_left hR (le_of_lt hqpos)
        refine le_trans hdist ?_
        rw [h5]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have hc : EqOn (fun t : ℝ => (e6 n)ᶜ.indicator
          (fun x => e2 n (e13 n) x * e2 n (e14 n) x * e1 (-(n:ℝ) * x)) t)
        (fun _ => (0:ℂ)) (uIcc (0:ℝ) 1) := by
        intro t ht
        have ht' : t ∈ Icc (0:ℝ) 1 := by
          rw [Set.uIcc_of_le (by norm_num)] at ht; exact ht
        have hnot : t ∉ (e6 n)ᶜ := fun h => h (hmem t ht')
        exact Set.indicator_of_notMem hnot _
      show (∫ t in (0:ℝ)..1, (e6 n)ᶜ.indicator
        (fun x => e2 n (e13 n) x * e2 n (e14 n) x * e1 (-(n:ℝ) * x)) t) = 0
      rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_zero]
  rw [hzero]
  simp only [norm_zero]
  exact mul_nonneg (le_of_lt hε) (Nat.cast_nonneg n)
