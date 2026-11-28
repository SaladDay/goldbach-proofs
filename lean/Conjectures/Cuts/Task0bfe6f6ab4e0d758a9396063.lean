import Mathlib

open scoped BigOperators

namespace Conjectures.Cuts.Task0bfe6f6ab4e0d758a9396063_aux

/-- The weight `w` is the prime logarithmic weight. -/
lemma summand {w : ℕ → ℝ}
    (hw : ∀ k, w k = if Nat.Prime k then Real.log (k : ℝ) else 0) (k : ℕ) :
    ArithmeticFunction.vonMangoldt k - w k =
      if ¬ Nat.Prime k then ArithmeticFunction.vonMangoldt k else 0 := by
  rw [hw k]
  by_cases hp : Nat.Prime k
  · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp [hp]

lemma gap_nonneg {w : ℕ → ℝ}
    (hw : ∀ k, w k = if Nat.Prime k then Real.log (k : ℝ) else 0) (k : ℕ) :
    0 ≤ ArithmeticFunction.vonMangoldt k - w k := by
  rw [summand hw k]
  by_cases hp : Nat.Prime k
  · simp [hp]
  · simp [hp, ArithmeticFunction.vonMangoldt_nonneg]

lemma range_insert (n : ℕ) : Finset.range (n + 1) = insert 0 (Finset.Ioc 0 n) := by
  ext k
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
  omega

/-- The total gap is exactly the Chebyshev prime-power difference `ψ - θ`. -/
lemma sum_gap {w : ℕ → ℝ}
    (hw : ∀ k, w k = if Nat.Prime k then Real.log (k : ℝ) else 0) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt k - w k)) =
      Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ) := by
  have h1 : (∑ k ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt k - w k)) =
      ∑ k ∈ Finset.range (n + 1),
        (if ¬ Nat.Prime k then ArithmeticFunction.vonMangoldt k else 0) := by
    refine Finset.sum_congr rfl fun k _ => summand hw k
  rw [h1, range_insert, Finset.sum_insert (by simp), ← Finset.sum_filter]
  have h0 : (if ¬ Nat.Prime 0 then ArithmeticFunction.vonMangoldt 0 else 0) = 0 := by
    simp
  rw [h0, zero_add, Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]

/-- Uniform spectral bound: the gap sum has norm at most the total gap. -/
lemma norm_gap_le {w : ℕ → ℝ}
    (hw : ∀ k, w k = if Nat.Prime k then Real.log (k : ℝ) else 0)
    (E : ℝ → ℂ) (hE : ∀ y, ‖E y‖ = 1) (n : ℕ) (t : ℝ) :
    ‖∑ k ∈ Finset.range (n + 1),
        ((ArithmeticFunction.vonMangoldt k : ℂ) * E ((k : ℝ) * t)) -
      ∑ k ∈ Finset.range (n + 1), ((w k : ℂ) * E ((k : ℝ) * t))‖ ≤
      ∑ k ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt k - w k) := by
  have hdiff :
      (∑ k ∈ Finset.range (n + 1),
          ((ArithmeticFunction.vonMangoldt k : ℂ) * E ((k : ℝ) * t))) -
        ∑ k ∈ Finset.range (n + 1), ((w k : ℂ) * E ((k : ℝ) * t)) =
      ∑ k ∈ Finset.range (n + 1),
        ((ArithmeticFunction.vonMangoldt k - w k : ℝ) : ℂ) * E ((k : ℝ) * t) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sub_mul, ← Complex.ofReal_sub]
  rw [hdiff]
  calc
    ‖∑ k ∈ Finset.range (n + 1),
        ((ArithmeticFunction.vonMangoldt k - w k : ℝ) : ℂ) * E ((k : ℝ) * t)‖
        ≤ ∑ k ∈ Finset.range (n + 1),
            ‖((ArithmeticFunction.vonMangoldt k - w k : ℝ) : ℂ) * E ((k : ℝ) * t)‖ :=
          norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt k - w k) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gap_nonneg hw k),
          hE, mul_one]

end Conjectures.Cuts.Task0bfe6f6ab4e0d758a9396063_aux

theorem Conjectures.Cuts.Task0bfe6f6ab4e0d758a9396063 :
    have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * x2) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), ↑(x4 x6) * x2 (↑x6 * x5); ∃ (x4 : ℕ), ∀ x5 ≥ x4, ∀ (x7 : ℝ), ‖x3 x5 (⇑ArithmeticFunction.vonMangoldt) x7 - x3 x5 x1 x7‖ ≤ ↑x5 ^ (2 / 3 : ℝ) := by
  intro x1 x2 x3
  have hw : ∀ k, x1 k = if Nat.Prime k then Real.log (k : ℝ) else 0 := fun _ => rfl
  have hE : ∀ y : ℝ, ‖x2 y‖ = 1 := by
    intro y
    dsimp only [x2]
    exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * y)
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hEv : ∀ᶠ y : ℝ in Filter.atTop, C ≤ y ^ (1 / 6 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).eventually_ge_atTop C
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hEv
  refine ⟨max 2 ⌈a⌉₊, ?_⟩
  intro n hn t
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hna : a ≤ (n : ℝ) :=
    le_trans (Nat.le_ceil a) (by exact_mod_cast le_trans (le_max_right _ _) hn)
  have hC6 : C ≤ (n : ℝ) ^ (1 / 6 : ℝ) := ha (n : ℝ) hna
  have hxpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx0 : (0 : ℝ) ≤ (n : ℝ) := hxpos.le
  have hgap :
      ‖x3 n (⇑ArithmeticFunction.vonMangoldt) t - x3 n x1 t‖ ≤
        ∑ k ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt k - x1 k) := by
    dsimp only [x3]
    exact Conjectures.Cuts.Task0bfe6f6ab4e0d758a9396063_aux.norm_gap_le hw x2 hE n t
  have htotal :
      (∑ k ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt k - x1 k)) =
        Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ) :=
    Conjectures.Cuts.Task0bfe6f6ab4e0d758a9396063_aux.sum_gap hw n
  have hsq : Real.sqrt (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have hrw : (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) = (n : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hxpos]
    norm_num
  calc
    ‖x3 n (⇑ArithmeticFunction.vonMangoldt) t - x3 n x1 t‖
        ≤ ∑ k ∈ Finset.range (n + 1), (ArithmeticFunction.vonMangoldt k - x1 k) := hgap
    _ = Chebyshev.psi (n : ℝ) - Chebyshev.theta (n : ℝ) := htotal
    _ ≤ C * Real.sqrt (n : ℝ) := hC (n : ℝ)
    _ = C * (n : ℝ) ^ (1 / 2 : ℝ) := by rw [hsq]
    _ ≤ (n : ℝ) ^ (1 / 6 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hC6 (Real.rpow_nonneg hx0 _)
    _ = (n : ℝ) ^ (2 / 3 : ℝ) := by rw [mul_comm, hrw]
