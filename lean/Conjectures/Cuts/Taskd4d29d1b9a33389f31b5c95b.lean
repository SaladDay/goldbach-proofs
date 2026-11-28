import Mathlib

/-!
Bounded base segment of the Farey inverse sieve, threshold 7.
For 7 ≤ n ≤ 12 with n even, n ∈ {8, 10, 12}; in each case every m of the base segment
`Icc ((n+2)/3) (2n/3)` either has `minFac m = 2 ≤ ⌊n^(1/3)⌋₊` or is prime, hence
`m / minFac m = 1`; so the sieve set x3 n is empty and the Goldbach count is 0, which is
below (16/25) * x4 n because the volume x4 n is nonnegative.  (n = 6 does not satisfy the
bound, so 7 is the smallest admissible threshold.)
-/

namespace Conjectures.Cuts.Taskd4d29d1b9a33389f31b5c95b_aux

private theorem factor_nonneg {p : ℕ} (h : 2 ≤ p) : (0 : ℝ) ≤ 1 - (2 : ℝ) / (p : ℝ) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 2) h
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h
  rw [sub_nonneg, div_le_one hp]
  linarith

private theorem volume_nonneg (I : ℕ → Finset ℕ) (n : ℕ) :
    0 ≤ (↑(I n).card : ℝ) * (↑n.totient : ℝ) / (↑n : ℝ) *
      ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt) with ¬p ∣ n,
        ((1 : ℝ) - (2 : ℝ) / (p : ℝ)) := by
  have hprod : 0 ≤ ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) n.sqrt) with ¬p ∣ n,
        ((1 : ℝ) - (2 : ℝ) / (p : ℝ)) := by
    refine Finset.prod_nonneg (fun p hp => ?_)
    have hp' := Finset.mem_filter.mp hp
    exact factor_nonneg (Finset.mem_Icc.mp (Finset.mem_filter.mp hp'.1).1).1
  exact mul_nonneg
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) hprod

private theorem cube_floor_ge_two {n : ℕ} (h : 8 ≤ n) : 2 ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ := by
  apply Nat.le_floor
  have hcube : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  have hn : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  have hmono : (8 : ℝ) ^ (1 / 3 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hn (by norm_num)
  linarith

end Conjectures.Cuts.Taskd4d29d1b9a33389f31b5c95b_aux

theorem Conjectures.Cuts.Taskd4d29d1b9a33389f31b5c95b :
    have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → ℕ := fun (x2 : ℕ) => ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | x2 x3 < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x4.sqrt) with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); ∃ (x5 : ℕ), ∀ (x6 : ℕ), x5 ≤ x6 → x6 ≤ (12 : ℕ) → Even x6 → (↑{x10 ∈ x3 x6 | Nat.Prime (x6 - x10)}.card : ℝ) ≤ (16 / 25 : ℝ) * x4 x6 := by
  intro x1 x2 x3 x4
  refine ⟨7, ?_⟩
  intro x6 hlo hhi hEven
  obtain ⟨k, hk⟩ := hEven
  have hcases : x6 = 8 ∨ x6 = 10 ∨ x6 = 12 := by omega
  have hvol : 0 ≤ x4 x6 :=
    Conjectures.Cuts.Taskd4d29d1b9a33389f31b5c95b_aux.volume_nonneg x1 x6
  have hempty : x3 x6 = ∅ := by
    rcases hcases with rfl | rfl | rfl
    · have hx1 : x1 8 = {3, 4, 5} := by decide
      have hge : 2 ≤ x2 8 := Conjectures.Cuts.Taskd4d29d1b9a33389f31b5c95b_aux.cube_floor_ge_two (by norm_num)
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun m hm => ?_)
      have hm' : m ∈ x1 8 ∧ x2 8 < m.minFac ∧ Nat.Prime m.minFac ∧ Nat.Prime (m / m.minFac) := by
        rw [Finset.mem_filter] at hm
        exact hm
      rw [hx1] at hm'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
      rcases hm' with ⟨hmem, hlt, _, hq⟩
      rcases hmem with rfl | rfl | rfl
      · have hmf : (3 : ℕ).minFac = 3 := Nat.Prime.minFac_eq (by decide)
        rw [hmf] at hq
        norm_num at hq
      · have hm4 : (4 : ℕ).minFac = 2 := by decide
        rw [hm4] at hlt
        omega
      · have hmf : (5 : ℕ).minFac = 5 := Nat.Prime.minFac_eq (by decide)
        rw [hmf] at hq
        norm_num at hq
    · have hx1 : x1 10 = {4, 5, 6} := by decide
      have hge : 2 ≤ x2 10 := Conjectures.Cuts.Taskd4d29d1b9a33389f31b5c95b_aux.cube_floor_ge_two (by norm_num)
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun m hm => ?_)
      have hm' : m ∈ x1 10 ∧ x2 10 < m.minFac ∧ Nat.Prime m.minFac ∧ Nat.Prime (m / m.minFac) := by
        rw [Finset.mem_filter] at hm
        exact hm
      rw [hx1] at hm'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
      rcases hm' with ⟨hmem, hlt, _, hq⟩
      rcases hmem with rfl | rfl | rfl
      · have hm4 : (4 : ℕ).minFac = 2 := by decide
        rw [hm4] at hlt
        omega
      · have hmf : (5 : ℕ).minFac = 5 := Nat.Prime.minFac_eq (by decide)
        rw [hmf] at hq
        norm_num at hq
      · have hm6 : (6 : ℕ).minFac = 2 := by decide
        rw [hm6] at hlt
        omega
    · have hx1 : x1 12 = {4, 5, 6, 7, 8} := by decide
      have hge : 2 ≤ x2 12 := Conjectures.Cuts.Taskd4d29d1b9a33389f31b5c95b_aux.cube_floor_ge_two (by norm_num)
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun m hm => ?_)
      have hm' : m ∈ x1 12 ∧ x2 12 < m.minFac ∧ Nat.Prime m.minFac ∧ Nat.Prime (m / m.minFac) := by
        rw [Finset.mem_filter] at hm
        exact hm
      rw [hx1] at hm'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm'
      rcases hm' with ⟨hmem, hlt, _, hq⟩
      rcases hmem with rfl | rfl | rfl | rfl | rfl
      · have hm4 : (4 : ℕ).minFac = 2 := by decide
        rw [hm4] at hlt
        omega
      · have hmf : (5 : ℕ).minFac = 5 := Nat.Prime.minFac_eq (by decide)
        rw [hmf] at hq
        norm_num at hq
      · have hm6 : (6 : ℕ).minFac = 2 := by decide
        rw [hm6] at hlt
        omega
      · have hmf : (7 : ℕ).minFac = 7 := Nat.Prime.minFac_eq (by decide)
        rw [hmf] at hq
        norm_num at hq
      · have hm8 : (8 : ℕ).minFac = 2 := by decide
        rw [hm8] at hlt
        omega
  have hcard : (↑{x10 ∈ x3 x6 | Nat.Prime (x6 - x10)}.card : ℝ) = 0 := by
    have hsub : {x10 ∈ x3 x6 | Nat.Prime (x6 - x10)} ⊆ x3 x6 := Finset.filter_subset _ _
    have hz : {x10 ∈ x3 x6 | Nat.Prime (x6 - x10)} = ∅ :=
      Finset.subset_empty.mp (hsub.trans (by rw [hempty]))
    rw [hz]
    simp
  rw [hcard]
  linarith
