import Mathlib

/-!
Refutation of `L-goldbach-cut-4b0fdb6043478256e517d88e` (premise 1/2 of
`L-goldbach-cut-991fba3dc9691a61bf8f6a62`).

Mahler's identity (1936):
  (9 t^4)^3 + (m (m^3 - 9 t^3))^3 + (3 t (m^3 - 3 t^3))^3 = m^12,
valid for all m, t.  For 1 ≤ t ≤ m/4 all three coordinates lie in [1, m^4], so with
A = Finset.Icc 1 (m^4) the fiber of P(a)+P(b)+P(c) over m^12 (P = X^3) has at least
m/4 elements, while (m^4)^(1/8) = √m.  Hence no constant x5 can work for x3 = 1/8.
-/

namespace Refute4b0f

private def tri (m t : ℕ) : Fin 3 → ℕ :=
  ![9 * t ^ 4, m * (m ^ 3 - 9 * t ^ 3), 3 * t * (m ^ 3 - 3 * t ^ 3)]

private lemma tri_zero (m t : ℕ) : tri m t 0 = 9 * t ^ 4 := by simp [tri]
private lemma tri_one (m t : ℕ) : tri m t 1 = m * (m ^ 3 - 9 * t ^ 3) := by simp [tri]
private lemma tri_two (m t : ℕ) : tri m t 2 = 3 * t * (m ^ 3 - 3 * t ^ 3) := by simp [tri]

private lemma cube_bound {m t : ℕ} (h : 4 * t ≤ m) : 64 * t ^ 3 ≤ m ^ 3 := by
  have h' : (4 * t) ^ 3 ≤ m ^ 3 := Nat.pow_le_pow_left h 3
  have h'' : (4 * t) ^ 3 = 64 * t ^ 3 := by
    rw [Nat.mul_pow]
  omega

private lemma fourth_bound {m t : ℕ} (h : 4 * t ≤ m) : 256 * t ^ 4 ≤ m ^ 4 := by
  have h' : (4 * t) ^ 4 ≤ m ^ 4 := Nat.pow_le_pow_left h 4
  have h'' : (4 * t) ^ 4 = 256 * t ^ 4 := by
    rw [Nat.mul_pow]
  omega

private lemma tri_bound {m t : ℕ} (ht : 1 ≤ t) (h : 4 * t ≤ m) (i : Fin 3) :
    1 ≤ tri m t i ∧ tri m t i ≤ m ^ 4 := by
  have hc := cube_bound h
  have hf := fourth_bound h
  have ht3 : 1 ≤ t ^ 3 := by simpa using Nat.pow_le_pow_left ht 3
  have ht4 : 1 ≤ t ^ 4 := by simpa using Nat.pow_le_pow_left ht 4
  have hm1 : 1 ≤ m := by omega
  have h9 : 1 + 9 * t ^ 3 ≤ m ^ 3 := by omega
  have h3 : 1 + 3 * t ^ 3 ≤ m ^ 3 := by omega
  have ha : 1 ≤ 9 * t ^ 4 ∧ 9 * t ^ 4 ≤ m ^ 4 := by omega
  have hb : 1 ≤ m * (m ^ 3 - 9 * t ^ 3) ∧ m * (m ^ 3 - 9 * t ^ 3) ≤ m ^ 4 := by
    refine ⟨one_le_mul_of_one_le_of_one_le hm1 (by omega), ?_⟩
    calc m * (m ^ 3 - 9 * t ^ 3) ≤ m * m ^ 3 := Nat.mul_le_mul_left m (Nat.sub_le _ _)
      _ = m ^ 4 := by ring
  have hd : 1 ≤ 3 * t * (m ^ 3 - 3 * t ^ 3) ∧ 3 * t * (m ^ 3 - 3 * t ^ 3) ≤ m ^ 4 := by
    refine ⟨one_le_mul_of_one_le_of_one_le (by omega) (by omega), ?_⟩
    calc 3 * t * (m ^ 3 - 3 * t ^ 3) ≤ 3 * t * m ^ 3 :=
          Nat.mul_le_mul_left (3 * t) (Nat.sub_le _ _)
      _ ≤ m * m ^ 3 := Nat.mul_le_mul_right (m ^ 3) (by omega)
      _ = m ^ 4 := by ring
  fin_cases i
  · exact ha
  · exact hb
  · exact hd

private lemma tri_mem {m t : ℕ} (ht : 1 ≤ t) (h : 4 * t ≤ m) :
    tri m t ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.Icc 1 (m ^ 4)) := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  exact tri_bound ht h i

private lemma tri_sum {m t : ℕ} (h : 4 * t ≤ m) :
    ∑ i : Fin 3, Polynomial.eval ((tri m t i : ℕ) : ℤ) ((Polynomial.X : Polynomial ℤ) ^ 3) =
      ((m ^ 12 : ℕ) : ℤ) := by
  have hc := cube_bound h
  have h9 : 9 * t ^ 3 ≤ m ^ 3 := by omega
  have h3 : 3 * t ^ 3 ≤ m ^ 3 := by omega
  simp only [Polynomial.eval_pow, Polynomial.eval_X]
  rw [Fin.sum_univ_three, tri_zero, tri_one, tri_two]
  push_cast [h9, h3]
  ring

private lemma tri_injective (m : ℕ) : Function.Injective (tri m) := by
  intro t t' h
  have h0 : tri m t 0 = tri m t' 0 := by rw [h]
  rw [tri_zero, tri_zero] at h0
  have h1 : t ^ 4 = t' ^ 4 := Nat.eq_of_mul_eq_mul_left (by norm_num) h0
  exact Nat.pow_left_injective (by norm_num) h1

/-- The negation of the cut premise `L-goldbach-cut-4b0fdb6043478256e517d88e`. -/
theorem not_task :
    ¬ (∀ (x1 : Polynomial ℤ), (3 : ℕ) ≤ x1.natDegree → ∀ (x3 : ℝ), (0 : ℝ) < x3 →
      ∃ (x5 : ℝ), (0 : ℝ) < x5 ∧ ∀ (x6 : ℕ), (2 : ℕ) ≤ x6 →
        ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6, ∀ (x10 : ℤ),
          ↑{x11 ∈ Fintype.piFinset fun (x11 : Fin (3 : ℕ)) => x8 |
            ∑ x12 : Fin (3 : ℕ), Polynomial.eval (↑(x11 x12)) x1 = x10}.card ≤
            x5 * ↑x6 ^ x3) := by
  intro h
  have hdeg : (3 : ℕ) ≤ ((Polynomial.X : Polynomial ℤ) ^ 3).natDegree := by simp
  obtain ⟨x5, hx5, h⟩ := h ((Polynomial.X : Polynomial ℤ) ^ 3) hdeg (1 / 8) (by norm_num)
  let a : ℝ := 64 * x5 ^ 2 + 1
  let m : ℕ := max 8 (Nat.ceil a)
  have hm8 : 8 ≤ m := le_max_left _ _
  have hmx : a ≤ (m : ℝ) := by
    have h1 : a ≤ (Nat.ceil a : ℝ) := Nat.le_ceil a
    have h2 : (Nat.ceil a : ℝ) ≤ (m : ℝ) := by
      dsimp [m]
      exact_mod_cast le_max_right 8 (Nat.ceil a)
    linarith
  have ha : 64 * x5 ^ 2 + 1 ≤ (m : ℝ) := hmx
  have h2 : (2 : ℕ) ≤ m ^ 4 := by
    have h4 := Nat.pow_le_pow_left hm8 4
    omega
  have hbound := h (m ^ 4) h2 (Finset.Icc 1 (m ^ 4)) (Finset.Subset.refl _)
    ((m ^ 12 : ℕ) : ℤ)
  have hsub : (Finset.Icc 1 (m / 4)).image (tri m) ⊆
      ({x11 ∈ Fintype.piFinset fun (_ : Fin 3) => (Finset.Icc 1 (m ^ 4) : Finset ℕ) |
        ∑ x12 : Fin 3, Polynomial.eval ((x11 x12 : ℕ) : ℤ) ((Polynomial.X : Polynomial ℤ) ^ 3) =
          ((m ^ 12 : ℕ) : ℤ)} : Finset (Fin 3 → ℕ)) := by
    intro f hf
    rw [Finset.mem_image] at hf
    obtain ⟨t, ht, rfl⟩ := hf
    rw [Finset.mem_Icc] at ht
    rw [Finset.mem_filter]
    exact ⟨tri_mem ht.1 (by omega), tri_sum (by omega)⟩
  have hinj := tri_injective m
  have hcard' : m / 4 ≤ ((Finset.Icc 1 (m / 4)).image (tri m)).card := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hcard := le_trans hcard' (Finset.card_le_card hsub)
  have hpow : ((m : ℝ) ^ 4) ^ ((1 : ℝ) / 8) = Real.sqrt (m : ℝ) := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have h4 : (m : ℝ) ^ (4 : ℕ) = (m : ℝ) ^ ((4 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
    rw [h4, ← Real.rpow_mul hm0]
    have h48 : ((4 : ℕ) : ℝ) * ((1 : ℝ) / 8) = 1 / 2 := by norm_num
    rw [h48, ← Real.sqrt_eq_rpow]
  have hsq : (8 * x5) ^ 2 < (m : ℝ) := by nlinarith
  have hlt : 8 * x5 < Real.sqrt (m : ℝ) := Real.lt_sqrt_of_sq_lt hsq
  have hsqrtpos : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hmul := mul_lt_mul_of_pos_right hlt hsqrtpos
  rw [Real.mul_self_sqrt (by positivity)] at hmul
  have hfloor : (m : ℝ) ≤ 4 * ((m / 4 : ℕ) : ℝ) + 3 := by
    have : m ≤ 4 * (m / 4) + 3 := by omega
    exact_mod_cast this
  have hq : (1 : ℝ) ≤ ((m / 4 : ℕ) : ℝ) := by
    have : 1 ≤ m / 4 := by omega
    exact_mod_cast this
  have hfinal : x5 * Real.sqrt (m : ℝ) < ((m / 4 : ℕ) : ℝ) := by nlinarith
  have hle : ((m / 4 : ℕ) : ℝ) ≤ x5 * ((m : ℝ) ^ 4) ^ ((1 : ℝ) / 8) := by
    calc ((m / 4 : ℕ) : ℝ) ≤ _ := by exact_mod_cast hcard
      _ ≤ x5 * ↑(m ^ 4) ^ ((1 : ℝ) / 8) := hbound
      _ = x5 * ((m : ℝ) ^ 4) ^ ((1 : ℝ) / 8) := by rw [Nat.cast_pow]
  rw [hpow] at hle
  linarith

end Refute4b0f

open Refute4b0f in
theorem Conjectures.Cuts.Refutea794150010d043c188831761 : ¬ (∀ (x1 : Polynomial ℤ), (3 : ℕ) ≤ x1.natDegree → ∀ (x3 : ℝ), (0 : ℝ) < x3 → ∃ (x5 : ℝ), (0 : ℝ) < x5 ∧ ∀ (x6 : ℕ), (2 : ℕ) ≤ x6 → ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6, ∀ (x10 : ℤ), ↑{x11 ∈ Fintype.piFinset fun (x11 : Fin (3 : ℕ)) => x8 | ∑ x12 : Fin (3 : ℕ), Polynomial.eval (↑(x11 x12)) x1 = x10}.card ≤ x5 * ↑x6 ^ x3) := by
  first
  | exact Refute4b0f.not_task
  | exact Refute4b0f.tri_injective
  | exact Refute4b0f.tri_sum
  | exact Refute4b0f.tri_mem
  | exact Refute4b0f.tri_bound
  | exact Refute4b0f.fourth_bound
  | exact Refute4b0f.cube_bound
  | exact Refute4b0f.tri_two
  | exact Refute4b0f.tri_one
  | exact Refute4b0f.tri_zero
