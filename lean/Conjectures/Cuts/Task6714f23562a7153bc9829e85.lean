import Mathlib

/-!
# Pairs of triples with equal polynomial sums and equal coordinate sums

For a polynomial `P` of degree at least `2`, a finite set `A` of natural numbers and
the set `T` of ordered pairs `z = (x, y)` of triples `x, y : Fin 3 -> A` with
`sum P (x i) = sum P (y i)` and `sum x i = sum y i`, we show

`|T| <= 2 * deg P * sum_k tau(|N k|) + (deg P + 1)^2 |A|^3`,

where `k = (x 0, y 0, x 1)` runs over `A^3` and `N k = P (a + c - b) + P b - P a - P c`.
The pairs with `N k = 0` are counted directly (`(deg P + 1)^2 |A|^3`), and for the
others the last coordinate difference `delta = (b - a - c) + y 2` divides `N k`, while
`y 1` is a root of a nonzero difference polynomial of degree at most `deg P`.

The divisor estimate `divisor_bound` is adapted from the accepted
`Conjectures.Goldbach.QuarticSquareSlice`; the difference-polynomial and signed-divisor
machinery is adapted from the accepted `Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b`.
-/

namespace Conjectures.Cuts.Task6714f23562a7153bc9829e85_aux

open Finset Polynomial Classical
open scoped BigOperators

/-- For `a > 1` and `e : ℕ`, `e + 1 ≤ C * a ^ e` with `C = max 1 (1 / (a - 1))`. -/
private lemma succ_le_mul_pow {a : ℝ} (ha : 1 < a) (e : ℕ) :
    (e + 1 : ℝ) ≤ max 1 (1 / (a - 1)) * a ^ e := by
  have ht : 0 < a - 1 := by linarith
  have h1 : 1 + (e : ℝ) * (a - 1) ≤ a ^ e := by
    have := one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ a - 1) e
    simpa [add_sub_cancel] using this
  have hC1 : 1 ≤ max 1 (1 / (a - 1)) := le_max_left _ _
  have hCt : 1 ≤ max 1 (1 / (a - 1)) * (a - 1) :=
    (div_le_iff₀ ht).mp (le_max_right _ _)
  have he : (e : ℝ) ≤ max 1 (1 / (a - 1)) * (a - 1) * (e : ℝ) := by
    have := mul_le_mul_of_nonneg_right hCt (Nat.cast_nonneg e)
    linarith
  calc (e + 1 : ℝ) ≤ max 1 (1 / (a - 1)) + max 1 (1 / (a - 1)) * (a - 1) * (e : ℝ) := by
        linarith
    _ = max 1 (1 / (a - 1)) * (1 + (e : ℝ) * (a - 1)) := by ring
    _ ≤ max 1 (1 / (a - 1)) * a ^ e :=
        mul_le_mul_of_nonneg_left h1 (le_trans zero_le_one hC1)

/-- `e + 1 ≤ 2 ^ e` for `e : ℕ`. -/
private lemma succ_le_two_pow (e : ℕ) : (e + 1 : ℝ) ≤ (2 : ℝ) ^ e := by
  calc (e + 1 : ℝ) = 1 + (e : ℝ) * 1 := by ring
    _ ≤ (1 + 1 : ℝ) ^ e := one_add_mul_le_pow (by norm_num) e
    _ = (2 : ℝ) ^ e := by norm_num

theorem divisor_bound : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ)^ε := by
  intro ε hε
  classical
  have ha : 1 < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
  have hC0ex : ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ e : ℕ, (e + 1 : ℝ) ≤ C0 * ((2 : ℝ) ^ ε) ^ e :=
    ⟨max 1 (1 / ((2 : ℝ) ^ ε - 1)), le_max_left _ _, fun e => succ_le_mul_pow ha e⟩
  obtain ⟨C0, hC0, hC0e⟩ := hC0ex
  set P : ℕ := ⌈(2 : ℝ) ^ (ε⁻¹)⌉₊
  refine ⟨C0 ^ P, pow_pos (lt_of_lt_of_le zero_lt_one hC0) P, ?_⟩
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.divisors_zero, Real.zero_rpow hε.ne']
  have hcard : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.card_divisors hn
  have hper : ∀ p ∈ n.primeFactors,
      ((n.factorization p + 1 : ℕ) : ℝ) ≤
        (if (p : ℝ) ^ ε < 2 then C0 else 1) * ((p : ℝ) ^ ε) ^ n.factorization p := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hpa : (2 : ℝ) ^ ε ≤ (p : ℝ) ^ ε :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp2) hε.le
    by_cases h : (p : ℝ) ^ ε < 2
    · simp only [h, ↓reduceIte]
      have h1 := hC0e (n.factorization p)
      have h2 : ((2 : ℝ) ^ ε) ^ n.factorization p ≤ ((p : ℝ) ^ ε) ^ n.factorization p :=
        pow_le_pow_left₀ (le_trans zero_le_one ha.le) hpa _
      simpa using h1.trans (mul_le_mul_of_nonneg_left h2 (le_trans zero_le_one hC0))
    · simp only [h, ↓reduceIte, one_mul]
      have h2 : (2 : ℝ) ^ n.factorization p ≤ ((p : ℝ) ^ ε) ^ n.factorization p :=
        pow_le_pow_left₀ (by norm_num) (le_of_not_gt h) _
      simpa using (succ_le_two_pow (n.factorization p)).trans h2
  have h1 : (n.divisors.card : ℝ) ≤
      ∏ p ∈ n.primeFactors,
        ((if (p : ℝ) ^ ε < 2 then C0 else 1) * ((p : ℝ) ^ ε) ^ n.factorization p) := by
    rw [hcard]
    exact Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg _) hper
  have h2 : ∏ p ∈ n.primeFactors, (if (p : ℝ) ^ ε < 2 then C0 else 1) ≤ C0 ^ P := by
    rw [← Finset.prod_filter, Finset.prod_const]
    refine pow_le_pow_right₀ hC0 ?_
    have hsub : n.primeFactors.filter (fun p : ℕ => (p : ℝ) ^ ε < 2) ⊆ Finset.range P := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_range]
      have hlt : (p : ℝ) < (2 : ℝ) ^ (ε⁻¹) :=
        (Real.lt_rpow_inv_iff_of_pos (Nat.cast_nonneg p) (by norm_num : (0 : ℝ) ≤ 2) hε).mpr hp.2
      exact Nat.lt_ceil.mpr hlt
    exact (Finset.card_le_card hsub).trans (le_of_eq (Finset.card_range P))
  have h3 : ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p = (n : ℝ) ^ ε := by
    have hcongr : ∀ p ∈ n.primeFactors,
        ((p : ℝ) ^ ε) ^ n.factorization p = ((p : ℝ) ^ n.factorization p) ^ ε := by
      intro p hp
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      rw [← Real.rpow_natCast ((p : ℝ) ^ ε) (n.factorization p),
        ← Real.rpow_mul hp0 ε (n.factorization p : ℝ),
        ← Real.rpow_natCast (p : ℝ) (n.factorization p),
        ← Real.rpow_mul hp0 (n.factorization p : ℝ) ε, mul_comm]
    rw [Finset.prod_congr rfl hcongr, Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    have hnprod : ∏ p ∈ n.primeFactors, (p : ℝ) ^ n.factorization p = (n : ℝ) := by
      exact_mod_cast Nat.prod_factorization_pow_eq_self hn
    rw [hnprod]
  rw [Finset.prod_mul_distrib, h3] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right h2 ?_)
  exact Real.rpow_nonneg (Nat.cast_nonneg n) ε


noncomputable def differencePolynomial (P : Polynomial ℤ) (h u : ℤ) : Polynomial ℤ :=
  P.taylor h - P - Polynomial.C u

theorem differencePolynomial_ne_zero (P : Polynomial ℤ) (h u : ℤ)
    (hdegree : 2 ≤ P.natDegree) (hh : h ≠ 0) :
    differencePolynomial P h u ≠ 0 := by
  let k := P.natDegree - 1
  let H := P.hasseDeriv k
  have hk0 : k ≠ 0 := by dsimp [k]; omega
  have h1k : 1 + k = P.natDegree := by dsimp [k]; omega
  have hHdeg : H.natDegree ≤ 1 := by
    apply (Polynomial.natDegree_hasseDeriv_le P k).trans
    dsimp [k]
    omega
  have hH_eval : H.eval h = H.coeff 1 * h + H.coeff 0 := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hHdeg]
    simp
  have hP0 : P ≠ 0 := by
    intro he
    simp [he] at hdegree
  have hH1 : H.coeff 1 ≠ 0 := by
    change (P.hasseDeriv k).coeff 1 ≠ 0
    rw [Polynomial.hasseDeriv_coeff, h1k, Polynomial.coeff_natDegree]
    apply mul_ne_zero
    · exact_mod_cast (Nat.choose_pos (show k ≤ P.natDegree by dsimp [k]; omega)).ne'
    · exact Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hH0 : H.coeff 0 = P.coeff k := by
    change (P.hasseDeriv k).coeff 0 = P.coeff k
    rw [Polynomial.hasseDeriv_coeff]
    simp
  have hC : ((Polynomial.C u : Polynomial ℤ).coeff k) = 0 := by
    exact Polynomial.coeff_C_of_ne_zero hk0
  have hq : (differencePolynomial P h u).coeff k = H.coeff 1 * h := by
    simp only [differencePolynomial, Polynomial.coeff_sub, Polynomial.taylor_coeff, hC]
    change H.eval h - P.coeff k - 0 = H.coeff 1 * h
    rw [hH_eval, hH0]
    ring
  intro he
  rw [he, Polynomial.coeff_zero] at hq
  exact (mul_ne_zero hH1 hh) hq.symm

theorem differencePolynomial_natDegree_le (P : Polynomial ℤ) (h u : ℤ) :
    (differencePolynomial P h u).natDegree ≤ P.natDegree := by
  unfold differencePolynomial
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  · simp

theorem differencePolynomial_eval (P : Polynomial ℤ) (h u x : ℤ) :
    (differencePolynomial P h u).eval x = P.eval (x+h) - P.eval x - u := by
  simp [differencePolynomial, Polynomial.taylor_apply, Polynomial.eval_comp]

def differencePairs (P : Polynomial ℤ) (A : Finset ℤ) (u : ℤ) : Finset (ℤ × ℤ) :=
  (A.product A).filter fun v => P.eval v.2 - P.eval v.1 = u

private def signedDivisors (u : ℤ) : Finset ℤ :=
  (u.natAbs.divisors.image fun d : ℕ => (d : ℤ)) ∪
    (u.natAbs.divisors.image fun d : ℕ => -(d : ℤ))

private theorem signedDivisors_card (u : ℤ) :
    (signedDivisors u).card ≤ 2 * u.natAbs.divisors.card := by
  unfold signedDivisors
  rw [two_mul]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

private theorem signedDivisors_mem {u h : ℤ} (hu : u ≠ 0) (hd : h ∣ u) :
    h ∈ signedDivisors u := by
  have habs : u.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hu
  have hh : h.natAbs ∈ u.natAbs.divisors :=
    Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hd, habs⟩
  unfold signedDivisors
  by_cases hn : 0 ≤ h
  · exact mem_union_left _ (mem_image.mpr ⟨h.natAbs, hh, Int.natAbs_of_nonneg hn⟩)
  · exact mem_union_right _ (mem_image.mpr ⟨h.natAbs, hh,
      (Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hn)).symm⟩)

private theorem signedDivisors_ne_zero {u h : ℤ} (hh : h ∈ signedDivisors u) : h ≠ 0 := by
  have hpos {n : ℕ} (hn : n ∈ u.natAbs.divisors) : 0 < n := Nat.pos_of_mem_divisors hn
  unfold signedDivisors at hh
  rcases mem_union.mp hh with hh | hh
  · obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
    exact Int.ofNat_ne_zero.mpr (hpos hn).ne'
  · obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
    exact neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr (hpos hn).ne')


/-! ### The counting argument -/

noncomputable section

section Counting


def psum (P : Polynomial ℤ) (A : Finset ℕ) (f : Fin 3 → ↥A) : ℤ :=
  ∑ i : Fin 3, Polynomial.eval ((f i : ℕ) : ℤ) P

def nsum (A : Finset ℕ) (f : Fin 3 → ↥A) : ℕ := ∑ i : Fin 3, (f i : ℕ)

def Good (P : Polynomial ℤ) (A : Finset ℕ) (z : (Fin 3 → ↥A) × (Fin 3 → ↥A)) : Prop :=
  psum P A z.1 = psum P A z.2 ∧ nsum A z.1 = nsum A z.2

def key (A : Finset ℕ) (z : (Fin 3 → ↥A) × (Fin 3 → ↥A)) : ↥A × ↥A × ↥A :=
  (z.1 0, z.2 0, z.1 1)

def kc1 (P : Polynomial ℤ) (A : Finset ℕ) (k : ↥A × ↥A × ↥A) : ℤ :=
  ((k.2.1 : ℕ) : ℤ) - ((k.1 : ℕ) : ℤ) - ((k.2.2 : ℕ) : ℤ)

def kc2 (P : Polynomial ℤ) (A : Finset ℕ) (k : ↥A × ↥A × ↥A) : ℤ :=
  P.eval ((k.2.1 : ℕ) : ℤ) - P.eval ((k.1 : ℕ) : ℤ) - P.eval ((k.2.2 : ℕ) : ℤ)

def kN (P : Polynomial ℤ) (A : Finset ℕ) (k : ↥A × ↥A × ↥A) : ℤ :=
  P.eval (-kc1 P A k) + kc2 P A k

def delta (P : Polynomial ℤ) (A : Finset ℕ) (z : (Fin 3 → ↥A) × (Fin 3 → ↥A)) : ℤ :=
  kc1 P A (key A z) + ((z.2 2 : ℕ) : ℤ)

lemma psum_three (P : Polynomial ℤ) (A : Finset ℕ) (f : Fin 3 → ↥A) :
    psum P A f = P.eval ((f 0 : ℕ) : ℤ) + P.eval ((f 1 : ℕ) : ℤ) + P.eval ((f 2 : ℕ) : ℤ) := by
  simp [psum, Fin.sum_univ_three]

lemma nsum_three (A : Finset ℕ) (f : Fin 3 → ↥A) :
    nsum A f = (f 0 : ℕ) + (f 1 : ℕ) + (f 2 : ℕ) := by
  simp [nsum, Fin.sum_univ_three]

lemma funext3 {A : Finset ℕ} {f g : Fin 3 → ↥A} (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (h2 : f 2 = g 2) : f = g := by
  funext i
  have h : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  rcases h i with rfl | rfl | rfl <;> assumption

lemma coord_two (P : Polynomial ℤ) (A : Finset ℕ) {z : (Fin 3 → ↥A) × (Fin 3 → ↥A)}
    (hz : Good P A z) :
    ((z.1 2 : ℕ) : ℤ) = ((z.2 1 : ℕ) : ℤ) + delta P A z := by
  have h := hz.2
  rw [nsum_three, nsum_three] at h
  have h' : ((z.1 0 : ℕ) : ℤ) + ((z.1 1 : ℕ) : ℤ) + ((z.1 2 : ℕ) : ℤ)
      = ((z.2 0 : ℕ) : ℤ) + ((z.2 1 : ℕ) : ℤ) + ((z.2 2 : ℕ) : ℤ) := by exact_mod_cast h
  simp only [delta, key, kc1]
  linarith

lemma eval_rel (P : Polynomial ℤ) (A : Finset ℕ) {z : (Fin 3 → ↥A) × (Fin 3 → ↥A)}
    (hz : Good P A z) :
    P.eval ((z.1 2 : ℕ) : ℤ) - P.eval ((z.2 1 : ℕ) : ℤ)
      = P.eval ((z.2 2 : ℕ) : ℤ) + kc2 P A (key A z) := by
  have h := hz.1
  rw [psum_three, psum_three] at h
  simp only [key, kc2] at h ⊢
  linarith

lemma delta_dvd (P : Polynomial ℤ) (A : Finset ℕ) {z : (Fin 3 → ↥A) × (Fin 3 → ↥A)}
    (hz : Good P A z) : delta P A z ∣ kN P A (key A z) := by
  have h1 : delta P A z ∣ P.eval ((z.1 2 : ℕ) : ℤ) - P.eval ((z.2 1 : ℕ) : ℤ) := by
    have hsub : ((z.1 2 : ℕ) : ℤ) - ((z.2 1 : ℕ) : ℤ) = delta P A z := by
      linarith [coord_two P A hz]
    exact hsub ▸ Polynomial.sub_dvd_eval_sub _ _ P
  rw [eval_rel P A hz] at h1
  have h2 : delta P A z ∣ P.eval ((z.2 2 : ℕ) : ℤ) - P.eval (-kc1 P A (key A z)) := by
    have hsub : ((z.2 2 : ℕ) : ℤ) - (-kc1 P A (key A z)) = delta P A z := by
      simp only [delta]; ring
    exact hsub ▸ Polynomial.sub_dvd_eval_sub _ _ P
  have h3 := dvd_sub h1 h2
  have h4 : (P.eval ((z.2 2 : ℕ) : ℤ) + kc2 P A (key A z))
      - (P.eval ((z.2 2 : ℕ) : ℤ) - P.eval (-kc1 P A (key A z))) = kN P A (key A z) := by
    simp only [kN]; ring
  rwa [h4] at h3

lemma eval_diff_zero (P : Polynomial ℤ) (A : Finset ℕ) {z : (Fin 3 → ↥A) × (Fin 3 → ↥A)}
    (hz : Good P A z) :
    (differencePolynomial P (delta P A z)
      (P.eval (delta P A z - kc1 P A (key A z)) + kc2 P A (key A z))).eval ((z.2 1 : ℕ) : ℤ) = 0 := by
  rw [differencePolynomial_eval]
  have h1 := coord_two P A hz
  have h2 : delta P A z - kc1 P A (key A z) = ((z.2 2 : ℕ) : ℤ) := by simp only [delta]; ring
  have h4 : ((z.2 1 : ℕ) : ℤ) + delta P A z = ((z.1 2 : ℕ) : ℤ) := by linarith
  rw [h2, h4]
  have h3 := eval_rel P A hz
  linarith

lemma eval_diff_zero' (P : Polynomial ℤ) (A : Finset ℕ) {z : (Fin 3 → ↥A) × (Fin 3 → ↥A)}
    (hz : Good P A z) :
    (differencePolynomial P (kc1 P A (key A z) + ((z.2 2 : ℕ) : ℤ))
      (P.eval ((z.2 2 : ℕ) : ℤ) + kc2 P A (key A z))).eval ((z.2 1 : ℕ) : ℤ) = 0 := by
  rw [differencePolynomial_eval]
  have h1 := coord_two P A hz
  have h4 : ((z.2 1 : ℕ) : ℤ) + (kc1 P A (key A z) + ((z.2 2 : ℕ) : ℤ)) = ((z.1 2 : ℕ) : ℤ) := by
    simp only [delta] at h1; linarith
  rw [h4]
  have h3 := eval_rel P A hz
  linarith

/-! #### Nondegenerate keys -/

def RootSet1 (P : Polynomial ℤ) (A : Finset ℕ) (k : ↥A × ↥A × ↥A) (δ : ℤ) : Finset ℤ :=
  (differencePolynomial P δ (P.eval (δ - kc1 P A k) + kc2 P A k)).roots.toFinset

def T1 (P : Polynomial ℤ) (A : Finset ℕ) : Finset ((Fin 3 → ↥A) × (Fin 3 → ↥A)) :=
  univ.filter (fun z => Good P A z ∧ kN P A (key A z) ≠ 0)

def Target1 (P : Polynomial ℤ) (A : Finset ℕ) : Finset (Σ k : ↥A × ↥A × ↥A, Σ _ : ℤ, ℤ) :=
  univ.sigma (fun k => (signedDivisors (kN P A k)).sigma (fun δ => RootSet1 P A k δ))

def f1 (P : Polynomial ℤ) (A : Finset ℕ) (z : (Fin 3 → ↥A) × (Fin 3 → ↥A)) :
    Σ k : ↥A × ↥A × ↥A, Σ _ : ℤ, ℤ :=
  ⟨key A z, ⟨delta P A z, ((z.2 1 : ℕ) : ℤ)⟩⟩

lemma mem_RootSet1 (P : Polynomial ℤ) (A : Finset ℕ) (hdeg : 2 ≤ P.natDegree)
    {z : (Fin 3 → ↥A) × (Fin 3 → ↥A)} (hz : Good P A z) (hN : kN P A (key A z) ≠ 0) :
    ((z.2 1 : ℕ) : ℤ) ∈ RootSet1 P A (key A z) (delta P A z) := by
  have hne0 : delta P A z ≠ 0 := by
    intro h
    apply hN
    have hd := delta_dvd P A hz
    rw [h] at hd
    simpa using hd
  have hne : differencePolynomial P (delta P A z)
      (P.eval (delta P A z - kc1 P A (key A z)) + kc2 P A (key A z)) ≠ 0 :=
    differencePolynomial_ne_zero P _ _ hdeg hne0
  exact Multiset.mem_toFinset.mpr
    ((Polynomial.mem_roots hne).mpr (eval_diff_zero P A hz))

theorem card_T1 (P : Polynomial ℤ) (A : Finset ℕ) (hdeg : 2 ≤ P.natDegree) :
    (T1 P A).card ≤ 2 * P.natDegree *
      ∑ k : ↥A × ↥A × ↥A, (kN P A k).natAbs.divisors.card := by
  have hmaps : ∀ z ∈ T1 P A, f1 P A z ∈ Target1 P A := by
    intro z hz
    obtain ⟨-, hG, hN⟩ := mem_filter.mp hz
    refine mem_sigma.mpr ⟨mem_univ _, mem_sigma.mpr ⟨?_, ?_⟩⟩
    · exact signedDivisors_mem hN (delta_dvd P A hG)
    · exact mem_RootSet1 P A hdeg hG hN
  have hinj : Set.InjOn (f1 P A) (T1 P A : Set _) := by
    intro z hz z' hz' h
    obtain ⟨-, hG, -⟩ := mem_filter.mp hz
    obtain ⟨-, hG', -⟩ := mem_filter.mp hz'
    have hk : key A z = key A z' := congrArg (fun s => s.1) h
    have hδ : delta P A z = delta P A z' := congrArg (fun s => s.2.1) h
    have hy1 : ((z.2 1 : ℕ) : ℤ) = ((z'.2 1 : ℕ) : ℤ) := congrArg (fun s => s.2.2) h
    have ha : z.1 0 = z'.1 0 := congrArg (fun k => k.1) hk
    have hb : z.2 0 = z'.2 0 := congrArg (fun k => k.2.1) hk
    have hc : z.1 1 = z'.1 1 := congrArg (fun k => k.2.2) hk
    have hy2 : ((z.2 2 : ℕ) : ℤ) = ((z'.2 2 : ℕ) : ℤ) := by
      simp only [delta] at hδ
      rw [hk] at hδ
      linarith
    have hx2 : ((z.1 2 : ℕ) : ℤ) = ((z'.1 2 : ℕ) : ℤ) := by
      rw [coord_two P A hG, coord_two P A hG', hδ, hy1]
    exact Prod.ext (funext3 ha hc (Subtype.ext (Nat.cast_injective hx2)))
      (funext3 hb (Subtype.ext (Nat.cast_injective hy1)) (Subtype.ext (Nat.cast_injective hy2)))
  calc (T1 P A).card ≤ (Target1 P A).card := card_le_card_of_injOn _ hmaps hinj
    _ = ∑ k ∈ (univ : Finset (↥A × ↥A × ↥A)),
          ((signedDivisors (kN P A k)).sigma (fun δ => RootSet1 P A k δ)).card := card_sigma _ _
    _ ≤ ∑ k ∈ (univ : Finset (↥A × ↥A × ↥A)),
          2 * (kN P A k).natAbs.divisors.card * P.natDegree := by
        refine sum_le_sum fun k _ => ?_
        calc ((signedDivisors (kN P A k)).sigma (fun δ => RootSet1 P A k δ)).card
            = ∑ δ ∈ signedDivisors (kN P A k), (RootSet1 P A k δ).card := card_sigma _ _
          _ ≤ ∑ _δ ∈ signedDivisors (kN P A k), P.natDegree := by
              refine sum_le_sum fun δ _ => ?_
              exact (Multiset.toFinset_card_le _).trans
                ((Polynomial.card_roots' _).trans (differencePolynomial_natDegree_le P δ _))
          _ = (signedDivisors (kN P A k)).card * P.natDegree := by simp
          _ ≤ 2 * (kN P A k).natAbs.divisors.card * P.natDegree := by
              exact Nat.mul_le_mul_right _ (signedDivisors_card _)
    _ = 2 * P.natDegree * ∑ k : ↥A × ↥A × ↥A, (kN P A k).natAbs.divisors.card := by
        rw [Finset.mul_sum]
        exact sum_congr rfl fun k _ => by ring

/-! #### Degenerate keys -/

def T2 (P : Polynomial ℤ) (A : Finset ℕ) : Finset ((Fin 3 → ↥A) × (Fin 3 → ↥A)) :=
  univ.filter (fun z => Good P A z ∧ kN P A (key A z) = 0)

def T2a (P : Polynomial ℤ) (A : Finset ℕ) : Finset ((Fin 3 → ↥A) × (Fin 3 → ↥A)) :=
  (T2 P A).filter (fun z => delta P A z = 0)

def T2b (P : Polynomial ℤ) (A : Finset ℕ) : Finset ((Fin 3 → ↥A) × (Fin 3 → ↥A)) :=
  (T2 P A).filter (fun z => delta P A z ≠ 0)

def DegSet (P : Polynomial ℤ) (A : Finset ℕ) : Finset (↥A × ↥A × ↥A) :=
  univ.filter (fun k => kN P A k = 0)

def RootSet2 (P : Polynomial ℤ) (A : Finset ℕ) (k : ↥A × ↥A × ↥A) (y : ↥A) : Finset ℤ :=
  if kc1 P A k + ((y : ℕ) : ℤ) = 0 then ∅
  else (differencePolynomial P (kc1 P A k + ((y : ℕ) : ℤ))
    (P.eval ((y : ℕ) : ℤ) + kc2 P A k)).roots.toFinset

lemma card_RootSet2 (P : Polynomial ℤ) (A : Finset ℕ) (k : ↥A × ↥A × ↥A) (y : ↥A) :
    (RootSet2 P A k y).card ≤ P.natDegree := by
  unfold RootSet2
  split_ifs
  · simp
  · exact (Multiset.toFinset_card_le _).trans
      ((Polynomial.card_roots' _).trans (differencePolynomial_natDegree_le P _ _))

def RootSet3 (P : Polynomial ℤ) (A : Finset ℕ) (p : ↥A × ↥A) : Finset ℤ :=
  (differencePolynomial P (((p.1 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ))
    (P.eval ((p.1 : ℕ) : ℤ) - P.eval ((p.2 : ℕ) : ℤ))).roots.toFinset

theorem card_DegSet (P : Polynomial ℤ) (A : Finset ℕ) (hdeg : 2 ≤ P.natDegree) :
    (DegSet P A).card ≤ (P.natDegree + 1) * A.card ^ 2 := by
  let D1 := (DegSet P A).filter (fun k => k.1 = k.2.1)
  let D2 := (DegSet P A).filter (fun k => k.1 ≠ k.2.1)
  have hsplit : DegSet P A ⊆ D1 ∪ D2 := by
    intro k hk
    by_cases h : k.1 = k.2.1
    · exact mem_union_left _ (mem_filter.mpr ⟨hk, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hk, h⟩)
  have hD1 : D1.card ≤ A.card ^ 2 := by
    have hmaps : ∀ k ∈ D1, (k.1, k.2.2) ∈ (univ : Finset (↥A × ↥A)) := fun _ _ => mem_univ _
    have hinj : Set.InjOn (fun k : ↥A × ↥A × ↥A => (k.1, k.2.2)) (D1 : Set _) := by
      intro k hk k' hk' h
      have h' : (k.1, k.2.2) = (k'.1, k'.2.2) := h
      have e1 : (k.1, k.2.2).1 = (k'.1, k'.2.2).1 := congrArg (fun p : ↥A × ↥A => p.1) h'
      have e2 : (k.1, k.2.2).2 = (k'.1, k'.2.2).2 := congrArg (fun p : ↥A × ↥A => p.2) h'
      have h1 : k.1 = k.2.1 := (mem_filter.mp hk).2
      have h2 : k'.1 = k'.2.1 := (mem_filter.mp hk').2
      exact Prod.ext e1 (Prod.ext (by rw [← h1, ← h2, e1]) e2)
    calc D1.card ≤ (univ : Finset (↥A × ↥A)).card := card_le_card_of_injOn _ hmaps hinj
      _ = A.card ^ 2 := by
          rw [Finset.card_univ, Fintype.card_prod, Fintype.card_coe]
          ring
  have hD2 : D2.card ≤ A.card ^ 2 * P.natDegree := by
    have hmaps : ∀ k ∈ D2, (⟨(k.1, k.2.1), ((k.2.2 : ℕ) : ℤ)⟩ : Σ p : ↥A × ↥A, ℤ) ∈
        (univ.filter (fun p : ↥A × ↥A => p.1 ≠ p.2)).sigma (RootSet3 P A) := by
      intro k hk
      have hne : k.1 ≠ k.2.1 := (mem_filter.mp hk).2
      have hN : kN P A k = 0 := (mem_filter.mp (mem_filter.mp hk).1).2
      refine mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _, hne⟩, ?_⟩
      have hroot : (differencePolynomial P (((k.1 : ℕ) : ℤ) - ((k.2.1 : ℕ) : ℤ))
          (P.eval ((k.1 : ℕ) : ℤ) - P.eval ((k.2.1 : ℕ) : ℤ))).eval ((k.2.2 : ℕ) : ℤ) = 0 := by
        rw [differencePolynomial_eval]
        have h1 : ((k.2.2 : ℕ) : ℤ) + (((k.1 : ℕ) : ℤ) - ((k.2.1 : ℕ) : ℤ)) = -kc1 P A k := by
          simp only [kc1]; ring
        rw [h1]
        simp only [kN, kc2] at hN
        linarith
      have hne' : differencePolynomial P (((k.1 : ℕ) : ℤ) - ((k.2.1 : ℕ) : ℤ))
          (P.eval ((k.1 : ℕ) : ℤ) - P.eval ((k.2.1 : ℕ) : ℤ)) ≠ 0 := by
        apply differencePolynomial_ne_zero P _ _ hdeg
        intro h
        apply hne
        have h' : ((k.1 : ℕ) : ℤ) = ((k.2.1 : ℕ) : ℤ) := by linarith
        exact Subtype.ext (Nat.cast_injective h')
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne').mpr hroot)
    have hinj : Set.InjOn (fun k : ↥A × ↥A × ↥A => (⟨(k.1, k.2.1), ((k.2.2 : ℕ) : ℤ)⟩ :
        Σ p : ↥A × ↥A, ℤ)) (D2 : Set _) := by
      intro k _ k' _ h
      have e1 : k.1 = k'.1 := congrArg (fun s => s.1.1) h
      have e2 : k.2.1 = k'.2.1 := congrArg (fun s => s.1.2) h
      have e3 : ((k.2.2 : ℕ) : ℤ) = ((k'.2.2 : ℕ) : ℤ) := congrArg (fun s => s.2) h
      exact Prod.ext e1 (Prod.ext e2 (Subtype.ext (Nat.cast_injective e3)))
    calc D2.card ≤ ((univ.filter (fun p : ↥A × ↥A => p.1 ≠ p.2)).sigma (RootSet3 P A)).card :=
          card_le_card_of_injOn _ hmaps hinj
      _ = ∑ p ∈ univ.filter (fun p : ↥A × ↥A => p.1 ≠ p.2), (RootSet3 P A p).card :=
          card_sigma _ _
      _ ≤ ∑ _p ∈ univ.filter (fun p : ↥A × ↥A => p.1 ≠ p.2), P.natDegree := by
          refine sum_le_sum fun p _ => ?_
          exact (Multiset.toFinset_card_le _).trans
            ((Polynomial.card_roots' _).trans (differencePolynomial_natDegree_le P _ _))
      _ ≤ ∑ _p ∈ (univ : Finset (↥A × ↥A)), P.natDegree :=
          sum_le_sum_of_subset (filter_subset _ _)
      _ = A.card ^ 2 * P.natDegree := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Finset.card_univ, Fintype.card_prod,
            Fintype.card_coe]
          ring
  calc (DegSet P A).card ≤ (D1 ∪ D2).card := card_le_card hsplit
    _ ≤ D1.card + D2.card := card_union_le _ _
    _ ≤ A.card ^ 2 + A.card ^ 2 * P.natDegree := Nat.add_le_add hD1 hD2
    _ = (P.natDegree + 1) * A.card ^ 2 := by ring

theorem card_T2 (P : Polynomial ℤ) (A : Finset ℕ) (hdeg : 2 ≤ P.natDegree) :
    (T2 P A).card ≤ (P.natDegree + 1) ^ 2 * A.card ^ 3 := by
  have hsplit : T2 P A ⊆ T2a P A ∪ T2b P A := by
    intro z hz
    by_cases h : delta P A z = 0
    · exact mem_union_left _ (mem_filter.mpr ⟨hz, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hz, h⟩)
  have hDeg := card_DegSet P A hdeg
  have ha : (T2a P A).card ≤ (DegSet P A).card * A.card := by
    have hmaps : ∀ z ∈ T2a P A, (⟨key A z, z.2 1⟩ : Σ _ : ↥A × ↥A × ↥A, ↥A) ∈
        (DegSet P A).sigma (fun _ => (univ : Finset ↥A)) := by
      intro z hz
      obtain ⟨hz2, -⟩ := mem_filter.mp hz
      obtain ⟨-, hG, hN⟩ := mem_filter.mp hz2
      exact mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _, hN⟩, mem_univ _⟩
    have hinj : Set.InjOn (fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) =>
        (⟨key A z, z.2 1⟩ : Σ _ : ↥A × ↥A × ↥A, ↥A)) (T2a P A : Set _) := by
      intro z hz z' hz' h
      obtain ⟨hz2, hδ0⟩ := mem_filter.mp hz
      obtain ⟨hz2', hδ0'⟩ := mem_filter.mp hz'
      obtain ⟨-, hG, -⟩ := mem_filter.mp hz2
      obtain ⟨-, hG', -⟩ := mem_filter.mp hz2'
      have hk : key A z = key A z' := congrArg (fun s => s.1) h
      have hy1 : ((z.2 1 : ℕ) : ℤ) = ((z'.2 1 : ℕ) : ℤ) := by
        exact_mod_cast congrArg (fun s => s.2) h
      have ha' : z.1 0 = z'.1 0 := congrArg (fun k => k.1) hk
      have hb' : z.2 0 = z'.2 0 := congrArg (fun k => k.2.1) hk
      have hc' : z.1 1 = z'.1 1 := congrArg (fun k => k.2.2) hk
      have hy2 : ((z.2 2 : ℕ) : ℤ) = ((z'.2 2 : ℕ) : ℤ) := by
        have e : kc1 P A (key A z) = kc1 P A (key A z') := by rw [hk]
        have h1 : kc1 P A (key A z) + ((z.2 2 : ℕ) : ℤ) = 0 := hδ0
        have h2 : kc1 P A (key A z') + ((z'.2 2 : ℕ) : ℤ) = 0 := hδ0'
        linarith
      have hx2 : ((z.1 2 : ℕ) : ℤ) = ((z'.1 2 : ℕ) : ℤ) := by
        rw [coord_two P A hG, coord_two P A hG', hδ0, hδ0', hy1]
      exact Prod.ext (funext3 ha' hc' (Subtype.ext (Nat.cast_injective hx2)))
        (funext3 hb' (Subtype.ext (Nat.cast_injective hy1)) (Subtype.ext (Nat.cast_injective hy2)))
    calc (T2a P A).card ≤ ((DegSet P A).sigma (fun _ => (univ : Finset ↥A))).card :=
          card_le_card_of_injOn _ hmaps hinj
      _ = ∑ _k ∈ DegSet P A, A.card := by
          rw [card_sigma]
          exact sum_congr rfl fun k _ => by rw [Finset.card_univ, Fintype.card_coe]
      _ = (DegSet P A).card * A.card := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  have hb : (T2b P A).card ≤ (DegSet P A).card * A.card * P.natDegree := by
    have hmaps : ∀ z ∈ T2b P A, (⟨key A z, ⟨z.2 2, ((z.2 1 : ℕ) : ℤ)⟩⟩ :
        Σ k : ↥A × ↥A × ↥A, Σ _ : ↥A, ℤ) ∈
        (DegSet P A).sigma (fun k => univ.sigma (fun y => RootSet2 P A k y)) := by
      intro z hz
      obtain ⟨hz2, hδ0⟩ := mem_filter.mp hz
      obtain ⟨-, hG, hN⟩ := mem_filter.mp hz2
      refine mem_sigma.mpr ⟨mem_filter.mpr ⟨mem_univ _, hN⟩, mem_sigma.mpr ⟨mem_univ _, ?_⟩⟩
      have hδ0' : kc1 P A (key A z) + ((z.2 2 : ℕ) : ℤ) ≠ 0 := hδ0
      unfold RootSet2
      simp only [hδ0', ↓reduceIte]
      refine Multiset.mem_toFinset.mpr ((Polynomial.mem_roots ?_).mpr (eval_diff_zero' P A hG))
      exact differencePolynomial_ne_zero P _ _ hdeg hδ0'
    have hinj : Set.InjOn (fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) =>
        (⟨key A z, ⟨z.2 2, ((z.2 1 : ℕ) : ℤ)⟩⟩ : Σ k : ↥A × ↥A × ↥A, Σ _ : ↥A, ℤ))
        (T2b P A : Set _) := by
      intro z hz z' hz' h
      obtain ⟨hz2, -⟩ := mem_filter.mp hz
      obtain ⟨hz2', -⟩ := mem_filter.mp hz'
      obtain ⟨-, hG, -⟩ := mem_filter.mp hz2
      obtain ⟨-, hG', -⟩ := mem_filter.mp hz2'
      have hk : key A z = key A z' := congrArg (fun s => s.1) h
      have hy2 : z.2 2 = z'.2 2 := congrArg (fun s => s.2.1) h
      have hy1 : ((z.2 1 : ℕ) : ℤ) = ((z'.2 1 : ℕ) : ℤ) := congrArg (fun s => s.2.2) h
      have ha' : z.1 0 = z'.1 0 := congrArg (fun k => k.1) hk
      have hb' : z.2 0 = z'.2 0 := congrArg (fun k => k.2.1) hk
      have hc' : z.1 1 = z'.1 1 := congrArg (fun k => k.2.2) hk
      have hx2 : ((z.1 2 : ℕ) : ℤ) = ((z'.1 2 : ℕ) : ℤ) := by
        rw [coord_two P A hG, coord_two P A hG']
        have e : kc1 P A (key A z) = kc1 P A (key A z') := by rw [hk]
        simp only [delta]
        rw [e, hy2, hy1]
      exact Prod.ext (funext3 ha' hc' (Subtype.ext (Nat.cast_injective hx2)))
        (funext3 hb' (Subtype.ext (Nat.cast_injective hy1)) hy2)
    calc (T2b P A).card ≤ ((DegSet P A).sigma (fun k => univ.sigma
          (fun y => RootSet2 P A k y))).card := card_le_card_of_injOn _ hmaps hinj
      _ = ∑ k ∈ DegSet P A, ∑ y ∈ (univ : Finset ↥A), (RootSet2 P A k y).card := by
          rw [card_sigma]
          exact sum_congr rfl fun k _ => card_sigma _ _
      _ ≤ ∑ k ∈ DegSet P A, ∑ _y ∈ (univ : Finset ↥A), P.natDegree := by
          refine sum_le_sum fun k _ => sum_le_sum fun y _ => card_RootSet2 P A k y
      _ = ∑ _k ∈ DegSet P A, A.card * P.natDegree := by
          refine sum_congr rfl fun k _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Finset.card_univ, Fintype.card_coe]
      _ = (DegSet P A).card * A.card * P.natDegree := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
          ring
  calc (T2 P A).card ≤ (T2a P A ∪ T2b P A).card := card_le_card hsplit
    _ ≤ (T2a P A).card + (T2b P A).card := card_union_le _ _
    _ ≤ (DegSet P A).card * A.card + (DegSet P A).card * A.card * P.natDegree :=
        Nat.add_le_add ha hb
    _ = (DegSet P A).card * A.card * (P.natDegree + 1) := by ring
    _ ≤ ((P.natDegree + 1) * A.card ^ 2) * A.card * (P.natDegree + 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hDeg)
    _ = (P.natDegree + 1) ^ 2 * A.card ^ 3 := by ring

theorem card_good (P : Polynomial ℤ) (A : Finset ℕ) (hdeg : 2 ≤ P.natDegree) :
    (univ.filter (fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) => Good P A z)).card ≤
      2 * P.natDegree * (∑ k : ↥A × ↥A × ↥A, (kN P A k).natAbs.divisors.card) +
        (P.natDegree + 1) ^ 2 * A.card ^ 3 := by
  have hsub : univ.filter (fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) => Good P A z) ⊆
      T1 P A ∪ T2 P A := by
    intro z hz
    have hG := (mem_filter.mp hz).2
    by_cases h : kN P A (key A z) = 0
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hG, h⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hG, h⟩)
  calc (univ.filter (fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) => Good P A z)).card
      ≤ (T1 P A ∪ T2 P A).card := card_le_card hsub
    _ ≤ (T1 P A).card + (T2 P A).card := card_union_le _ _
    _ ≤ 2 * P.natDegree * (∑ k : ↥A × ↥A × ↥A, (kN P A k).natAbs.divisors.card) +
          (P.natDegree + 1) ^ 2 * A.card ^ 3 :=
        Nat.add_le_add (card_T1 P A hdeg) (card_T2 P A hdeg)

end Counting

end

/-! ### Real-valued estimates -/

lemma abs_eval_le (P : Polynomial ℤ) (n : ℤ) (B : ℝ) (hB : 1 ≤ B) (hn : |(n : ℝ)| ≤ B) :
    |((P.eval n : ℤ) : ℝ)| ≤ (∑ j ∈ Finset.range (P.natDegree + 1), |(P.coeff j : ℝ)|) * B ^ P.natDegree := by
  have h1 : ((P.eval n : ℤ) : ℝ) = ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℝ) * (n : ℝ) ^ j := by
    rw [Polynomial.eval_eq_sum_range, Int.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [h1]
  calc |∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℝ) * (n : ℝ) ^ j|
      ≤ ∑ j ∈ Finset.range (P.natDegree + 1), |(P.coeff j : ℝ) * (n : ℝ) ^ j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ Finset.range (P.natDegree + 1), |(P.coeff j : ℝ)| * |(n : ℝ)| ^ j := by
        refine Finset.sum_congr rfl fun j _ => by rw [abs_mul, abs_pow]
    _ ≤ ∑ j ∈ Finset.range (P.natDegree + 1), |(P.coeff j : ℝ)| * B ^ P.natDegree := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : j ≤ P.natDegree := by rw [Finset.mem_range] at hj; omega
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc |(n : ℝ)| ^ j ≤ B ^ j := pow_le_pow_left₀ (abs_nonneg _) hn j
          _ ≤ B ^ P.natDegree := pow_le_pow_right₀ hB hj'
    _ = (∑ j ∈ Finset.range (P.natDegree + 1), |(P.coeff j : ℝ)|) * B ^ P.natDegree := by
        rw [← Finset.sum_mul]

lemma abs_add_sub3 (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
  rw [sub_eq_add_neg]
  have h1 := abs_add_le (a + b) (-c)
  have h2 := abs_add_le a b
  rw [abs_neg] at h1
  linarith

lemma abs_add_sub4 (a b c d : ℝ) : |a + b - c - d| ≤ |a| + |b| + |c| + |d| := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  have h1 := abs_add_le (a + b + -c) (-d)
  have h2 := abs_add_le (a + b) (-c)
  have h3 := abs_add_le a b
  rw [abs_neg] at h1 h2
  linarith

theorem tau_bound (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (x3 : ℝ) (hx3 : 0 < x3) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (M : ℕ), 2 ≤ M → ∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 M →
      ∀ k : ↥A × ↥A × ↥A, (((kN P A k).natAbs.divisors.card : ℕ) : ℝ) ≤ Cc * (M : ℝ) ^ x3 := by
  have hd : (0 : ℝ) < (P.natDegree : ℝ) := by exact_mod_cast (by omega : 0 < P.natDegree)
  let ε' := x3 / (P.natDegree : ℝ)
  have hε' : 0 < ε' := div_pos hx3 hd
  obtain ⟨C, hC, hτ⟩ := divisor_bound ε' hε'
  let K := ∑ j ∈ Finset.range (P.natDegree + 1), |(P.coeff j : ℝ)|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hdexp : (P.natDegree : ℝ) * ε' = x3 := by
    dsimp [ε']
    exact mul_div_cancel₀ x3 hd.ne'
  refine ⟨C * (4 * K) ^ ε' * (3 : ℝ) ^ x3, ?_, ?_⟩
  · exact mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg (by norm_num) _)
  intro M hM A hA k
  have hmem : ∀ y : ↥A, 1 ≤ (y : ℕ) ∧ (y : ℕ) ≤ M := by
    intro y; simpa using hA y.2
  have hcomp : ∀ y : ↥A, |((y : ℕ) : ℝ)| ≤ (M : ℝ) := by
    intro y
    obtain ⟨h1, h2⟩ := hmem y
    have h1' : (1 : ℝ) ≤ ((y : ℕ) : ℝ) := by exact_mod_cast h1
    have h2' : ((y : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast h2
    rw [abs_of_pos (by linarith)]
    exact h2'
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hB : (1 : ℝ) ≤ 3 * (M : ℝ) := by linarith
  have hc1 : |(-kc1 P A k : ℝ)| ≤ 3 * (M : ℝ) := by
    have e : (-kc1 P A k : ℝ) = ((k.1 : ℕ) : ℝ) + ((k.2.2 : ℕ) : ℝ) - ((k.2.1 : ℕ) : ℝ) := by
      simp only [kc1]; push_cast; ring
    rw [e]
    have h := abs_add_sub3 (((k.1 : ℕ) : ℝ)) (((k.2.2 : ℕ) : ℝ)) (((k.2.1 : ℕ) : ℝ))
    have h1 := hcomp k.1
    have h2 := hcomp k.2.1
    have h3 := hcomp k.2.2
    linarith
  have hev : ∀ n : ℤ, |(n : ℝ)| ≤ 3 * (M : ℝ) →
      |((P.eval n : ℤ) : ℝ)| ≤ K * (3 * (M : ℝ)) ^ P.natDegree := fun n hn => abs_eval_le P n _ hB hn
  have hN : |(kN P A k : ℝ)| ≤ 4 * K * (3 * (M : ℝ)) ^ P.natDegree := by
    have e : (kN P A k : ℝ) = ((P.eval (-kc1 P A k) : ℤ) : ℝ) + ((P.eval ((k.2.1 : ℕ) : ℤ) : ℤ) : ℝ)
        - ((P.eval ((k.1 : ℕ) : ℤ) : ℤ) : ℝ) - ((P.eval ((k.2.2 : ℕ) : ℤ) : ℤ) : ℝ) := by
      simp only [kN, kc2]; push_cast; ring
    rw [e]
    have h := abs_add_sub4 ((P.eval (-kc1 P A k) : ℤ) : ℝ) ((P.eval ((k.2.1 : ℕ) : ℤ) : ℤ) : ℝ)
      ((P.eval ((k.1 : ℕ) : ℤ) : ℤ) : ℝ) ((P.eval ((k.2.2 : ℕ) : ℤ) : ℤ) : ℝ)
    have hM3 : (M : ℝ) ≤ 3 * (M : ℝ) := by linarith
    have h1 := hev (-kc1 P A k) hc1
    have h2 := hev ((k.2.1 : ℕ) : ℤ) (le_trans (hcomp k.2.1) hM3)
    have h3 := hev ((k.1 : ℕ) : ℤ) (le_trans (hcomp k.1) hM3)
    have h4 := hev ((k.2.2 : ℕ) : ℤ) (le_trans (hcomp k.2.2) hM3)
    linarith
  have hnat : (((kN P A k).natAbs : ℕ) : ℝ) ≤ 4 * K * (3 * (M : ℝ)) ^ P.natDegree := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    exact hN
  calc (((kN P A k).natAbs.divisors.card : ℕ) : ℝ)
      ≤ C * (((kN P A k).natAbs : ℕ) : ℝ) ^ ε' := hτ _
    _ ≤ C * (4 * K * (3 * (M : ℝ)) ^ P.natDegree) ^ ε' := by
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        exact Real.rpow_le_rpow (Nat.cast_nonneg _) hnat hε'.le
    _ = C * ((4 * K) ^ ε' * (3 : ℝ) ^ x3 * (M : ℝ) ^ x3) := by
        have key : (4 * K * (3 * (M : ℝ)) ^ P.natDegree) ^ ε'
            = (4 * K) ^ ε' * (3 : ℝ) ^ x3 * (M : ℝ) ^ x3 := by
          have h4K : (0 : ℝ) ≤ 4 * K := by linarith
          have h3d : (0 : ℝ) ≤ (3 : ℝ) ^ P.natDegree := by positivity
          have hMd : (0 : ℝ) ≤ (M : ℝ) ^ P.natDegree := by positivity
          have e1 : 4 * K * (3 * (M : ℝ)) ^ P.natDegree
              = (4 * K) * ((3 : ℝ) ^ P.natDegree * (M : ℝ) ^ P.natDegree) := by ring
          rw [e1, Real.mul_rpow h4K (mul_nonneg h3d hMd), Real.mul_rpow h3d hMd]
          have hd3 : ((3 : ℝ) ^ P.natDegree) ^ ε' = (3 : ℝ) ^ x3 := by
            rw [← Real.rpow_natCast (3 : ℝ) P.natDegree, ← Real.rpow_mul (by norm_num), hdexp]
          have hdM : ((M : ℝ) ^ P.natDegree) ^ ε' = (M : ℝ) ^ x3 := by
            rw [← Real.rpow_natCast (M : ℝ) P.natDegree, ← Real.rpow_mul (by positivity), hdexp]
          rw [hd3, hdM]
          ring
        rw [key]
    _ = (C * (4 * K) ^ ε' * (3 : ℝ) ^ x3) * (M : ℝ) ^ x3 := by ring

theorem main (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (x3 : ℝ) (hx3 : 0 < x3) :
    ∃ x5 : ℝ, 0 < x5 ∧ ∀ (M : ℕ), 2 ≤ M → ∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 M →
      ((univ.filter (fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) =>
        psum P A z.1 = psum P A z.2 ∧ nsum A z.1 = nsum A z.2 ∧
          (∑ i : Fin 3, (z.1 i : ℕ) ^ 2) ≠ ∑ i : Fin 3, (z.2 i : ℕ) ^ 2)).card : ℝ)
        ≤ x5 * (M : ℝ) ^ x3 * (A.card : ℝ) ^ 3 := by
  obtain ⟨Cc, hCc, hτ⟩ := tau_bound P hdeg x3 hx3
  refine ⟨2 * (P.natDegree : ℝ) * Cc + ((P.natDegree : ℝ) + 1) ^ 2, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 2 * (P.natDegree : ℝ) * Cc :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hCc
    have h2 : (0 : ℝ) < ((P.natDegree : ℝ) + 1) ^ 2 := by positivity
    linarith
  intro M hM A hA
  have hsub : univ.filter (fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) =>
        psum P A z.1 = psum P A z.2 ∧ nsum A z.1 = nsum A z.2 ∧
          (∑ i : Fin 3, (z.1 i : ℕ) ^ 2) ≠ ∑ i : Fin 3, (z.2 i : ℕ) ^ 2) ⊆
      univ.filter (fun z => Good P A z) := by
    intro z hz
    have hz' := (mem_filter.mp hz).2
    exact mem_filter.mpr ⟨mem_univ _, hz'.1, hz'.2.1⟩
  have hcard := card_good P A hdeg
  have h1 : ((univ.filter (fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) => Good P A z)).card : ℝ) ≤
      2 * (P.natDegree : ℝ) * (∑ k : ↥A × ↥A × ↥A, ((kN P A k).natAbs.divisors.card : ℝ)) +
        ((P.natDegree : ℝ) + 1) ^ 2 * (A.card : ℝ) ^ 3 := by
    calc ((univ.filter (fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) => Good P A z)).card : ℝ)
        ≤ ((2 * P.natDegree * (∑ k : ↥A × ↥A × ↥A, (kN P A k).natAbs.divisors.card) +
            (P.natDegree + 1) ^ 2 * A.card ^ 3 : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = 2 * (P.natDegree : ℝ) * (∑ k : ↥A × ↥A × ↥A, ((kN P A k).natAbs.divisors.card : ℝ)) +
          ((P.natDegree : ℝ) + 1) ^ 2 * (A.card : ℝ) ^ 3 := by
          push_cast
          ring_nf
  have hsum : (∑ k : ↥A × ↥A × ↥A, ((kN P A k).natAbs.divisors.card : ℝ)) ≤
      (A.card : ℝ) ^ 3 * Cc * (M : ℝ) ^ x3 := by
    calc (∑ k : ↥A × ↥A × ↥A, ((kN P A k).natAbs.divisors.card : ℝ))
        ≤ ∑ k : ↥A × ↥A × ↥A, Cc * (M : ℝ) ^ x3 := sum_le_sum fun k _ => hτ M hM A hA k
      _ = (A.card : ℝ) ^ 3 * Cc * (M : ℝ) ^ x3 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_coe,
            nsmul_eq_mul]
          push_cast
          ring
  have hM1 : (1 : ℝ) ≤ (M : ℝ) ^ x3 := by
    refine Real.one_le_rpow ?_ hx3.le
    exact_mod_cast (show 1 ≤ M by omega)
  calc ((univ.filter (fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) =>
        psum P A z.1 = psum P A z.2 ∧ nsum A z.1 = nsum A z.2 ∧
          (∑ i : Fin 3, (z.1 i : ℕ) ^ 2) ≠ ∑ i : Fin 3, (z.2 i : ℕ) ^ 2)).card : ℝ)
      ≤ ((univ.filter (fun z : (Fin 3 → ↥A) × (Fin 3 → ↥A) => Good P A z)).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ 2 * (P.natDegree : ℝ) * (∑ k : ↥A × ↥A × ↥A, ((kN P A k).natAbs.divisors.card : ℝ)) +
          ((P.natDegree : ℝ) + 1) ^ 2 * (A.card : ℝ) ^ 3 := h1
    _ ≤ 2 * (P.natDegree : ℝ) * ((A.card : ℝ) ^ 3 * Cc * (M : ℝ) ^ x3) +
          ((P.natDegree : ℝ) + 1) ^ 2 * (A.card : ℝ) ^ 3 * (M : ℝ) ^ x3 := by
        have ha : 2 * (P.natDegree : ℝ) *
            (∑ k : ↥A × ↥A × ↥A, ((kN P A k).natAbs.divisors.card : ℝ)) ≤
            2 * (P.natDegree : ℝ) * ((A.card : ℝ) ^ 3 * Cc * (M : ℝ) ^ x3) :=
          mul_le_mul_of_nonneg_left hsum
            (mul_nonneg (by norm_num) (Nat.cast_nonneg P.natDegree))
        have hnn : (0 : ℝ) ≤ ((P.natDegree : ℝ) + 1) ^ 2 * (A.card : ℝ) ^ 3 := by positivity
        have hb : ((P.natDegree : ℝ) + 1) ^ 2 * (A.card : ℝ) ^ 3 ≤
            ((P.natDegree : ℝ) + 1) ^ 2 * (A.card : ℝ) ^ 3 * (M : ℝ) ^ x3 := by
          calc ((P.natDegree : ℝ) + 1) ^ 2 * (A.card : ℝ) ^ 3
              = ((P.natDegree : ℝ) + 1) ^ 2 * (A.card : ℝ) ^ 3 * 1 := by ring
            _ ≤ ((P.natDegree : ℝ) + 1) ^ 2 * (A.card : ℝ) ^ 3 * (M : ℝ) ^ x3 :=
                mul_le_mul_of_nonneg_left hM1 hnn
        linarith
    _ = (2 * (P.natDegree : ℝ) * Cc + ((P.natDegree : ℝ) + 1) ^ 2) * (M : ℝ) ^ x3 *
          (A.card : ℝ) ^ 3 := by ring


end Conjectures.Cuts.Task6714f23562a7153bc9829e85_aux

theorem Conjectures.Cuts.Task6714f23562a7153bc9829e85 :
∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : (Fin (3 : ℕ) → ↥x8) → ℤ := fun (x10 : Fin (3 : ℕ) → ↥x8) => ∑ x11 : Fin (3 : ℕ), Polynomial.eval (↑↑(x10 x11)) x1;                   have x11 : (Fin (3 : ℕ) → ↥x8) → ℕ := fun (x11 : Fin (3 : ℕ) → ↥x8) => ∑ x12 : Fin (3 : ℕ), ↑(x11 x12);                   have x12 : (Fin (3 : ℕ) → ↥x8) → ℕ := fun (x12 : Fin (3 : ℕ) → ↥x8) => ∑ x13 : Fin (3 : ℕ), ↑(x12 x13) ^ (2 : ℕ);                   have x13 : Finset ((Fin (3 : ℕ) → ↥x8) × (Fin (3 : ℕ) → ↥x8)) := Finset.univ;                   ↑{x14 ∈ x13 | x10 x14.1 = x10 x14.2 ∧ x11 x14.1 = x11 x14.2 ∧ x12 x14.1 ≠ x12 x14.2}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ (3 : ℕ) := by
  intro P hdeg x3 hx3
  obtain ⟨x5, hx5, h⟩ := Conjectures.Cuts.Task6714f23562a7153bc9829e85_aux.main P (by omega) x3 hx3
  refine ⟨x5, hx5, ?_⟩
  intro x6 hM x8 hA
  exact h x6 hM x8 hA
