import Mathlib

/-!
# Refutation of `L-goldbach-cut-352993f1a31b71109661701c`

The cut claims: for every `P : Polynomial ℤ` of degree `≥ 3` and every `ε > 0` there is `C > 0`
such that for all `M ≥ 2` and all `n : ℤ` the number of ordered triples with pairwise different
coordinates in `[1,M]` whose `P`-values sum to `n` is at most `C·M^ε`.

This is false for `P = X^3` and `ε = 1/8`, by the classical identity of Gérardin (1912)
(Hardy–Wright, *An Introduction to the Theory of Numbers*, §21.11, identity (21.11.4); it is the
identity Mahler used to disprove the Hardy–Littlewood conjecture that every large integer is a sum
of three positive cubes):

```
(q^4 - 9 p^3 q)^3 + (3 p q^3 - 9 p^4)^3 + (9 p^4)^3 = q^12 ,
```

which for fixed `q` is a one-parameter polynomial family of representations of `q^12` as a sum of
three positive cubes.  The three coordinates are positive, pairwise different and `≤ q^4` for
`1 ≤ p ≤ q/4`, so `q^12` is a sum of three positive cubes in `≥ q/4` ways.

Taking `q = 4 t^2` and `p = 1, …, t^2`, the coordinates lie in `[1, (2t)^8]` and the cubes sum to
`(2t)^24`, so the fiber over `n = (2t)^24` inside `[1,(2t)^8]^3` has at least `t^2` elements with
pairwise different coordinates, whereas the claimed bound is `C·((2t)^8)^{1/8} = C·2t`.  For
`t > 2C` this is a contradiction.  (The range restriction `p ≤ q/4` is what makes the family
admissible: the coordinates are positive only for `p ≲ q`, so this is not a polynomial family that
is eventually positive, yet the number of parameters `t^2 = M^{1/4}` is still a positive power of
the side length `M = (2t)^8`.)
-/

namespace Conjectures.Cuts.Task352993f1a31b71109661701c_aux

/-- The cut statement (verbatim). -/
def TaskStmt : Prop :=
∀ (x1 : Polynomial ℤ), (3 : ℕ) ≤ x1.natDegree → ∀ (x3 : ℝ), (0 : ℝ) < x3 → ∃ (x5 : ℝ), (0 : ℝ) < x5 ∧ ∀ (x6 : ℕ), (2 : ℕ) ≤ x6 → ∀ (x8 : ℤ), ↑{x9 ∈ Fintype.piFinset fun (x9 : Fin (3 : ℕ)) => Finset.Icc (1 : ℕ) x6 | x9 (0 : Fin (3 : ℕ)) ≠ x9 (1 : Fin (3 : ℕ)) ∧ x9 (0 : Fin (3 : ℕ)) ≠ x9 (2 : Fin (3 : ℕ)) ∧ x9 (1 : Fin (3 : ℕ)) ≠ x9 (2 : Fin (3 : ℕ)) ∧ ∑ x10 : Fin (3 : ℕ), Polynomial.eval (↑(x9 x10)) x1 = x8}.card ≤ x5 * ↑x6 ^ x3

/-! ### The Lehmer family over `ℤ` -/

def qZ (t : ℤ) : ℤ := 4 * t ^ 2
def XZ (t p : ℤ) : ℤ := (qZ t) ^ 4 - 9 * p ^ 3 * qZ t
def YZ (t p : ℤ) : ℤ := 3 * p * (qZ t) ^ 3 - 9 * p ^ 4
def ZZ (t p : ℤ) : ℤ := 9 * p ^ 4

/-- For `1 ≤ p ≤ t^2` the three Lehmer coordinates lie in `[1,(2t)^8]`, are strictly decreasing
and their cubes sum to `(4t^2)^12 = (2t)^24`. -/
lemma key (t p : ℤ) (ht : 1 ≤ t) (hp1 : 1 ≤ p) (hp2 : p ≤ t ^ 2) :
    1 ≤ XZ t p ∧ XZ t p ≤ (2 * t) ^ 8 ∧ 1 ≤ YZ t p ∧ YZ t p ≤ (2 * t) ^ 8 ∧
    1 ≤ ZZ t p ∧ ZZ t p ≤ (2 * t) ^ 8 ∧ ZZ t p < YZ t p ∧ YZ t p < XZ t p ∧
    XZ t p ^ 3 + YZ t p ^ 3 + ZZ t p ^ 3 = (qZ t) ^ 12 := by
  have hp3 : p ^ 3 ≤ t ^ 6 := by
    calc p ^ 3 ≤ (t ^ 2) ^ 3 := pow_le_pow_left₀ (by omega) hp2 3
      _ = t ^ 6 := by ring
  have hp4 : p ^ 4 ≤ t ^ 8 := by
    calc p ^ 4 ≤ (t ^ 2) ^ 4 := pow_le_pow_left₀ (by omega) hp2 4
      _ = t ^ 8 := by ring
  have hpt : p * t ^ 6 ≤ t ^ 8 := by
    calc p * t ^ 6 ≤ t ^ 2 * t ^ 6 := mul_le_mul_of_nonneg_right hp2 (by positivity)
      _ = t ^ 8 := by ring
  have h3t : p ^ 3 * t ^ 2 ≤ t ^ 8 := by
    calc p ^ 3 * t ^ 2 ≤ t ^ 6 * t ^ 2 := mul_le_mul_of_nonneg_right hp3 (by positivity)
      _ = t ^ 8 := by ring
  have h4p : p ^ 4 ≤ p * t ^ 6 := by
    calc p ^ 4 = p * p ^ 3 := by ring
      _ ≤ p * t ^ 6 := mul_le_mul_of_nonneg_left hp3 (by omega)
  have ht8 : 1 ≤ t ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 1) ht 8
    simpa using this
  have ht6 : 1 ≤ t ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 1) ht 6
    simpa using this
  have hpt1 : 1 ≤ p * t ^ 6 := by nlinarith [ht6]
  have hp4one : 1 ≤ p ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 1) hp1 4
    simpa using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [XZ, qZ]; nlinarith [h3t, ht8]
  · simp only [XZ, qZ]; nlinarith [h3t]
  · simp only [YZ, qZ]; nlinarith [h4p, hpt1]
  · simp only [YZ, qZ]; nlinarith [h4p, hpt]
  · simp only [ZZ]; nlinarith [hp4one]
  · simp only [ZZ]; nlinarith [hp4]
  · simp only [YZ, ZZ, qZ]; nlinarith [h4p]
  · simp only [XZ, YZ, qZ]; nlinarith [h3t, hpt, h4p]
  · simp only [XZ, YZ, ZZ, qZ]; ring

end Conjectures.Cuts.Task352993f1a31b71109661701c_aux

namespace Conjectures.Cuts.Task352993f1a31b71109661701c_aux

/-! ### The family over `ℕ` -/

def Xn (t p : ℕ) : ℕ := (XZ (t : ℤ) (p : ℤ)).toNat
def Yn (t p : ℕ) : ℕ := (YZ (t : ℤ) (p : ℤ)).toNat
def Zn (t p : ℕ) : ℕ := (ZZ (t : ℤ) (p : ℤ)).toNat

/-- The side length of the box: `(2t)^8 = q^4`. -/
def Mt (t : ℕ) : ℕ := (2 * t) ^ 8

/-- The ordered triple attached to the parameter `p`. -/
def triple (t p : ℕ) (i : Fin 3) : ℕ :=
  if i = 0 then Xn t p else if i = 1 then Yn t p else Zn t p

lemma triple_zero (t p : ℕ) : triple t p 0 = Xn t p := by
  simp [triple]

lemma triple_one (t p : ℕ) : triple t p 1 = Yn t p := by
  simp only [triple]
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  simp [h10]

lemma triple_two (t p : ℕ) : triple t p 2 = Zn t p := by
  simp only [triple]
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp [h20, h21]

/-- The fiber of the cut at `P = X^3`, side length `(2t)^8` and target `(2t)^24`. -/
noncomputable def fiber (t : ℕ) : Finset (Fin 3 → ℕ) :=
  {x9 ∈ Fintype.piFinset fun (_ : Fin 3) => Finset.Icc 1 (Mt t) |
    x9 0 ≠ x9 1 ∧ x9 0 ≠ x9 2 ∧ x9 1 ≠ x9 2 ∧
    ∑ i : Fin 3, Polynomial.eval (↑(x9 i)) (Polynomial.X ^ (3 : ℕ) : Polynomial ℤ) =
      (((2 * t) ^ 24 : ℕ) : ℤ)}

lemma mem_fiber (t p : ℕ) (ht : 1 ≤ t) (hp1 : 1 ≤ p) (hp2 : p ≤ t ^ 2) :
    triple t p ∈ fiber t := by
  obtain ⟨hX1, hX2, hY1, hY2, hZ1, hZ2, hZY, hYX, hsum⟩ :=
    key (t : ℤ) (p : ℤ) (by omega) (by omega) (by exact_mod_cast hp2)
  have cX : ((Xn t p : ℕ) : ℤ) = XZ (t : ℤ) (p : ℤ) := by
    simp [Xn, Int.toNat_of_nonneg (by omega : 0 ≤ XZ (t : ℤ) (p : ℤ))]
  have cY : ((Yn t p : ℕ) : ℤ) = YZ (t : ℤ) (p : ℤ) := by
    simp [Yn, Int.toNat_of_nonneg (by omega : 0 ≤ YZ (t : ℤ) (p : ℤ))]
  have cZ : ((Zn t p : ℕ) : ℤ) = ZZ (t : ℤ) (p : ℤ) := by
    simp [Zn, Int.toNat_of_nonneg (by omega : 0 ≤ ZZ (t : ℤ) (p : ℤ))]
  have cM : ((Mt t : ℕ) : ℤ) = (2 * (t : ℤ)) ^ 8 := by
    unfold Mt; push_cast; ring
  have bX1 : 1 ≤ Xn t p := by omega
  have bX2 : Xn t p ≤ Mt t := by omega
  have bY1 : 1 ≤ Yn t p := by omega
  have bY2 : Yn t p ≤ Mt t := by omega
  have bZ1 : 1 ≤ Zn t p := by omega
  have bZ2 : Zn t p ≤ Mt t := by omega
  have bYX : Yn t p < Xn t p := by omega
  have bZY : Zn t p < Yn t p := by omega
  have hmem : ∀ i : Fin 3, triple t p i ∈ Finset.Icc 1 (Mt t) := by
    intro i
    rw [Finset.mem_Icc, triple]
    split_ifs <;> omega
  have hsum' : ∑ i : Fin 3, Polynomial.eval (↑(triple t p i))
      (Polynomial.X ^ (3 : ℕ) : Polynomial ℤ) = (((2 * t) ^ 24 : ℕ) : ℤ) := by
    rw [Fin.sum_univ_three, triple_zero, triple_one, triple_two]
    have e0 : Polynomial.eval (↑(Xn t p)) (Polynomial.X ^ (3 : ℕ) : Polynomial ℤ) =
        ((Xn t p : ℕ) : ℤ) ^ 3 := by simp [Polynomial.eval_pow, Polynomial.eval_X]
    have e1 : Polynomial.eval (↑(Yn t p)) (Polynomial.X ^ (3 : ℕ) : Polynomial ℤ) =
        ((Yn t p : ℕ) : ℤ) ^ 3 := by simp [Polynomial.eval_pow, Polynomial.eval_X]
    have e2 : Polynomial.eval (↑(Zn t p)) (Polynomial.X ^ (3 : ℕ) : Polynomial ℤ) =
        ((Zn t p : ℕ) : ℤ) ^ 3 := by simp [Polynomial.eval_pow, Polynomial.eval_X]
    rw [e0, e1, e2, cX, cY, cZ, hsum]
    simp only [qZ]
    push_cast
    ring
  rw [fiber, Finset.mem_filter]
  refine ⟨Fintype.mem_piFinset.mpr hmem, ?_, ?_, ?_, ?_⟩
  · rw [triple_zero, triple_one]; omega
  · rw [triple_zero, triple_two]; omega
  · rw [triple_one, triple_two]; omega
  · exact hsum'

lemma card_fiber (t : ℕ) (ht : 1 ≤ t) : t ^ 2 ≤ (fiber t).card := by
  have hsub : (Finset.Icc 1 (t ^ 2)).image (triple t) ⊆ fiber t := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact mem_fiber t p ht (Finset.mem_Icc.mp hp).1 (Finset.mem_Icc.mp hp).2
  have hinj : Set.InjOn (triple t) ((Finset.Icc 1 (t ^ 2) : Finset ℕ) : Set ℕ) := by
    intro p _ p' _ h
    have h2 := congr_fun h 2
    rw [triple_two, triple_two] at h2
    have hz : (ZZ (t : ℤ) (p : ℤ)) = (ZZ (t : ℤ) (p' : ℤ)) := by
      have := congrArg (fun n : ℕ => (n : ℤ)) h2
      rwa [Zn, Zn, Int.toNat_of_nonneg (by simp [ZZ]),
        Int.toNat_of_nonneg (by simp [ZZ])] at this
    have h4 : (p : ℤ) ^ 4 = (p' : ℤ) ^ 4 := by simp only [ZZ] at hz; linarith
    have hle : (p : ℤ) ≤ (p' : ℤ) := le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h4.le
    have hge : (p' : ℤ) ≤ (p : ℤ) := le_of_pow_le_pow_left₀ (by norm_num) (by positivity) h4.ge
    omega
  calc t ^ 2 = (Finset.Icc 1 (t ^ 2)).card := by simp
    _ = ((Finset.Icc 1 (t ^ 2)).image (triple t)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (fiber t).card := Finset.card_le_card hsub

end Conjectures.Cuts.Task352993f1a31b71109661701c_aux

/-- The cut statement is false: it fails at `P = X ^ 3` and exponent `1 / 8`. -/
theorem not_task : ¬ Conjectures.Cuts.Task352993f1a31b71109661701c_aux.TaskStmt := by
  intro h
  have hdeg : (3 : ℕ) ≤ (Polynomial.X ^ (3 : ℕ) : Polynomial ℤ).natDegree := by
    rw [Polynomial.natDegree_X_pow]
  obtain ⟨x5, hx5, h⟩ :=
    h (Polynomial.X ^ (3 : ℕ)) hdeg ((1 : ℝ) / 8) (by norm_num)
  obtain ⟨t, ht⟩ := exists_nat_gt (2 * x5)
  have htpos : (0 : ℝ) < (t : ℝ) := by linarith
  have ht1 : 1 ≤ t := by exact_mod_cast htpos
  have hM2 : 2 ≤ Conjectures.Cuts.Task352993f1a31b71109661701c_aux.Mt t := by
    calc 2 ≤ (2 * t) ^ 1 := by simp only [pow_one]; omega
      _ ≤ (2 * t) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have hbound := h (Conjectures.Cuts.Task352993f1a31b71109661701c_aux.Mt t) hM2
    (((2 * t) ^ 24 : ℕ) : ℤ)
  change ((Conjectures.Cuts.Task352993f1a31b71109661701c_aux.fiber t).card : ℝ) ≤
    x5 * ((Conjectures.Cuts.Task352993f1a31b71109661701c_aux.Mt t : ℕ) : ℝ) ^ ((1 : ℝ) / 8) at hbound
  have hcard := Conjectures.Cuts.Task352993f1a31b71109661701c_aux.card_fiber t ht1
  have hrpow : ((Conjectures.Cuts.Task352993f1a31b71109661701c_aux.Mt t : ℕ) : ℝ) ^ ((1 : ℝ) / 8) =
      2 * (t : ℝ) := by
    have h1 : ((Conjectures.Cuts.Task352993f1a31b71109661701c_aux.Mt t : ℕ) : ℝ) =
        (2 * (t : ℝ)) ^ (8 : ℕ) := by
      simp [Conjectures.Cuts.Task352993f1a31b71109661701c_aux.Mt]
    rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hcard' : (t : ℝ) ^ 2 ≤ ((Conjectures.Cuts.Task352993f1a31b71109661701c_aux.fiber t).card : ℝ) := by
    exact_mod_cast hcard
  rw [hrpow] at hbound
  have hlt : x5 * (2 * (t : ℝ)) < (t : ℝ) ^ 2 := by nlinarith
  linarith

open Conjectures.Cuts.Task352993f1a31b71109661701c_aux in
theorem Conjectures.Cuts.Refutea0b886bfb6fc9156afc5db5e : ¬ (∀ (x1 : Polynomial ℤ), (3 : ℕ) ≤ x1.natDegree → ∀ (x3 : ℝ), (0 : ℝ) < x3 → ∃ (x5 : ℝ), (0 : ℝ) < x5 ∧ ∀ (x6 : ℕ), (2 : ℕ) ≤ x6 → ∀ (x8 : ℤ), ↑{x9 ∈ Fintype.piFinset fun (x9 : Fin (3 : ℕ)) => Finset.Icc (1 : ℕ) x6 | x9 (0 : Fin (3 : ℕ)) ≠ x9 (1 : Fin (3 : ℕ)) ∧ x9 (0 : Fin (3 : ℕ)) ≠ x9 (2 : Fin (3 : ℕ)) ∧ x9 (1 : Fin (3 : ℕ)) ≠ x9 (2 : Fin (3 : ℕ)) ∧ ∑ x10 : Fin (3 : ℕ), Polynomial.eval (↑(x9 x10)) x1 = x8}.card ≤ x5 * ↑x6 ^ x3) := by
  first
  | exact not_task
  | exact Conjectures.Cuts.Task352993f1a31b71109661701c_aux.card_fiber
  | exact Conjectures.Cuts.Task352993f1a31b71109661701c_aux.mem_fiber
  | exact Conjectures.Cuts.Task352993f1a31b71109661701c_aux.triple_two
  | exact Conjectures.Cuts.Task352993f1a31b71109661701c_aux.triple_one
  | exact Conjectures.Cuts.Task352993f1a31b71109661701c_aux.triple_zero
  | exact Conjectures.Cuts.Task352993f1a31b71109661701c_aux.key
