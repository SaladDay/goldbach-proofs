import Mathlib

/-!
Cut premise 1/2 of L-goldbach-cut-5eb70d35d0d67d8ffb2800d9.

The quantified hypothesis `(2 : ℕ) ≤ x7 → x7 ≤ (2 : ℕ)` pins the parameter to `x7 = 2`, so
`x10 ⊆ Finset.Icc 1 2` has at most two elements.  The counted set of collision pairs with
different permutation orbits is a filter of the product `x12 × x12`, hence its cardinality is at
most `(x10.card ^ 3) ^ 2 = x10.card ^ 6`.  Since `x10.card ≤ 2`, we have
`x10.card ^ 6 ≤ 8 * x10.card ^ 3 ≤ 8 * 2 ^ x4 * x10.card ^ 3` for every `x4 > 0` (using
`1 ≤ 2 ^ x4`), so the witness `x6 = 8` works uniformly.  The polynomial hypotheses
`3 ≤ x1.natDegree` and `x1.natDegree ≠ 3` are not needed for this counting bound.

Self-contained: Mathlib only.
-/

theorem Conjectures.Cuts.Task1898a9d6dce8e70325f5e151 :
    ∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     x1.natDegree ≠ (3 : ℕ) →       ∀ (x4 : ℝ),         (0 : ℝ) < x4 →           ∃ (x6 : ℝ),             (0 : ℝ) < x6 ∧               ∀ (x7 : ℕ),                 (2 : ℕ) ≤ x7 →                   x7 ≤ (2 : ℕ) →                     ∀ x10 ⊆ Finset.Icc (1 : ℕ) x7,                       have x12 : Finset (Fin (3 : ℕ) → ℕ) := Fintype.piFinset fun (x12 : Fin (3 : ℕ)) => x10;                       have x13 : (Fin (3 : ℕ) → ℕ) → ℤ := fun (x13 : Fin (3 : ℕ) → ℕ) => ∑ x14 : Fin (3 : ℕ), Polynomial.eval (↑(x13 x14)) x1;                       ↑{x14 ∈ x12.product x12 | x13 x14.1 = x13 x14.2 ∧ ∀ (x15 : Equiv.Perm (Fin (3 : ℕ))), x14.2 ≠ x14.1 ∘ ⇑x15}.card ≤ x6 * ↑x7 ^ x4 * ↑x10.card ^ (3 : ℕ) := by
  intro x1 _ _ x4 hx4
  refine ⟨8, by norm_num, ?_⟩
  intro x7 hx7 hx7'
  have hx7eq : x7 = 2 := le_antisymm hx7' hx7
  subst hx7eq
  intro x10 hx10
  dsimp only
  have hcard : ((x10.card : ℕ) : ℝ) ≤ 2 := by
    have h1 : x10.card ≤ (Finset.Icc (1 : ℕ) 2).card := Finset.card_le_card hx10
    have h2 : (Finset.Icc (1 : ℕ) 2).card = 2 := by decide
    exact_mod_cast (h1.trans_eq h2)
  have hn0 : (0 : ℝ) ≤ (x10.card : ℝ) := Nat.cast_nonneg _
  have hn2 : ((x10.card : ℝ)) ^ 2 ≤ 4 := by nlinarith
  have hn3 : ((x10.card : ℝ)) ^ 3 ≤ 8 := by
    have h3 : ((x10.card : ℝ)) ^ 3 = ((x10.card : ℝ)) ^ 2 * ((x10.card : ℝ)) := by ring
    rw [h3]
    have := mul_le_mul hn2 hcard hn0 (by norm_num)
    linarith
  have hrpow : (1 : ℝ) ≤ (2 : ℝ) ^ x4 := Real.one_le_rpow (by norm_num) hx4.le
  have hkey : ((x10.card : ℝ)) ^ 6 ≤ 8 * (2 : ℝ) ^ x4 * ((x10.card : ℝ)) ^ 3 := by
    have h6 : ((x10.card : ℝ)) ^ 6 = ((x10.card : ℝ)) ^ 3 * ((x10.card : ℝ)) ^ 3 := by ring
    have hpos3 : (0 : ℝ) ≤ ((x10.card : ℝ)) ^ 3 := by positivity
    have h1 : ((x10.card : ℝ)) ^ 3 * ((x10.card : ℝ)) ^ 3 ≤ ((x10.card : ℝ)) ^ 3 * 8 :=
      mul_le_mul_of_nonneg_left hn3 hpos3
    have h2 : (8 : ℝ) ≤ 8 * (2 : ℝ) ^ x4 := by nlinarith
    have h3' : ((x10.card : ℝ)) ^ 3 * 8 ≤ ((x10.card : ℝ)) ^ 3 * (8 * (2 : ℝ) ^ x4) :=
      mul_le_mul_of_nonneg_left h2 hpos3
    linarith
  calc (↑{x14 ∈ (Fintype.piFinset fun x12 : Fin 3 => x10).product
            (Fintype.piFinset fun x12 : Fin 3 => x10) |
          ∑ x14_1, Polynomial.eval (↑(x14.1 x14_1)) x1 =
            ∑ x14_1, Polynomial.eval (↑(x14.2 x14_1)) x1 ∧
            ∀ (x15 : Equiv.Perm (Fin 3)), x14.2 ≠ x14.1 ∘ ⇑x15}.card : ℝ)
      ≤ ↑((Fintype.piFinset fun x12 : Fin 3 => x10).product
            (Fintype.piFinset fun x12 : Fin 3 => x10)).card := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ = ((x10.card : ℝ)) ^ 6 := by
        simp [Finset.card_product]
        ring
    _ ≤ 8 * (2 : ℝ) ^ x4 * ((x10.card : ℝ)) ^ 3 := hkey
