import Mathlib

/-!
# Premise 1/2 of the cut `L-goldbach-cut-02aab4ac77906f1936d14042`

The counted family is a filtered subset of `x14 ⊆ x13 ⊆ x11.product x11`, where
`x11 = Fintype.piFinset (fun _ : Fin 4 => x8)`, so `x11.card = x8.card ^ 4`.
Hence the count is at most `x8.card ^ 4 * x8.card ^ 4 = x8.card ^ 8`, and the side condition
`(x8.card : ℝ) ≤ x6 ^ (x3 / 3)` turns the factor `x8.card ^ 3` into `x6 ^ x3`, leaving
`x8.card ^ 5`.  The witness is the constant `x5 = 1`; the polynomial hypothesis
`x1.natDegree = 3` and the collision predicates are not needed, only the chain of filter
inclusions.
-/

namespace Conjectures.Cuts.Task85192744354d130305c7854e_aux

lemma card_le_of_subset {α : Type*} [DecidableEq α] {s t : Finset α} (h : s ⊆ t) :
    s.card ≤ t.card := Finset.card_le_card h

lemma card_piFinset_four (x8 : Finset ℕ) :
    (Fintype.piFinset (fun _ : Fin (4 : ℕ) => x8)).card = x8.card ^ (4 : ℕ) := by
  rw [Fintype.card_piFinset]
  simp

/-- Third power of a nonneg real is monotone. -/
lemma pow_three_le_pow_three {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ (3 : ℕ) ≤ b ^ (3 : ℕ) :=
  pow_le_pow_left₀ ha h 3

end Conjectures.Cuts.Task85192744354d130305c7854e_aux

theorem Conjectures.Cuts.Task85192744354d130305c7854e :
∀ (x1 : Polynomial ℤ),   x1.natDegree = (3 : ℕ) →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   (↑x8.card : ℝ) ≤ (↑x6 : ℝ) ^ (x3 / (3 : ℝ)) →                     have x11 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x11 : Fin (4 : ℕ)) => x8;                     have x12 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x12 : Fin (4 : ℕ) → ℕ) => ∑ x13 : Fin (4 : ℕ), Polynomial.eval (↑(x12 x13) : ℤ) x1;                     have x13 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x13 ∈ x11.product x11 | x12 x13.1 = x12 x13.2 ∧ ∀ (x14 : Fin (4 : ℕ) × Fin (4 : ℕ)), x13.1 x14.1 ≠ x13.2 x14.2};                     have x14 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x14 ∈ x13 | ∀ (x15 x16 : Fin (4 : ℕ) × Fin (4 : ℕ)), x15.1 ≠ x15.2 → x16.1 ≠ x16.2 → x14.1 x15.1 + x14.1 x15.2 ≠ x14.2 x16.1 + x14.2 x16.2 ∧ x14.1 x15.1 ^ (2 : ℕ) + x14.1 x15.2 ^ (2 : ℕ) ≠ x14.2 x16.1 ^ (2 : ℕ) + x14.2 x16.2 ^ (2 : ℕ)};                     have x15 : (Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ) → Finset ℕ := fun (x15 : (Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) => Finset.image x15.1 Finset.univ ∪ Finset.image x15.2 Finset.univ;                     (↑{x16 ∈ x14 | (x15 x16).card = (8 : ℕ)}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ (5 : ℕ) := by
  intro x1 _ x3 hx3
  refine ⟨1, one_pos, ?_⟩
  intro x6 hx6 x8 _ hx8 x11 x12 x13 x14 x15
  have hsub : {x16 ∈ x14 | (x15 x16).card = (8 : ℕ)} ⊆ x11.product x11 :=
    (Finset.filter_subset _ x14).trans ((Finset.filter_subset _ x13).trans
      (Finset.filter_subset _ (x11.product x11)))
  have h11 : x11.card = x8.card ^ (4 : ℕ) :=
    Conjectures.Cuts.Task85192744354d130305c7854e_aux.card_piFinset_four x8
  have hcard : ({x16 ∈ x14 | (x15 x16).card = (8 : ℕ)}).card ≤
      x8.card ^ (4 : ℕ) * x8.card ^ (4 : ℕ) := by
    calc _ ≤ (x11.product x11).card :=
          Conjectures.Cuts.Task85192744354d130305c7854e_aux.card_le_of_subset hsub
      _ = x11.card * x11.card := Finset.card_product x11 x11
      _ = x8.card ^ (4 : ℕ) * x8.card ^ (4 : ℕ) := by rw [h11]
  have hcast : ((↑{x16 ∈ x14 | (x15 x16).card = (8 : ℕ)}.card : ℕ) : ℝ) ≤
      (↑x8.card : ℝ) ^ (4 : ℕ) * (↑x8.card : ℝ) ^ (4 : ℕ) := by
    exact_mod_cast hcard
  have hpow : (↑x8.card : ℝ) ^ (3 : ℕ) ≤ (↑x6 : ℝ) ^ x3 := by
    have h3 : (↑x8.card : ℝ) ^ (3 : ℕ) ≤ ((↑x6 : ℝ) ^ (x3 / (3 : ℝ))) ^ (3 : ℕ) :=
      Conjectures.Cuts.Task85192744354d130305c7854e_aux.pow_three_le_pow_three
        (Nat.cast_nonneg _) hx8
    have hrw : ((↑x6 : ℝ) ^ (x3 / (3 : ℝ))) ^ (3 : ℕ) = (↑x6 : ℝ) ^ x3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg x6)]
      congr 1
      ring
    linarith [h3, hrw]
  calc ((↑{x16 ∈ x14 | (x15 x16).card = (8 : ℕ)}.card : ℕ) : ℝ)
      ≤ (↑x8.card : ℝ) ^ (4 : ℕ) * (↑x8.card : ℝ) ^ (4 : ℕ) := hcast
    _ = (↑x8.card : ℝ) ^ (5 : ℕ) * (↑x8.card : ℝ) ^ (3 : ℕ) := by ring
    _ ≤ (↑x8.card : ℝ) ^ (5 : ℕ) * (↑x6 : ℝ) ^ x3 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (1 : ℝ) * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ (5 : ℕ) := by ring
