import Mathlib

/-!
# Premise 1/2 of the cut `L-goldbach-cut-a7333324bc5804e5d42aeece`

The counted family is a filtered subset of `x15 ⊆ x14 ⊆ x12 × x12`, where
`x12 = Fintype.piFinset (fun _ : Fin 4 => x8)`, so `x12.card = x8.card ^ 4`.
Hence the count is at most `x8.card ^ 4 * x8.card ^ 4`, and the side condition
`(x8.card : ℝ) ≤ x6 ^ (x3 / 4)` turns the second factor `x8.card ^ 4` into
`x6 ^ x3`.  The witness is the constant `x5 = 1`; the polynomial hypothesis
`4 ≤ x1.natDegree` and the two collision predicates `x16`, `x17` are not
needed, only the chain of filter inclusions.
-/

namespace Conjectures.Cuts.Task8bb4883b9c82e7ea9aa55b87_aux

lemma card_le_of_subset {α : Type*} [DecidableEq α] {s t : Finset α} (h : s ⊆ t) :
    s.card ≤ t.card := Finset.card_le_card h

lemma card_piFinset_four (x8 : Finset ℕ) :
    (Fintype.piFinset (fun _ : Fin (4 : ℕ) => x8)).card = x8.card ^ (4 : ℕ) := by
  rw [Fintype.card_piFinset]
  simp

/-- Fourth power of a nonneg real is monotone. -/
lemma pow_four_le_pow_four {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ (4 : ℕ) ≤ b ^ (4 : ℕ) :=
  pow_le_pow_left₀ ha h 4

end Conjectures.Cuts.Task8bb4883b9c82e7ea9aa55b87_aux

theorem Conjectures.Cuts.Task8bb4883b9c82e7ea9aa55b87 :
∀ (x1 : Polynomial ℤ),   (4 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   (↑x8.card : ℝ) ≤ (↑x6 : ℝ) ^ (x3 / (4 : ℝ)) →                     have x11 : ℕ → ℤ := fun (x11 : ℕ) => Polynomial.eval (↑x11 : ℤ) x1;                     have x12 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x12 : Fin (4 : ℕ)) => x8;                     have x13 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x13 : Fin (4 : ℕ) → ℕ) => ∑ x14 : Fin (4 : ℕ), x11 (x13 x14);                     have x14 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x14 ∈ x12.product x12 | x13 x14.1 = x13 x14.2 ∧ ∀ (x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 x15.1 ≠ x14.2 x15.2};                     have x15 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x15 ∈ x14 | ∀ (x16 x17 : Fin (4 : ℕ) × Fin (4 : ℕ)), x16.1 ≠ x16.2 → x17.1 ≠ x17.2 → x15.1 x16.1 + x15.1 x16.2 ≠ x15.2 x17.1 + x15.2 x17.2 ∧ x15.1 x16.1 ^ (2 : ℕ) + x15.1 x16.2 ^ (2 : ℕ) ≠ x15.2 x17.1 ^ (2 : ℕ) + x15.2 x17.2 ^ (2 : ℕ)};                     let x16 : (Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ) → Prop := fun (x16 : (Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) => ∃ (x17 : Fin (4 : ℕ) × Fin (4 : ℕ)), x11 (x16.1 x17.1) = x11 (x16.2 x17.2);                     let x17 : (Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ) → Prop := fun (x17 : (Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) => ∃ (x18 : Fin (4 : ℕ) × Fin (4 : ℕ)) (x19 : Fin (4 : ℕ) × Fin (4 : ℕ)), x18.1 ≠ x18.2 ∧ x19.1 ≠ x19.2 ∧ x11 (x17.1 x18.1) + x11 (x17.1 x18.2) = x11 (x17.2 x19.1) + x11 (x17.2 x19.2);                     (↑{x18 ∈ x15 | ¬x16 x18 ∧ ¬x17 x18}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ (4 : ℕ) := by
  intro x1 _ x3 hx3
  refine ⟨1, one_pos, ?_⟩
  intro x6 hx6 x8 _ hx8 x11 x12 x13 x14 x15 x16 x17
  have hsub : {x18 ∈ x15 | ¬x16 x18 ∧ ¬x17 x18} ⊆ x12.product x12 :=
    (Finset.filter_subset _ x15).trans ((Finset.filter_subset _ x14).trans
      (Finset.filter_subset _ (x12.product x12)))
  have h12 : x12.card = x8.card ^ (4 : ℕ) :=
    Conjectures.Cuts.Task8bb4883b9c82e7ea9aa55b87_aux.card_piFinset_four x8
  have hcard : ({x18 ∈ x15 | ¬x16 x18 ∧ ¬x17 x18}).card ≤ x8.card ^ (4 : ℕ) * x8.card ^ (4 : ℕ) := by
    calc _ ≤ (x12.product x12).card :=
          Conjectures.Cuts.Task8bb4883b9c82e7ea9aa55b87_aux.card_le_of_subset hsub
      _ = x12.card * x12.card := Finset.card_product x12 x12
      _ = x8.card ^ (4 : ℕ) * x8.card ^ (4 : ℕ) := by rw [h12]
  have hcast : ((↑{x18 ∈ x15 | ¬x16 x18 ∧ ¬x17 x18}.card : ℕ) : ℝ) ≤
      (↑x8.card : ℝ) ^ (4 : ℕ) * (↑x8.card : ℝ) ^ (4 : ℕ) := by
    exact_mod_cast hcard
  have hpow : (↑x8.card : ℝ) ^ (4 : ℕ) ≤ (↑x6 : ℝ) ^ x3 := by
    have h4 : (↑x8.card : ℝ) ^ (4 : ℕ) ≤ ((↑x6 : ℝ) ^ (x3 / (4 : ℝ))) ^ (4 : ℕ) :=
      Conjectures.Cuts.Task8bb4883b9c82e7ea9aa55b87_aux.pow_four_le_pow_four
        (Nat.cast_nonneg _) hx8
    have hrw : ((↑x6 : ℝ) ^ (x3 / (4 : ℝ))) ^ (4 : ℕ) = (↑x6 : ℝ) ^ x3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg x6)]
      congr 1
      ring
    linarith [h4, hrw]
  calc ((↑{x18 ∈ x15 | ¬x16 x18 ∧ ¬x17 x18}.card : ℕ) : ℝ)
      ≤ (↑x8.card : ℝ) ^ (4 : ℕ) * (↑x8.card : ℝ) ^ (4 : ℕ) := hcast
    _ ≤ (↑x8.card : ℝ) ^ (4 : ℕ) * (↑x6 : ℝ) ^ x3 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (1 : ℝ) * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ (4 : ℕ) := by ring
