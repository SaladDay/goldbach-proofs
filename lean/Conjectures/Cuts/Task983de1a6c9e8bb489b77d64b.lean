import Mathlib

namespace Conjectures.Cuts.Task983de1a6c9e8bb489b77d64b_aux

theorem band_inter_empty {α : Type*} (A B C D : Set α) :
    ((A \ B) \ (C \ B)) \ D ∩ C = ∅ := by
  ext t
  simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]
  tauto

theorem empty_indicator_integral_re (f : ℝ → ℂ) :
    (∫ t in (0 : ℝ)..(1 : ℝ), (∅ : Set ℝ).indicator f t).re = 0 := by
  simp

end Conjectures.Cuts.Task983de1a6c9e8bb489b77d64b_aux

theorem Conjectures.Cuts.Task983de1a6c9e8bb489b77d64b :
    have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log (↑x1 : ℝ) else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x2) : ℂ) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x4 x6) : ℂ) * x2 ((↑x6 : ℝ) * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - (↑x8 : ℝ) / (↑x7 : ℝ)| ≤ (↑(x4 x5) : ℝ) / ((↑x7 : ℝ) * (↑x5 : ℝ))}; have x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-(↑x6 : ℝ) * x7); have x7 : ℕ → ℕ := fun (x7 : ℕ) => ⌊(↑x7 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x8 : ℕ → ℕ := fun (x8 : ℕ) => (256 : ℕ) * x7 x8 * x4 x8; have x9 : ℕ → Set ℝ := fun (x9 : ℕ) => {x10 : ℝ | ∃ (x11 : ℕ) (x12 : ℕ), (1 : ℕ) ≤ x11 ∧ x11 ≤ x7 x9 ∧ x12 ≤ x11 ∧ x12.Coprime x11 ∧ |x10 - (↑x12 : ℝ) / (↑x11 : ℝ)| ≤ (↑(x8 x9) : ℝ) / ((↑x11 : ℝ) * (↑x9 : ℝ))}; have x10 : ℕ → Set ℝ := fun (x10 : ℕ) => {x11 : ℝ | ∃ (x12 : ℕ) (x13 : ℕ), (1 : ℕ) ≤ x12 ∧ x12 ≤ x4 x10 ∧ x13 ≤ x12 ∧ x13.Coprime x12 ∧ |x11 - (↑x13 : ℝ) / (↑x12 : ℝ)| ≤ (↑(x8 x10) : ℝ) / ((↑x12 : ℝ) * (↑x10 : ℝ))}; have x11 : ℕ → Set ℝ := fun (x11 : ℕ) => x10 x11 \ x5 x11; have x12 : ℕ → Set ℝ := fun (x12 : ℕ) => (x9 x12 \ x5 x12) \ x11 x12; have x13 : ℕ → Set ℝ := fun (x13 : ℕ) => {x14 : ℝ | ∃ (x15 : ℕ) (x16 : ℕ), (1 : ℕ) ≤ x15 ∧ x15 ≤ x7 x13 ∧ x16 ≤ x15 ∧ x16.Coprime x15 ∧ |x14 - (↑x16 : ℝ) / (↑x15 : ℝ)| ≤ (↑(x4 x13) : ℝ) * (↑x13 : ℝ) ^ (1 / 6 : ℝ) / ((↑x15 : ℝ) * (↑x13 : ℝ))}; have x14 : ℕ → Set ℝ → ℝ := fun (x14 : ℕ) (x15 : Set ℝ) => (∫ (x16 : ℝ) in (0 : ℝ)..(1 : ℝ), x15.indicator (x6 x14) x16).re; have x15 : (ℕ → Set ℝ) → Prop := fun (x15 : ℕ → Set ℝ) => ∀ (x16 : ℝ), (0 : ℝ) < x16 → ∃ (x18 : ℕ), ∀ (x19 : ℕ), x18 ≤ x19 → Even x19 → -(x16 / (2 : ℝ) * (↑x19 : ℝ)) ≤ x14 x19 (x15 x19); x15 fun (x16 : ℕ) => x12 x16 \ x13 x16 ∩ x10 x16 := by
  refine fun x16 hx16 => ⟨0, fun x19 _ _ => ?_⟩
  beta_reduce
  rw [Conjectures.Cuts.Task983de1a6c9e8bb489b77d64b_aux.band_inter_empty]
  rw [Conjectures.Cuts.Task983de1a6c9e8bb489b77d64b_aux.empty_indicator_integral_re]
  have hnonneg : (0 : ℝ) ≤ x16 / 2 * (x19 : ℝ) := by positivity
  linarith
