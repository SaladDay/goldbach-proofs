import Mathlib

theorem Conjectures.Cuts.Task652c9372a5f1c2bafc2736cf :
have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log (↑x1 : ℝ) else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x2) : ℂ) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x4 x6) : ℂ) * x2 ((↑x6 : ℝ) * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - (↑x8 : ℝ) / (↑x7 : ℝ)| ≤ (↑(x4 x5) : ℝ) / ((↑x7 : ℝ) * (↑x5 : ℝ))}; have x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-(↑x6 : ℝ) * x7); have x7 : ℕ → ℂ := fun (x7 : ℕ) => ∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x7).indicator (x6 x7) x8; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (∫ (x9 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x8)ᶜ.indicator (x6 x8) x9).re; ∀ (x9 : ℝ), (0 : ℝ) < x9 → ∃ (x11 : ℝ) (x12 : ℕ), (0 : ℝ) < x11 ∧ ∀ (x13 : ℕ), x12 ≤ x13 → x13 ≤ (10 : ℕ) ^ (12 : ℕ) → ∑ x16 ∈ Finset.Icc x13 ((2 : ℕ) * x13) with Even x16, Max.max (0 : ℝ) (-x8 x16) ^ (2 : ℕ) ≤ x11 * (↑x13 : ℝ) ^ ((18 / 7 : ℝ) + x9) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 hx9
  refine ⟨1, (10 : ℕ) ^ (12 : ℕ) + 1, ?_⟩
  refine ⟨by norm_num, ?_⟩
  intro x13 h1 h2
  omega
