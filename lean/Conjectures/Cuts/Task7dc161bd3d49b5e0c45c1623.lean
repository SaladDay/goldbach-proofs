import Mathlib

/-!
Adapted from the accepted proof of Conjectures.Cuts.Task8681b110dfc0625ae26222ac
(upstream, Apache-2.0), itself following upstream PR #4715.  The deep-minor
self-pairing integral of the dyadic type-II matrix is invariant under the reflection
`t ↦ 1 - t` combined with complex conjugation, because the coefficient family is
real and the Farey arc set is symmetric about `1/2`; hence its imaginary part
vanishes identically and the required `o(n)` bound is immediate.
-/

open Finset MeasureTheory
open scoped ComplexConjugate

namespace Conjectures.Cuts.Task7dc161bd3d49b5e0c45c1623_aux

def arcs (Q : ℕ) (radius : ℕ → ℝ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧
    |t - (a:ℝ)/q| ≤ radius q}

private theorem reflect_mem {Q r t} (ht : t ∈ arcs Q r) : 1-t ∈ arcs Q r := by
  obtain ⟨q,a,hq,hQ,ha,hc,hr⟩ := ht
  refine ⟨q,q-a,hq,hQ,Nat.sub_le _ _,(Nat.coprime_self_sub_left ha).2 hc,?_⟩
  rw [Nat.cast_sub ha]
  have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [show 1-t-((q:ℝ)-a)/q = -(t-(a:ℝ)/q) by field_simp; ring, abs_neg]
  exact hr

noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
noncomputable def exponentialSum (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n+1), (u k:ℂ)*phase ((k:ℝ)*t)

private theorem phase_reflect (k : ℤ) (t : ℝ) :
    phase ((k:ℝ)*(1-t)) = conj (phase ((k:ℝ)*t)) := by
  unfold phase
  rw [← Complex.exp_conj]
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat]
  rw [show (2*(Real.pi:ℂ)*((k:ℂ)*(1-(t:ℂ))))*Complex.I =
    (k:ℂ)*(2*Real.pi*Complex.I) + 2*Real.pi*((k:ℂ)*t)*(-Complex.I) by ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

private theorem sum_reflect (n : ℕ) (u : ℕ → ℝ) (t : ℝ) :
    exponentialSum n u (1-t) = conj (exponentialSum n u t) := by
  unfold exponentialSum
  rw [map_sum]
  apply sum_congr rfl
  intro k _
  simpa using congrArg (fun z : ℂ => (u k:ℂ)*z) (phase_reflect (k:ℤ) t)

theorem imaginary_part_zero (Q n : ℕ) (r : ℕ → ℝ) (u v : ℕ → ℝ) :
    (∫ t in (0:ℝ)..1, (arcs Q r)ᶜ.indicator
      (fun x => exponentialSum n u x * exponentialSum n v x * phase (-(n:ℝ)*x)) t).im = 0 := by
  let F := (arcs Q r)ᶜ.indicator
      (fun x => exponentialSum n u x * exponentialSum n v x * phase (-(n:ℝ)*x))
  have hf (t : ℝ) : F (1-t) = conj (F t) := by
    have hm : 1-t ∈ arcs Q r ↔ t ∈ arcs Q r :=
      ⟨fun h => by simpa using reflect_mem h, reflect_mem⟩
    by_cases ht : t ∈ arcs Q r
    · simp [F, ht, hm]
    · have hn := phase_reflect (-(n:ℤ)) t
      push_cast at hn
      simpa [F, ht, hm, sum_reflect] using congrArg
        (fun z : ℂ => conj (exponentialSum n u t) * conj (exponentialSum n v t) * z) hn
  let J := ∫ t in (0:ℝ)..1, F t
  have hJ : J = conj J := by
    calc
      J = ∫ t in (0:ℝ)..1, F (1-t) := by
        simp [J, intervalIntegral.integral_comp_sub_left]
      _ = ∫ t in (0:ℝ)..1, conj (F t) := by simp_rw [hf]
      _ = conj J := by simp [J, intervalIntegral, integral_conj]
  change J.im = 0
  have hh := congrArg Complex.im hJ
  simpa using (show J.im = 0 by simp at hh; linarith)

end Conjectures.Cuts.Task7dc161bd3d49b5e0c45c1623_aux

theorem Conjectures.Cuts.Task7dc161bd3d49b5e0c45c1623 :
    have x1 : ℝ → ℂ := fun (x1 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x1) : ℂ) * Complex.I); have x2 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x2 : ℕ) (x3 : ℕ → ℝ) (x4 : ℝ) => ∑ x5 ∈ Finset.range (x2 + (1 : ℕ)), (↑(x3 x5) : ℂ) * x1 ((↑x5 : ℝ) * x4); have x3 : ℕ → ℕ := fun (x3 : ℕ) => Nat.log (2 : ℕ) (x3 + (2 : ℕ)) ^ (2 : ℕ); have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊(↑x4 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x5 : ℕ → ℕ := fun (x5 : ℕ) => (256 : ℕ) * x4 x5 * x3 x5; have x6 : ℕ → Set ℝ := fun (x6 : ℕ) => {x7 : ℝ | ∃ (x8 : ℕ) (x9 : ℕ), (1 : ℕ) ≤ x8 ∧ x8 ≤ x4 x6 ∧ x9 ≤ x8 ∧ x9.Coprime x8 ∧ |x7 - (↑x9 : ℝ) / (↑x8 : ℝ)| ≤ (↑(x5 x6) : ℝ) / ((↑x8 : ℝ) * (↑x6 : ℝ))}; have x7 : ArithmeticFunction ℝ := ArithmeticFunction.vonMangoldt; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (↑((ArithmeticFunction.moebius : ℕ → ℤ) x8) : ℝ); have x9 : ℕ → ℕ := fun (x9 : ℕ) => ⌊(↑x9 : ℝ) ^ (1 / 16 : ℝ)⌋₊; have x10 : ℕ → ℕ := fun (x10 : ℕ) => ⌊(↑x10 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x11 : ℕ → ℕ := fun (x11 : ℕ) => ⌊(↑x11 : ℝ) ^ (2 / 3 : ℝ)⌋₊; have x12 : ℕ → ℕ → ℝ := fun (x12 x13 : ℕ) => ∑ x14 ∈ x13.divisors with x10 x12 < x14 ∧ x14 ≤ x11 x12 ∧ x9 x12 < x13 / x14, (∑ x15 ∈ x14.divisors with x9 x12 < x15, x8 x15) * (x7 : ℕ → ℝ) (x13 / x14); have x13 : ℕ → (ℕ → ℝ) → (ℕ → ℝ) → ℂ := fun (x13 : ℕ) (x14 x15 : ℕ → ℝ) => ∫ (x16 : ℝ) in (0 : ℝ)..(1 : ℝ), (x6 x13)ᶜ.indicator (fun (x17 : ℝ) => x2 x13 x14 x17 * x2 x13 x15 x17 * x1 (-(↑x13 : ℝ) * x17)) x16; ∀ (x14 : ℝ), (0 : ℝ) < x14 → ∃ (x16 : ℕ), ∀ (x17 : ℕ), x16 ≤ x17 → Even x17 → |(x13 x17 (x12 x17) (x12 x17)).im| ≤ x14 * (↑x17 : ℝ) / (2 : ℝ) := by
  intro E S Q Q₁ H wide Λ μ U B₁ B₂ τ₂ τ₃ J ε
  refine ⟨0, fun n _ _ => ?_⟩
  have hz : (τ₃ n (τ₂ n) (τ₂ n)).im = 0 :=
    Conjectures.Cuts.Task7dc161bd3d49b5e0c45c1623_aux.imaginary_part_zero (Q₁ n) n
      (fun q => (H n : ℝ) / ((q:ℝ)*n)) (τ₂ n) (τ₂ n)
  rw [hz, abs_zero]
  positivity
