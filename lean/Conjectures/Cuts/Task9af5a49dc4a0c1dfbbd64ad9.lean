import Mathlib

/-!
Exceptional-modulus set from a weighted first moment.

Given a finite set `x1` with nonnegative weights `x2`, a threshold `x3 > 0` and a
nonnegative factor `x4` with `(∑ x2) * x4 ≤ x3 * x5`, the set of indices whose weight
exceeds `x3` is an exceptional set: every index outside it has weight at most `x3`, and
its cardinality times `x4` is at most `x5`.  Indeed `card · x3 ≤ ∑_{heavy} x2 ≤ ∑ x2`,
and multiplying by `x4 ≥ 0` and cancelling `x3 > 0` gives the bound.
-/

namespace Conjectures.Cuts.Task9af5a49dc4a0c1dfbbd64ad9_aux

theorem main (x1 : Finset ℕ) (x2 : ℕ → ℝ) (x3 x4 x5 : ℝ)
    (hx3 : (0 : ℝ) < x3) (hx4 : (0 : ℝ) ≤ x4)
    (hnonneg : ∀ x8 ∈ x1, (0 : ℝ) ≤ x2 x8)
    (hsum : (∑ x9 ∈ x1, x2 x9) * x4 ≤ x3 * x5) :
    ∃ x10 ⊆ x1, (↑x10.card : ℝ) * x4 ≤ x5 ∧
      ∀ x11 ∈ x1, x11 ∉ x10 → x2 x11 ≤ x3 := by
  classical
  set S : Finset ℕ := x1.filter (fun a => x3 < x2 a)
  have hSsub : S ⊆ x1 := Finset.filter_subset _ _
  have hS : ∀ a ∈ S, x3 ≤ x2 a := fun a ha => le_of_lt (Finset.mem_filter.mp ha).2
  have hcard : (S.card : ℝ) * x3 ≤ ∑ a ∈ S, x2 a := by
    calc (S.card : ℝ) * x3 = ∑ _a ∈ S, x3 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ a ∈ S, x2 a := Finset.sum_le_sum hS
  have hsub : (∑ a ∈ S, x2 a) ≤ ∑ a ∈ x1, x2 a :=
    Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun a ha _ => hnonneg a ha)
  have h1 : (S.card : ℝ) * x3 * x4 ≤ (∑ a ∈ x1, x2 a) * x4 :=
    mul_le_mul_of_nonneg_right (le_trans hcard hsub) hx4
  have h2 : x3 * ((S.card : ℝ) * x4) ≤ x3 * x5 := by
    calc x3 * ((S.card : ℝ) * x4) = (S.card : ℝ) * x3 * x4 := by ring
      _ ≤ (∑ a ∈ x1, x2 a) * x4 := h1
      _ ≤ x3 * x5 := hsum
  refine ⟨S, hSsub, le_of_mul_le_mul_left h2 hx3, ?_⟩
  intro a ha hnot
  by_contra h
  exact hnot (Finset.mem_filter.mpr ⟨ha, not_le.mp h⟩)

end Conjectures.Cuts.Task9af5a49dc4a0c1dfbbd64ad9_aux

theorem Conjectures.Cuts.Task9af5a49dc4a0c1dfbbd64ad9 :
∀ (x1 : Finset ℕ) (x2 : ℕ → ℝ) (x3 x4 x5 : ℝ), (0 : ℝ) < x3 → (0 : ℝ) ≤ x4 → (∀ x8 ∈ x1, (0 : ℝ) ≤ x2 x8) → (∑ x9 ∈ x1, x2 x9) * x4 ≤ x3 * x5 → ∃ x10 ⊆ x1, ↑x10.card * x4 ≤ x5 ∧ ∀ x11 ∈ x1, x11 ∉ x10 → x2 x11 ≤ x3 :=
  Conjectures.Cuts.Task9af5a49dc4a0c1dfbbd64ad9_aux.main
