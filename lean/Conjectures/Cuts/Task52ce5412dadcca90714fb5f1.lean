import Mathlib

/-!
# Signed weight minus total weight

Subtracting the signed sum from the unsigned sum extracts twice the weight of the
part carrying the negative sign.  Elementary `Finset` algebra: on the filtered set
`x3 = -1`, so `x2 - x2 * x3 = 2 * x2`, and off it `x2 - x2 * x3 = 0`.

Adapted from the `Finset.sum_filter` / `Finset.mul_sum` idiom used throughout the
accepted `repo/lean/Conjectures/Cuts` modules.
-/

namespace Conjectures.Cuts.Task52ce5412dadcca90714fb5f1_aux

lemma signed_sub_total (x1 : Finset ℕ) (x2 x3 : ℕ → ℤ) :
    ∑ x6 ∈ x1, x2 x6 - ∑ x6 ∈ x1, x2 x6 * x3 x6 = ∑ x6 ∈ x1, x2 x6 * (1 - x3 x6) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x6 _ => ?_)
  ring

lemma term_eq_ite (x2 x3 : ℕ → ℤ) (x4 : ℕ → Bool) (x6 : ℕ)
    (h : x3 x6 = if x4 x6 = Bool.true then (-1 : ℤ) else (1 : ℤ)) :
    x2 x6 * (1 - x3 x6) = if x4 x6 = Bool.true then (2 : ℤ) * x2 x6 else 0 := by
  rw [h]
  split_ifs <;> ring

end Conjectures.Cuts.Task52ce5412dadcca90714fb5f1_aux

theorem Conjectures.Cuts.Task52ce5412dadcca90714fb5f1 :
    ∀ (x1 : Finset ℕ) (x2 x3 : ℕ → ℤ) (x4 : ℕ → Bool),
      (∀ x5 ∈ x1, x3 x5 = if x4 x5 = Bool.true then (-1 : ℤ) else (1 : ℤ)) →
      ∑ x6 ∈ x1, x2 x6 - ∑ x6 ∈ x1, x2 x6 * x3 x6 =
        (2 : ℤ) * ∑ x6 ∈ x1 with x4 x6 = Bool.true, x2 x6 := by
  intro x1 x2 x3 x4 h
  rw [Conjectures.Cuts.Task52ce5412dadcca90714fb5f1_aux.signed_sub_total]
  have h2 : ∀ x6 ∈ x1, x2 x6 * (1 - x3 x6) = if x4 x6 = Bool.true then (2 : ℤ) * x2 x6 else 0 :=
    fun x6 hx6 => Conjectures.Cuts.Task52ce5412dadcca90714fb5f1_aux.term_eq_ite x2 x3 x4 x6 (h x6 hx6)
  rw [Finset.sum_congr rfl h2, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x6 _ => ?_)
  split_ifs <;> ring
