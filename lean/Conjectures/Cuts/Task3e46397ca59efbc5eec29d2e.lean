import Mathlib

/-!
# Premise 1/2 of the cut `L-goldbach-cut-d114212d6c52bf3acc0a2d0c`

The statement bounds, for a polynomial `P` of degree at least `3` and a positive exponent `x4`,
the sixth-moment energy of the truncated exponential sum over `x10 ⊆ Finset.Icc 1 x7` by
`x6 * x7 ^ x4 * x10.card ^ 3` for some constant `x6 > 0` depending on `P` and `x4`.

The formal statement pins the range of `x7` by `2 ≤ x7 → x7 ≤ 2`, so only `x7 = 2` occurs and
the set `x10` ranges over the finitely many subsets of `Finset.Icc 1 2 = {1, 2}`.  Hence no
analytic estimate is needed: the constant is taken as `1` plus the (finite) sum, over those
subsets, of the normalised absolute value of the corresponding energy integral.  For `x10 = ∅`
the integrand vanishes identically, so the right-hand side `x6 * 2 ^ x4 * 0` is `0` as well.
-/

open scoped BigOperators

namespace Conjectures.Cuts.Task3e46397ca59efbc5eec29d2e_aux

/-- The truncated exponential sum attached to a polynomial and a finite set. -/
noncomputable def trunc (P : Polynomial ℤ) (s : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ x4 : ↥s, Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑(Polynomial.eval (↑↑x4) P) * ↑t)

/-- The energy integral of the cut. -/
noncomputable def energy (P : Polynomial ℤ) (s : Finset ℕ) : ℝ :=
  ∫ (x12 : ℝ) in (0 : ℝ)..(1 : ℝ), Max.max (0 : ℝ)
    (‖trunc P s x12‖ ^ (6 : ℕ) - (s.card : ℝ) ^ (2 : ℕ) * ‖trunc P s x12‖ ^ (2 : ℕ))

lemma energy_empty (P : Polynomial ℤ) : energy P ∅ = 0 := by
  unfold energy trunc
  simp

end Conjectures.Cuts.Task3e46397ca59efbc5eec29d2e_aux

open Conjectures.Cuts.Task3e46397ca59efbc5eec29d2e_aux

theorem Conjectures.Cuts.Task3e46397ca59efbc5eec29d2e :
    have x1 : Polynomial ℤ → Finset ℕ → ℝ → ℂ := fun (x1 : Polynomial ℤ) (x2 : Finset ℕ) (x3 : ℝ) => ∑ x4 : ↥x2, Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑(Polynomial.eval (↑↑x4) x1) * ↑x3); ∀ (x2 : Polynomial ℤ), (3 : ℕ) ≤ x2.natDegree → ∀ (x4 : ℝ), (0 : ℝ) < x4 → ∃ (x6 : ℝ), (0 : ℝ) < x6 ∧ ∀ (x7 : ℕ), (2 : ℕ) ≤ x7 → x7 ≤ (2 : ℕ) → ∀ x10 ⊆ Finset.Icc (1 : ℕ) x7, ∫ (x12 : ℝ) in (0 : ℝ)..(1 : ℝ), Max.max (0 : ℝ) (‖x1 x2 x10 x12‖ ^ (6 : ℕ) - ↑x10.card ^ (2 : ℕ) * ‖x1 x2 x10 x12‖ ^ (2 : ℕ)) ≤ x6 * ↑x7 ^ x4 * ↑x10.card ^ (3 : ℕ) := by
  dsimp only
  intro x2 _ x4 _
  change ∃ x6 : ℝ, 0 < x6 ∧ ∀ (x7 : ℕ), 2 ≤ x7 → x7 ≤ 2 →
    ∀ x10 ⊆ Finset.Icc 1 x7,
      energy x2 x10 ≤ x6 * (x7 : ℝ) ^ x4 * (x10.card : ℝ) ^ (3 : ℕ)
  refine ⟨1 + ∑ s ∈ (Finset.Icc (1 : ℕ) 2).powerset,
    |energy x2 s| / ((2 : ℝ) ^ x4 * (s.card : ℝ) ^ (3 : ℕ)), ?_, ?_⟩
  · have h : 0 ≤ ∑ s ∈ (Finset.Icc (1 : ℕ) 2).powerset,
        |energy x2 s| / ((2 : ℝ) ^ x4 * (s.card : ℝ) ^ (3 : ℕ)) :=
      Finset.sum_nonneg (fun s _ => div_nonneg (abs_nonneg _) (by positivity))
    linarith
  · intro x7 h1 h2 x10 hsub
    have h72 : x7 = 2 := by omega
    subst h72
    have hmem : x10 ∈ (Finset.Icc (1 : ℕ) 2).powerset := Finset.mem_powerset.mpr hsub
    have hle : |energy x2 x10| / ((2 : ℝ) ^ x4 * (x10.card : ℝ) ^ (3 : ℕ)) ≤
        1 + ∑ s ∈ (Finset.Icc (1 : ℕ) 2).powerset,
          |energy x2 s| / ((2 : ℝ) ^ x4 * (s.card : ℝ) ^ (3 : ℕ)) := by
      have h := Finset.single_le_sum
        (f := fun s : Finset ℕ => |energy x2 s| / ((2 : ℝ) ^ x4 * (s.card : ℝ) ^ (3 : ℕ)))
        (fun s _ => div_nonneg (abs_nonneg _) (by positivity)) hmem
      linarith
    by_cases hc : x10.card = 0
    · have hE : x10 = ∅ := Finset.card_eq_zero.mp hc
      subst hE
      rw [energy_empty]
      simp
    · have hcp : (0 : ℝ) < (x10.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hc
      have hd : (0 : ℝ) < (2 : ℝ) ^ x4 * (x10.card : ℝ) ^ (3 : ℕ) := by positivity
      have hb := (div_le_iff₀ hd).mp hle
      calc energy x2 x10 ≤ |energy x2 x10| := le_abs_self _
        _ ≤ (1 + ∑ s ∈ (Finset.Icc (1 : ℕ) 2).powerset,
              |energy x2 s| / ((2 : ℝ) ^ x4 * (s.card : ℝ) ^ (3 : ℕ))) *
            ((2 : ℝ) ^ x4 * (x10.card : ℝ) ^ (3 : ℕ)) := hb
        _ = (1 + ∑ s ∈ (Finset.Icc (1 : ℕ) 2).powerset,
              |energy x2 s| / ((2 : ℝ) ^ x4 * (s.card : ℝ) ^ (3 : ℕ))) *
            (2 : ℝ) ^ x4 * (x10.card : ℝ) ^ (3 : ℕ) := by ring
