import Mathlib

/-!
Bounded base segment: there is a threshold from which the representation count of
`2 * x2 ^ 6` stays positive up to `x2 = 8`.

The quantifier is `∃ x1, ∀ x2, x1 ≤ x2 → x2 ≤ 8 → ...`, so the largest admissible
threshold is `x1 = 8`: the remaining obligation is the single finite case `x2 = 8`,
i.e. the Goldbach representation `2 * 8 ^ 6 = 524288 = 19 + 524269` with both
summands prime.  The certificate is `19 ∈ Finset.range (2 * 8 ^ 6 + 1)` together with
`Nat.Prime 19` and `Nat.Prime 524269`, so the filtered finset is nonempty.

Self-contained: Mathlib only.
-/

theorem Conjectures.Cuts.Task07038f2192dc1e35b91d766a :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ), x1 ≤ x2 → x2 ≤ (8 : ℕ) → (0 : ℕ) < {x5 ∈ Finset.range ((2 : ℕ) * x2 ^ (6 : ℕ) + (1 : ℕ)) | Nat.Prime x5 ∧ Nat.Prime ((2 : ℕ) * x2 ^ (6 : ℕ) - x5)}.card := by
  refine ⟨8, ?_⟩
  intro x2 hx1 hx2
  have hx2eq : x2 = 8 := le_antisymm hx2 hx1
  subst hx2eq
  have hmem : (19 : ℕ) ∈ Finset.filter
      (fun x5 => Nat.Prime x5 ∧ Nat.Prime ((2 : ℕ) * (8 : ℕ) ^ (6 : ℕ) - x5))
      (Finset.range ((2 : ℕ) * (8 : ℕ) ^ (6 : ℕ) + (1 : ℕ))) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · norm_num [Finset.mem_range]
    · refine ⟨by norm_num, ?_⟩
      have hsub : (2 : ℕ) * (8 : ℕ) ^ (6 : ℕ) - 19 = 524269 := by norm_num
      rw [hsub]
      norm_num
  exact Finset.card_pos.mpr ⟨19, hmem⟩
