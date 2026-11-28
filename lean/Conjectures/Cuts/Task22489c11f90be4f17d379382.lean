import Mathlib

/-!
# Cut `L-goldbach-cut-22489c11f90be4f17d379382`

Detect a symmetric index representation by its reflected count on the exact half interval.

For a predicate `x1 : ℕ → Bool` and a target `x2 ≥ 1`, put `n = x2 - 1`.  The left-hand
side asks for two indices `a, b` with `x1 a = x1 b = true` and `a + b = n`.  Such a pair is
symmetric under `a ↦ n - a`, so the smaller of the two indices satisfies
`2 * min a b ≤ n`, i.e. `min a b < n / 2 + 1`, and its reflection is the larger one; hence the
filtered set on the exact half interval `range (n / 2 + 1)` is nonempty.  Conversely any
element of that filtered set, together with its reflection `n - a`, is a pair of true indices
summing to `n` (the index is at most `n / 2 ≤ n`, so no truncation happens in `n - a`).

Self-contained: Mathlib only.
-/

namespace Conjectures.Cuts.Task22489c11f90be4f17d379382_aux

/-- The smaller index of a symmetric pair sits on the half interval and its reflection is the
larger one. -/
private lemma witness {x1 : ℕ → Bool} {n a b : ℕ} (ha : x1 a = Bool.true)
    (hb : x1 b = Bool.true) (hab : a + b = n) :
    ∃ m ∈ Finset.range (n / 2 + 1), x1 m = Bool.true ∧ x1 (n - m) = Bool.true := by
  rcases le_total a b with hle | hle
  · refine ⟨a, ?_, ha, ?_⟩
    · rw [Finset.mem_range]
      have h2 : 2 * a ≤ n := by omega
      have h3 : a ≤ n / 2 := by omega
      omega
    · have hba : n - a = b := by omega
      rw [hba]
      exact hb
  · refine ⟨b, ?_, hb, ?_⟩
    · rw [Finset.mem_range]
      have h2 : 2 * b ≤ n := by omega
      have h3 : b ≤ n / 2 := by omega
      omega
    · have hab' : n - b = a := by omega
      rw [hab']
      exact ha

end Conjectures.Cuts.Task22489c11f90be4f17d379382_aux

theorem Conjectures.Cuts.Task22489c11f90be4f17d379382 :
∀ (x1 : ℕ → Bool) (x2 : ℕ), (1 : ℕ) ≤ x2 → ((∃ (x4 : ℕ) (x5 : ℕ), x1 x4 = Bool.true ∧ x1 x5 = Bool.true ∧ x4 + x5 + (1 : ℕ) = x2) ↔ (0 : ℕ) < {x4 ∈ Finset.range ((x2 - (1 : ℕ)) / (2 : ℕ) + (1 : ℕ)) | x1 x4 = Bool.true ∧ x1 (x2 - (1 : ℕ) - x4) = Bool.true}.card) := by
  intro x1 x2 hx2
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    have hab' : a + b = x2 - (1 : ℕ) := by omega
    obtain ⟨m, hm, h1, h2⟩ :=
      Conjectures.Cuts.Task22489c11f90be4f17d379382_aux.witness ha hb hab'
    have hmem : m ∈ {x4 ∈ Finset.range ((x2 - (1 : ℕ)) / (2 : ℕ) + (1 : ℕ)) |
        x1 x4 = Bool.true ∧ x1 (x2 - (1 : ℕ) - x4) = Bool.true} :=
      Finset.mem_filter.mpr ⟨hm, h1, h2⟩
    exact Finset.card_pos.mpr ⟨m, hmem⟩
  · intro h
    obtain ⟨m, hm⟩ := Finset.card_pos.mp h
    obtain ⟨hmr, h1, h2⟩ := Finset.mem_filter.mp hm
    have hlt : m < (x2 - (1 : ℕ)) / (2 : ℕ) + (1 : ℕ) := Finset.mem_range.mp hmr
    have hmle : m ≤ x2 - (1 : ℕ) := by
      have h3 : m ≤ (x2 - (1 : ℕ)) / 2 := by omega
      omega
    refine ⟨m, x2 - (1 : ℕ) - m, h1, h2, ?_⟩
    omega
