import Mathlib

/-!
Choose the largest element of a finite set of breakpoints that does not exceed a
given phase.

Since `0` belongs to the set and the phase is nonnegative, the subset of
breakpoints at most the phase is nonempty, so it has a maximum `x5`.  That
maximum lies in the set, is nonnegative (it dominates `0`), is at most the
phase, and it is the largest breakpoint not exceeding the phase, so for every
breakpoint `x6` the comparisons `x6 ≤ x2` and `x6 ≤ x5` agree.
-/

namespace Conjectures.Cuts.Task740545f0057b16031735cbcd_aux

/-- The largest element of a finite set that is at most `t`, when `0` is in the
set and `0 ≤ t`. -/
theorem exists_max_predecessor (s : Finset ℝ) (t : ℝ) (h0 : (0 : ℝ) ∈ s)
    (ht : (0 : ℝ) ≤ t) :
    ∃ x5 ∈ s, (0 : ℝ) ≤ x5 ∧ x5 ≤ t ∧ ∀ x6 ∈ s, x6 ≤ t ↔ x6 ≤ x5 := by
  classical
  have h0F : (0 : ℝ) ∈ s.filter (fun x => x ≤ t) := Finset.mem_filter.mpr ⟨h0, ht⟩
  have hne : (s.filter (fun x => x ≤ t)).Nonempty := ⟨0, h0F⟩
  have hmem : (s.filter (fun x => x ≤ t)).max' hne ∈ s.filter (fun x => x ≤ t) :=
    Finset.max'_mem _ hne
  have hle : (0 : ℝ) ≤ (s.filter (fun x => x ≤ t)).max' hne :=
    Finset.le_max' _ 0 h0F
  refine ⟨(s.filter (fun x => x ≤ t)).max' hne, (Finset.mem_filter.mp hmem).1,
    hle, (Finset.mem_filter.mp hmem).2, ?_⟩
  intro x6 hx6
  constructor
  · intro hx6t
    exact Finset.le_max' _ x6 (Finset.mem_filter.mpr ⟨hx6, hx6t⟩)
  · intro hx6m
    exact hx6m.trans (Finset.mem_filter.mp hmem).2

end Conjectures.Cuts.Task740545f0057b16031735cbcd_aux

theorem Conjectures.Cuts.Task740545f0057b16031735cbcd :
    ∀ (x1 : Finset ℝ) (x2 : ℝ), (0 : ℝ) ∈ x1 → (0 : ℝ) ≤ x2 → ∃ x5 ∈ x1, (0 : ℝ) ≤ x5 ∧ x5 ≤ x2 ∧ ∀ x6 ∈ x1, x6 ≤ x2 ↔ x6 ≤ x5 := by
  intro x1 x2 h0 ht
  exact Conjectures.Cuts.Task740545f0057b16031735cbcd_aux.exists_max_predecessor x1 x2 h0 ht
