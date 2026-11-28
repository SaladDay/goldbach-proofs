import Mathlib

/-!
Cut lemma for the no-three-in-line problem.

A finite set of points with pairwise distinct ranks has size at most two as soon as
every member has at most one higher-ranked member.  Take the member `a` of minimal
rank; by injectivity every other member has strictly larger rank, so the filter of
higher-ranked members is exactly `x2.erase a`, and its cardinality bound gives
`x2.card - 1 ≤ 1`.
-/

theorem Conjectures.Cuts.Task0d959ecd730c507b73e49e2c :
∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin (4 : ℕ))) (x3 : Fin x1 × Fin (4 : ℕ) → ℕ), Function.Injective x3 → (∀ x5 ∈ x2, {x7 ∈ x2 | x3 x5 < x3 x7}.card ≤ (1 : ℕ)) → x2.card ≤ (2 : ℕ) := by
  intro x1 x2 x3 hinj h
  by_cases hne : x2.Nonempty
  · obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image x2 x3 hne
    have hcard := h a ha
    have heq : {x7 ∈ x2 | x3 a < x3 x7} = x2.erase a := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hy, hlt⟩
        exact ⟨fun hya => by rw [hya] at hlt; exact lt_irrefl _ hlt, hy⟩
      · rintro ⟨hne, hy⟩
        refine ⟨hy, ?_⟩
        exact lt_of_le_of_ne (hmin y hy) (fun h => hne (hinj h.symm))
    rw [heq, Finset.card_erase_of_mem ha] at hcard
    have hpos : 0 < x2.card := Finset.card_pos.mpr hne
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]
