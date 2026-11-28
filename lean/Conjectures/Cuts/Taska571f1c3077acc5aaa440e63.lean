import Mathlib

/-!
Covering a filtered closed window by aligned half-open blocks with a uniform bound.

Every index `n` of the closed window `[x1, x1 + x2]` lies in the aligned half-open block
`[q * x3, (q + 1) * x3)` attached to its quotient `q = n / x3`, because
`n = x3 * (n / x3) + n % x3` with `n % x3 < x3`.  Division is monotone, so
`x1 ≤ n ≤ x1 + x2` forces `x1 / x3 ≤ q ≤ (x1 + x2) / x3`: the quotients of the window index
the blocks `Finset.Icc (x1 / x3) ((x1 + x2) / x3)`.

Hence the filtered window is contained in the union of the filtered blocks over that quotient
interval, so its cardinality is at most the sum of the block cardinalities
(`Finset.card_biUnion_le`), and each of those is at most `x5` by hypothesis.  Summing the
constant `x5` over the quotient interval gives the announced bound
`card (Icc ...) * x5` in `ℝ`.

Self-contained: Mathlib only.
-/

theorem Conjectures.Cuts.Taska571f1c3077acc5aaa440e63 :
    ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Bool) (x5 : ℝ), (0 : ℕ) < x3 → (∀ x7 ∈ Finset.Icc (x1 / x3) ((x1 + x2) / x3), ↑{x9 ∈ Finset.Ico (x7 * x3) ((x7 + (1 : ℕ)) * x3) | x4 x9 = Bool.true}.card ≤ x5) → ↑{x8 ∈ Finset.Icc x1 (x1 + x2) | x4 x8 = Bool.true}.card ≤ ↑(Finset.Icc (x1 / x3) ((x1 + x2) / x3)).card * x5 := by
  intro x1 x2 x3 x4 x5 hx3 h
  have hsub : {x8 ∈ Finset.Icc x1 (x1 + x2) | x4 x8 = Bool.true} ⊆
      (Finset.Icc (x1 / x3) ((x1 + x2) / x3)).biUnion
        (fun q => {x9 ∈ Finset.Ico (q * x3) ((q + (1 : ℕ)) * x3) | x4 x9 = Bool.true}) := by
    intro n hn
    obtain ⟨hnI, hpn⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hnI
    have hdiv : x3 * (n / x3) + n % x3 = n := Nat.div_add_mod n x3
    have hmod : n % x3 < x3 := Nat.mod_lt n hx3
    have hmul : (n / x3 + 1) * x3 = x3 * (n / x3) + x3 := by ring
    rw [Finset.mem_biUnion]
    refine ⟨n / x3, Finset.mem_Icc.mpr ⟨?_, ?_⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, hpn⟩⟩
    · exact Nat.div_le_div_right hn1
    · exact Nat.div_le_div_right hn2
    · rw [mul_comm]; omega
    · rw [hmul]; omega
  have hcard : ({x8 ∈ Finset.Icc x1 (x1 + x2) | x4 x8 = Bool.true}).card ≤
      ∑ q ∈ Finset.Icc (x1 / x3) ((x1 + x2) / x3),
        ({x9 ∈ Finset.Ico (q * x3) ((q + (1 : ℕ)) * x3) | x4 x9 = Bool.true}).card :=
    le_trans (Finset.card_le_card hsub)
      (Finset.card_biUnion_le)
  calc ((↑({x8 ∈ Finset.Icc x1 (x1 + x2) | x4 x8 = Bool.true}).card : ℕ) : ℝ)
      ≤ ∑ q ∈ Finset.Icc (x1 / x3) ((x1 + x2) / x3),
          ((↑({x9 ∈ Finset.Ico (q * x3) ((q + (1 : ℕ)) * x3) | x4 x9 = Bool.true}).card : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ ∑ _q ∈ Finset.Icc (x1 / x3) ((x1 + x2) / x3), x5 :=
        Finset.sum_le_sum (fun q hq => h q hq)
    _ = ((↑(Finset.Icc (x1 / x3) ((x1 + x2) / x3)).card : ℕ) : ℝ) * x5 := by
        rw [Finset.sum_const, nsmul_eq_mul]
