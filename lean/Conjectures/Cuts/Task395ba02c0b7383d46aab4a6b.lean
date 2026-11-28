import Mathlib

/-!
Reindexing a bounded filtered progression through the quotient by the modulus.

The elements `n` of `[x1, x2]` with `n % x3 = x4` (where `x4 < x3`) are exactly the numbers
`n = x3 * q + x4`, with `q = n / x3`; the map `n ↦ n / x3` is therefore injective on them, and it
carries the extra filter `x5 (n / x3)` to the filter `x5 q` on the quotients.

The interval condition translates as

* `x1 ≤ x3 * q + x4 ↔ x1 - x4 ≤ x3 * q ↔ (x1 - x4) ⌈/⌉ x3 ≤ q`
  (`ceilDiv_le_iff_le_mul`);
* `x3 * q + x4 ≤ x2 ↔ x3 * q < x2 + 1 - x4 ↔ q < (x2 + 1 - x4) ⌈/⌉ x3`
  (the auxiliary `lt_ceilDiv_iff`, from `Nat.ceilDiv_eq_add_pred_div` and
  `Nat.lt_div_iff_mul_lt`).

Truncated subtraction is harmless: if `x4 > x2` the upper ceiling is `0` and both sides are
empty.  Self-contained: Mathlib only, one auxiliary lemma.
-/

namespace Conjectures.Cuts.Task395ba02c0b7383d46aab4a6b_aux

/-- Strict inequality against a ceiling division, for a positive divisor. -/
lemma lt_ceilDiv_iff {d m q : ℕ} (hd : 0 < d) : q < m ⌈/⌉ d ↔ d * q < m := by
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.lt_div_iff_mul_lt hd]
  have h : m + d - 1 - (d - 1) = m := by omega
  rw [h, mul_comm]

end Conjectures.Cuts.Task395ba02c0b7383d46aab4a6b_aux

theorem Conjectures.Cuts.Task395ba02c0b7383d46aab4a6b :
    ∀ (x1 x2 x3 x4 : ℕ) (x5 : ℕ → Bool), (0 : ℕ) < x3 → x4 < x3 → {x8 ∈ Finset.Icc x1 x2 | x8 % x3 = x4 ∧ x5 (x8 / x3) = Bool.true}.card = {x8 ∈ Finset.Ico ((x1 - x4) ⌈/⌉ x3) ((x2 + (1 : ℕ) - x4) ⌈/⌉ x3) | x5 x8 = Bool.true}.card := by
  intro x1 x2 x3 x4 x5 hx3 hx4
  refine Finset.card_bij (fun (n : ℕ) _ => n / x3) ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnI, hmod, hx5⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hnI
    have hdiv : x3 * (n / x3) + x4 = n := by
      have := Nat.div_add_mod n x3
      omega
    have hlo : x1 - x4 ≤ x3 * (n / x3) := by omega
    have hhi : x3 * (n / x3) < x2 + 1 - x4 := by omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩, hx5⟩
    · exact (ceilDiv_le_iff_le_mul hx3).mpr hlo
    · exact (Conjectures.Cuts.Task395ba02c0b7383d46aab4a6b_aux.lt_ceilDiv_iff hx3).mpr hhi
  · intro a ha b hb hab
    obtain ⟨_, hmoda, _⟩ := Finset.mem_filter.mp ha
    obtain ⟨_, hmodb, _⟩ := Finset.mem_filter.mp hb
    have ha' : x3 * (a / x3) + x4 = a := by
      have := Nat.div_add_mod a x3
      omega
    have hb' : x3 * (b / x3) + x4 = b := by
      have := Nat.div_add_mod b x3
      omega
    rw [hab] at ha'
    omega
  · intro q hq
    obtain ⟨hqI, hx5⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqlo, hqhi⟩ := Finset.mem_Ico.mp hqI
    have hlo : x1 - x4 ≤ x3 * q := (ceilDiv_le_iff_le_mul hx3).mp hqlo
    have hhi : x3 * q < x2 + 1 - x4 :=
      (Conjectures.Cuts.Task395ba02c0b7383d46aab4a6b_aux.lt_ceilDiv_iff hx3).mp hqhi
    have hmod : (x3 * q + x4) % x3 = x4 := by
      rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx4]
    have hdiv : (x3 * q + x4) / x3 = q := by
      rw [add_comm, Nat.add_mul_div_left _ _ hx3, Nat.div_eq_of_lt hx4, zero_add]
    refine ⟨x3 * q + x4, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hmod, ?_⟩, ?_⟩
    · rw [hdiv]
      exact hx5
    · exact hdiv
