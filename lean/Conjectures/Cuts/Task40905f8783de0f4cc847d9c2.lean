import Mathlib

/-!
Double counting identity (combinatorial extraction) for two exponent bands.

For `m` in the dyadic window `[x1, 2 * x1)` write `J₁ m` for the number of exponents
`e ∈ [x2, x3]` with `m - 2 ^ e` prime and `J₂ m` for the number of `f ∈ [x4, x5]` with
`m - 2 ^ f` prime.  The sum `∑ m, J₁ m * J₂ m` counts triples `(m, e, f)`.

The map `(m, e, f) ↦ (e, f, m - 2 ^ e, m - 2 ^ f)` is a bijection onto the quadruples
`(e, f, p, q)` with `e ∈ [x2, x3]`, `f ∈ [x4, x5]`, `p, q < 2 * x1` prime,
`x1 ≤ p + 2 ^ e < 2 * x1` and `p + 2 ^ e = q + 2 ^ f`:

* well defined: `m - 2 ^ e` is prime, hence nonzero, hence `2 ^ e ≤ m`, so
  `m - 2 ^ e < m < 2 * x1` and `(m - 2 ^ e) + 2 ^ e = m`;
* injective: `p = m - 2 ^ e` and `2 ^ e ≤ m` recover `m = p + 2 ^ e`;
* surjective: given `(e, f, p, q)` take `m = p + 2 ^ e`; the equality `p + 2 ^ e = q + 2 ^ f`
  gives `m - 2 ^ f = q`, and `m - 2 ^ e = p`.

Each side is first rewritten as a cardinality of a filtered finset (`card_filter_cast`), then
the two cardinalities are identified with `Finset.card_bij`, and the two band counts are
expanded into a double sum with `Finset.sum_mul_sum` and reordered with `Finset.sum_comm`.

Self-contained: Mathlib only.  Method adapted from the fleet proofs of the sibling cuts
`L-goldbach-cut-a571f1c3077acc5aaa440e63` (block covering) and
`L-goldbach-cut-395ba02c0b7383d46aab4a6b` (filtered cardinality estimates), which use the same
`Finset` cardinality/`sum_congr` style.
-/

namespace Conjectures.Cuts.Task40905f8783de0f4cc847d9c2_aux

private lemma card_filter_cast {α : Type*} (s : Finset α) (P : α → Prop) [DecidablePred P] :
    ((s.filter P).card : ℝ) = ∑ a ∈ s, (if P a then (1 : ℝ) else 0) := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp

private lemma two_pow_le_of_prime_sub {m e : ℕ} (h : Nat.Prime (m - 2 ^ e)) : 2 ^ e ≤ m := by
  by_contra hlt
  have h1 : m < 2 ^ e := by omega
  have h0 : m - 2 ^ e = 0 := Nat.sub_eq_zero_of_le (le_of_lt h1)
  exact h.ne_zero h0

/-- The finite bijection `m ↦ (m - 2 ^ e, m - 2 ^ f)` for a fixed pair of exponents. -/
private lemma key (x1 e f : ℕ) :
    (∑ m ∈ Finset.Ico x1 (2 * x1),
        (if Nat.Prime (m - 2 ^ e) ∧ Nat.Prime (m - 2 ^ f) then (1 : ℝ) else 0))
      = ∑ p ∈ Finset.range (2 * x1), ∑ q ∈ Finset.range (2 * x1),
        (if Nat.Prime p ∧ Nat.Prime q ∧ x1 ≤ p + 2 ^ e ∧ p + 2 ^ e < 2 * x1 ∧
            p + 2 ^ e = q + 2 ^ f then (1 : ℝ) else 0) := by
  have hL : (∑ m ∈ Finset.Ico x1 (2 * x1),
        (if Nat.Prime (m - 2 ^ e) ∧ Nat.Prime (m - 2 ^ f) then (1 : ℝ) else 0)) =
      (((Finset.Ico x1 (2 * x1)).filter
        (fun m => Nat.Prime (m - 2 ^ e) ∧ Nat.Prime (m - 2 ^ f))).card : ℝ) :=
    (card_filter_cast (Finset.Ico x1 (2 * x1))
      (fun m => Nat.Prime (m - 2 ^ e) ∧ Nat.Prime (m - 2 ^ f))).symm
  have hR : (∑ p ∈ Finset.range (2 * x1), ∑ q ∈ Finset.range (2 * x1),
        (if Nat.Prime p ∧ Nat.Prime q ∧ x1 ≤ p + 2 ^ e ∧ p + 2 ^ e < 2 * x1 ∧
            p + 2 ^ e = q + 2 ^ f then (1 : ℝ) else 0)) =
      (((Finset.range (2 * x1) ×ˢ Finset.range (2 * x1)).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ x1 ≤ pq.1 + 2 ^ e ∧
          pq.1 + 2 ^ e < 2 * x1 ∧ pq.1 + 2 ^ e = pq.2 + 2 ^ f)).card : ℝ) := by
    have h1 : (∑ p ∈ Finset.range (2 * x1), ∑ q ∈ Finset.range (2 * x1),
          (if Nat.Prime p ∧ Nat.Prime q ∧ x1 ≤ p + 2 ^ e ∧ p + 2 ^ e < 2 * x1 ∧
            p + 2 ^ e = q + 2 ^ f then (1 : ℝ) else 0)) =
        ∑ pq ∈ Finset.range (2 * x1) ×ˢ Finset.range (2 * x1),
          (if Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ x1 ≤ pq.1 + 2 ^ e ∧
            pq.1 + 2 ^ e < 2 * x1 ∧ pq.1 + 2 ^ e = pq.2 + 2 ^ f then (1 : ℝ) else 0) :=
      (Finset.sum_product (Finset.range (2 * x1)) (Finset.range (2 * x1))
        (fun pq : ℕ × ℕ => if Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ x1 ≤ pq.1 + 2 ^ e ∧
            pq.1 + 2 ^ e < 2 * x1 ∧ pq.1 + 2 ^ e = pq.2 + 2 ^ f then (1 : ℝ) else 0)).symm
    rw [h1, ← card_filter_cast]
  have hcard : ((Finset.Ico x1 (2 * x1)).filter
        (fun m => Nat.Prime (m - 2 ^ e) ∧ Nat.Prime (m - 2 ^ f))).card =
      ((Finset.range (2 * x1) ×ˢ Finset.range (2 * x1)).filter
        (fun pq => Nat.Prime pq.1 ∧ Nat.Prime pq.2 ∧ x1 ≤ pq.1 + 2 ^ e ∧
          pq.1 + 2 ^ e < 2 * x1 ∧ pq.1 + 2 ^ e = pq.2 + 2 ^ f)).card := by
    refine Finset.card_bij (fun m _ => (m - 2 ^ e, m - 2 ^ f)) ?_ ?_ ?_
    · intro m hm
      obtain ⟨hmI, hp⟩ := Finset.mem_filter.mp hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hmI
      have he : 2 ^ e ≤ m := two_pow_le_of_prime_sub hp.1
      have hf : 2 ^ f ≤ m := two_pow_le_of_prime_sub hp.2
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, ?_⟩
      · exact lt_of_le_of_lt (Nat.sub_le m (2 ^ e)) hm2
      · exact lt_of_le_of_lt (Nat.sub_le m (2 ^ f)) hm2
      · refine ⟨hp.1, hp.2, ?_, ?_, ?_⟩
        · rw [Nat.sub_add_cancel he]; exact hm1
        · rw [Nat.sub_add_cancel he]; exact hm2
        · rw [Nat.sub_add_cancel he, Nat.sub_add_cancel hf]
    · intro m1 hm1 m2 hm2 h
      obtain ⟨_, hp1⟩ := Finset.mem_filter.mp hm1
      obtain ⟨_, hp2⟩ := Finset.mem_filter.mp hm2
      have he1 : 2 ^ e ≤ m1 := two_pow_le_of_prime_sub hp1.1
      have he2 : 2 ^ e ≤ m2 := two_pow_le_of_prime_sub hp2.1
      have hfst : m1 - 2 ^ e = m2 - 2 ^ e := congrArg Prod.fst h
      calc m1 = (m1 - 2 ^ e) + 2 ^ e := (Nat.sub_add_cancel he1).symm
        _ = (m2 - 2 ^ e) + 2 ^ e := by rw [hfst]
        _ = m2 := Nat.sub_add_cancel he2
    · intro b hb
      obtain ⟨hbT, hc⟩ := Finset.mem_filter.mp hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_product.mp hbT
      obtain ⟨hpp, hqq, hlo, hhi, heq⟩ := hc
      have hbe : b.1 + 2 ^ e - 2 ^ e = b.1 := Nat.add_sub_cancel_right b.1 (2 ^ e)
      have hbf : b.1 + 2 ^ e - 2 ^ f = b.2 := by
        rw [heq]; exact Nat.add_sub_cancel_right b.2 (2 ^ f)
      refine ⟨b.1 + 2 ^ e, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlo, hhi⟩, ?_⟩, ?_⟩
      · rw [hbe, hbf]; exact ⟨hpp, hqq⟩
      · ext
        · exact hbe
        · exact hbf
  rw [hL, hcard, hR]

end Conjectures.Cuts.Task40905f8783de0f4cc847d9c2_aux

theorem Conjectures.Cuts.Task40905f8783de0f4cc847d9c2 :
    ∀ (x1 x2 x3 x4 x5 : ℕ), ∑ x6 ∈ Finset.Ico x1 ((2 : ℕ) * x1), (↑{x7 ∈ Finset.Icc x2 x3 | Nat.Prime (x6 - (2 : ℕ) ^ x7)}.card : ℝ) * (↑{x7 ∈ Finset.Icc x4 x5 | Nat.Prime (x6 - (2 : ℕ) ^ x7)}.card : ℝ) = ∑ x6 ∈ Finset.Icc x2 x3, ∑ x7 ∈ Finset.Icc x4 x5, ∑ x8 ∈ Finset.range ((2 : ℕ) * x1), ∑ x9 ∈ Finset.range ((2 : ℕ) * x1), if Nat.Prime x8 ∧ Nat.Prime x9 ∧ x1 ≤ x8 + (2 : ℕ) ^ x6 ∧ x8 + (2 : ℕ) ^ x6 < (2 : ℕ) * x1 ∧ x8 + (2 : ℕ) ^ x6 = x9 + (2 : ℕ) ^ x7 then (↑(1 : ℕ) : ℝ) else (0 : ℝ) := by
  intro x1 x2 x3 x4 x5
  have hL : (∑ x6 ∈ Finset.Ico x1 ((2 : ℕ) * x1), (↑{x7 ∈ Finset.Icc x2 x3 | Nat.Prime (x6 - (2 : ℕ) ^ x7)}.card : ℝ) * (↑{x7 ∈ Finset.Icc x4 x5 | Nat.Prime (x6 - (2 : ℕ) ^ x7)}.card : ℝ)) =
      ∑ e ∈ Finset.Icc x2 x3, ∑ f ∈ Finset.Icc x4 x5, ∑ m ∈ Finset.Ico x1 ((2 : ℕ) * x1),
        (if Nat.Prime (m - 2 ^ e) ∧ Nat.Prime (m - 2 ^ f) then (1 : ℝ) else 0) := by
    calc (∑ x6 ∈ Finset.Ico x1 ((2 : ℕ) * x1), (↑{x7 ∈ Finset.Icc x2 x3 | Nat.Prime (x6 - (2 : ℕ) ^ x7)}.card : ℝ) * (↑{x7 ∈ Finset.Icc x4 x5 | Nat.Prime (x6 - (2 : ℕ) ^ x7)}.card : ℝ))
        = ∑ m ∈ Finset.Ico x1 ((2 : ℕ) * x1), ∑ e ∈ Finset.Icc x2 x3, ∑ f ∈ Finset.Icc x4 x5,
            (if Nat.Prime (m - 2 ^ e) ∧ Nat.Prime (m - 2 ^ f) then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [Conjectures.Cuts.Task40905f8783de0f4cc847d9c2_aux.card_filter_cast,
            Conjectures.Cuts.Task40905f8783de0f4cc847d9c2_aux.card_filter_cast,
            Finset.sum_mul_sum]
          refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun f _ => ?_))
          by_cases h1 : Nat.Prime (m - 2 ^ e) <;> by_cases h2 : Nat.Prime (m - 2 ^ f) <;>
            simp [h1, h2]
      _ = ∑ e ∈ Finset.Icc x2 x3, ∑ m ∈ Finset.Ico x1 ((2 : ℕ) * x1), ∑ f ∈ Finset.Icc x4 x5,
            (if Nat.Prime (m - 2 ^ e) ∧ Nat.Prime (m - 2 ^ f) then (1 : ℝ) else 0) :=
          Finset.sum_comm
      _ = ∑ e ∈ Finset.Icc x2 x3, ∑ f ∈ Finset.Icc x4 x5, ∑ m ∈ Finset.Ico x1 ((2 : ℕ) * x1),
            (if Nat.Prime (m - 2 ^ e) ∧ Nat.Prime (m - 2 ^ f) then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun e _ => ?_)
          exact Finset.sum_comm
  rw [hL]
  refine Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun f _ => ?_))
  simpa only [Nat.cast_one] using
    Conjectures.Cuts.Task40905f8783de0f4cc847d9c2_aux.key x1 e f
