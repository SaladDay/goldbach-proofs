import Mathlib

/-!
# Cut premise: at most `2 * √T * log₂ T` exceptional representations

For a target `T` the representations `T = a + b` with `a, b` both prime powers and at least one
of them composite are bounded by `2 * ⌊√T⌋ * ⌊log₂ T⌋`.

Method (self-contained, Mathlib only; the box count is the same as in the accepted module
`Conjectures.Goldbach.PowerBoxCard`, and the exponent/root bounds follow
`Conjectures.Goldbach.PowerIndexCount`):

* a composite prime power `n = p ^ j ≤ T` has `j ≥ 2`, hence `p ≤ √T` and `j ≤ log₂ T`, so the
  set `C` of composite prime powers `≤ T` injects into the image of the box
  `Icc 2 ⌊√T⌋ × Icc 2 ⌊log₂ T⌋`, whose cardinality is `(√T - 1)(log₂ T - 1) ≤ √T * log₂ T`;
* every exceptional representation has a composite end, so it lies in `A ∪ B` where
  `A = {a ≤ T composite prime power}` and `B = {a ≤ T : T - a composite prime power}`; the
  reflection `a ↦ T - a` is injective on `B` and lands in `A`, so `#B ≤ #A`.

Hence `#(A ∪ B) ≤ 2 * √T * log₂ T`.
-/

namespace Conjectures.Cuts.Task82241387be599407eb3b592e_aux

open Finset

/-- Composite prime powers in `[0, T]`. -/
private def compPP (T : ℕ) : Finset ℕ :=
  (Finset.range (T + 1)).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)

private lemma card_compPP (T : ℕ) : (compPP T).card ≤ Nat.sqrt T * Nat.log 2 T := by
  classical
  let B : Finset (ℕ × ℕ) :=
    (Finset.Icc 2 (Nat.sqrt T)).product (Finset.Icc 2 (Nat.log 2 T))
  have hsub : compPP T ⊆ B.image (fun z : ℕ × ℕ => z.1 ^ z.2) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnT : n ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn'.1)
    obtain ⟨p, j, hp, hj, hpj⟩ := hn'.2.1
    have hpN : Nat.Prime p := Nat.prime_iff.mpr hp
    have hj2 : 2 ≤ j := by
      by_contra h
      have hj1 : j = 1 := by omega
      subst j
      simp at hpj
      exact hn'.2.2 (hpj ▸ hpN)
    have hp2 : p ^ 2 ≤ T := by
      calc p ^ 2 ≤ p ^ j := pow_le_pow_right₀ (by exact_mod_cast Nat.Prime.one_le hpN) hj2
        _ = n := hpj
        _ ≤ T := hnT
    have hpsqrt : p ≤ Nat.sqrt T := (Nat.le_sqrt).mpr (by simpa [pow_two] using hp2)
    have h2j : 2 ^ j ≤ T := by
      calc 2 ^ j ≤ p ^ j := Nat.pow_le_pow_left (Nat.Prime.two_le hpN) j
        _ = n := hpj
        _ ≤ T := hnT
    have hjlog : j ≤ Nat.log 2 T := Nat.le_log_of_pow_le (by omega) h2j
    exact Finset.mem_image.mpr ⟨(p, j), Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.Prime.two_le hpN, hpsqrt⟩,
       Finset.mem_Icc.mpr ⟨hj2, hjlog⟩⟩, hpj⟩
  calc (compPP T).card ≤ (B.image (fun z : ℕ × ℕ => z.1 ^ z.2)).card := Finset.card_le_card hsub
    _ ≤ B.card := Finset.card_image_le
    _ = (Nat.sqrt T + 1 - 2) * (Nat.log 2 T + 1 - 2) := by
      simp [B, Finset.card_product]
    _ ≤ Nat.sqrt T * Nat.log 2 T :=
      Nat.mul_le_mul (by omega) (by omega)

private lemma card_refl (T : ℕ) :
    ((Finset.range (T + 1)).filter (fun a => IsPrimePow (T - a) ∧ ¬ Nat.Prime (T - a))).card ≤
      (compPP T).card := by
  classical
  set Bf : Finset ℕ :=
    (Finset.range (T + 1)).filter (fun a => IsPrimePow (T - a) ∧ ¬ Nat.Prime (T - a))
  have hinj : Set.InjOn (fun a : ℕ => T - a) (Bf : Set ℕ) := by
    intro a ha b hb heq
    have ha' := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
    have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
    have haT : a ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha'.1)
    have hbT : b ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb'.1)
    dsimp only at heq
    omega
  have hsub : Bf.image (fun a : ℕ => T - a) ⊆ compPP T := by
    intro m hm
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hm
    have ha' := Finset.mem_filter.mp ha
    have haT : a ≤ T := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha'.1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (by omega)),
      ha'.2⟩
  calc Bf.card = (Bf.image (fun a : ℕ => T - a)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ (compPP T).card := Finset.card_le_card hsub

theorem main (T : ℕ) :
    {x2 ∈ Finset.range (T + (1 : ℕ)) |
        IsPrimePow x2 ∧ IsPrimePow (T - x2) ∧ ¬(Nat.Prime x2 ∧ Nat.Prime (T - x2))}.card ≤
      (2 : ℕ) * T.sqrt * Nat.log (2 : ℕ) T := by
  classical
  let S : Finset ℕ := Finset.filter
    (fun x2 => IsPrimePow x2 ∧ IsPrimePow (T - x2) ∧ ¬(Nat.Prime x2 ∧ Nat.Prime (T - x2)))
    (Finset.range (T + 1))
  let Af : Finset ℕ := (Finset.range (T + 1)).filter (fun a => IsPrimePow a ∧ ¬ Nat.Prime a)
  let Bf : Finset ℕ :=
    (Finset.range (T + 1)).filter (fun a => IsPrimePow (T - a) ∧ ¬ Nat.Prime (T - a))
  have hsub : S ⊆ Af ∪ Bf := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    by_cases h : Nat.Prime a
    · have h2 : ¬ Nat.Prime (T - a) := fun hp => ha'.2.2.2 ⟨h, hp⟩
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha'.1, ha'.2.2.1, h2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha'.1, ha'.2.1, h⟩)
  have hA : Af = compPP T := rfl
  have hB : Bf.card ≤ (compPP T).card := card_refl T
  calc S.card ≤ (Af ∪ Bf).card := Finset.card_le_card hsub
    _ ≤ Af.card + Bf.card := Finset.card_union_le _ _
    _ ≤ (compPP T).card + (compPP T).card := by rw [hA]; exact Nat.add_le_add_left hB _
    _ = 2 * (compPP T).card := by omega
    _ ≤ 2 * (Nat.sqrt T * Nat.log 2 T) := Nat.mul_le_mul_left 2 (card_compPP T)
    _ = (2 : ℕ) * T.sqrt * Nat.log (2 : ℕ) T := by
      rw [Nat.mul_assoc]

end Conjectures.Cuts.Task82241387be599407eb3b592e_aux

theorem Conjectures.Cuts.Task82241387be599407eb3b592e :
    ∀ (x1 : ℕ), {x2 ∈ Finset.range (x1 + (1 : ℕ)) | IsPrimePow x2 ∧ IsPrimePow (x1 - x2) ∧ ¬(Nat.Prime x2 ∧ Nat.Prime (x1 - x2))}.card ≤ (2 : ℕ) * x1.sqrt * Nat.log (2 : ℕ) x1 := by
  intro x1
  exact Conjectures.Cuts.Task82241387be599407eb3b592e_aux.main x1
