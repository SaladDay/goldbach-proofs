import Mathlib

/-!
# Cut premise 1/2 of `L-goldbach-local-density-half-endpoint`

If for every shift `h > 0` and every `ε > 0` the number of `a ≤ x` with `a, a + h` both in
`A` is eventually at most `ε x`, then `A` itself has density `0`: for every `ε > 0` eventually
`#(A ∩ [1, x]) ≤ ε x`.

The proof is a pigeonhole on a finite set of shifts.  Fix `d > 0` and put `m = ⌈2 / d⌉`.
If `S = A ∩ [1, x]` has more than `d x` elements, then the elements of `S` that have no
neighbour in `S` within distance `m` are pairwise more than `m` apart, so there are at most
`x / (m + 1) + 1` of them; the remaining ones each produce a pair at some distance `h ∈ [1, m]`.
Hence `Σ_{h ∈ [1,m]} #{a ∈ S : a + h ∈ S} > d x / 4`, so one shift `h ∈ [1, m]` already has
more than `d x / (4 m)` pairs.  Taking the maximum of the finitely many thresholds supplied by
the premise over `h ∈ [1, m]` and then a large `x` with `#S > d x` gives the contradiction.

Self-contained: Mathlib only.
-/

namespace Conjectures.Cuts.Task7f8d442fa7dc85f8d9180c28_aux

open Finset

private lemma card_bound (S : Finset ℕ) (m x : ℕ) (hS : ∀ a ∈ S, 1 ≤ a ∧ a ≤ x) :
    S.card ≤ x / (m + 1) + 1 + ∑ h ∈ Finset.Icc 1 m, (S.filter (fun a => a + h ∈ S)).card := by
  classical
  set S' : Finset ℕ := S.filter (fun a => ∀ h ∈ Finset.Icc 1 m, a + h ∉ S)
  set T : Finset ℕ := S.filter (fun a => ∃ h ∈ Finset.Icc 1 m, a + h ∈ S)
  have hsub : S ⊆ S' ∪ T := by
    intro a ha
    by_cases hh : ∀ h ∈ Finset.Icc 1 m, a + h ∉ S
    · exact mem_union_left _ (mem_filter.mpr ⟨ha, hh⟩)
    · push Not at hh
      exact mem_union_right _ (mem_filter.mpr ⟨ha, hh⟩)
  have hT : T ⊆ (Finset.Icc 1 m).biUnion (fun h => S.filter (fun a => a + h ∈ S)) := by
    intro a ha
    obtain ⟨haS, h, hh, hah⟩ := mem_filter.mp ha
    exact mem_biUnion.mpr ⟨h, hh, mem_filter.mpr ⟨haS, hah⟩⟩
  have hcardT : T.card ≤ ∑ h ∈ Finset.Icc 1 m, (S.filter (fun a => a + h ∈ S)).card :=
    (card_le_card hT).trans card_biUnion_le
  have key : ∀ {u v : ℕ}, u ∈ S' → v ∈ S' → u < v → m + 1 ≤ v - u := by
    intro u v hu hv huv
    have hu' := mem_filter.mp hu
    have hv' := mem_filter.mp hv
    by_contra hlt
    have h1 : 1 ≤ v - u := by omega
    have h2 : v - u ≤ m := by omega
    have h3 : u + (v - u) ∈ S := by
      have : u + (v - u) = v := Nat.add_sub_of_le (le_of_lt huv)
      rw [this]
      exact hv'.1
    exact hu'.2 (v - u) (mem_Icc.mpr ⟨h1, h2⟩) h3
  have hinj : Set.InjOn (fun a : ℕ => a / (m + 1)) (S' : Set ℕ) := by
    intro a ha b hb heq
    rw [mem_coe] at ha hb
    dsimp only at heq
    rcases eq_or_ne a b with rfl | hne
    · rfl
    · exfalso
      rcases lt_or_gt_of_ne hne with h1 | h1
      · have hk : m + 1 ≤ b - a := key ha hb h1
        have h2 : a + (m + 1) ≤ b := by omega
        have h3 : (a + (m + 1)) / (m + 1) ≤ b / (m + 1) := Nat.div_le_div_right h2
        rw [Nat.add_div_right _ (by omega : 0 < m + 1)] at h3
        omega
      · have hk : m + 1 ≤ a - b := key hb ha h1
        have h2 : b + (m + 1) ≤ a := by omega
        have h3 : (b + (m + 1)) / (m + 1) ≤ a / (m + 1) := Nat.div_le_div_right h2
        rw [Nat.add_div_right _ (by omega : 0 < m + 1)] at h3
        omega
  have hScard : S'.card ≤ x / (m + 1) + 1 := by
    have himg : (S'.image (fun a : ℕ => a / (m + 1))).card = S'.card := card_image_of_injOn hinj
    have hsub2 : S'.image (fun a : ℕ => a / (m + 1)) ⊆ Finset.range (x / (m + 1) + 1) := by
      intro y hy
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
      have hax := hS a (mem_filter.mp ha).1
      rw [mem_range]
      have : a / (m + 1) ≤ x / (m + 1) := Nat.div_le_div_right hax.2
      omega
    calc S'.card = (S'.image (fun a : ℕ => a / (m + 1))).card := himg.symm
      _ ≤ (Finset.range (x / (m + 1) + 1)).card := card_le_card hsub2
      _ = x / (m + 1) + 1 := card_range _
  calc S.card ≤ (S' ∪ T).card := card_le_card hsub
    _ ≤ S'.card + T.card := card_union_le _ _
    _ ≤ (x / (m + 1) + 1) + ∑ h ∈ Finset.Icc 1 m, (S.filter (fun a => a + h ∈ S)).card :=
      Nat.add_le_add hScard hcardT

theorem main (A : Set ℕ)
    (hA : ∀ (x2 : ℕ), (0 : ℕ) < x2 → ∀ (x4 : ℝ), (0 : ℝ) < x4 → ∃ (x6 : ℕ), ∀ x7 ≥ x6,
      ((Set.Icc (1 : ℕ) x7 ∩ {x9 : ℕ | x9 ∈ A ∧ x9 + x2 ∈ A}).ncard : ℝ) ≤ x4 * (x7 : ℝ))
    (x3 : ℝ) (hx3 : (0 : ℝ) < x3) :
    ∃ (x5 : ℕ), ∀ x6 ≥ x5, ((Set.Icc (1 : ℕ) x6 ∩ A).ncard : ℝ) ≤ x3 * (x6 : ℝ) := by
  classical
  by_contra h
  push Not at h
  let m : ℕ := ⌈2 / x3⌉₊
  have hm1 : 1 ≤ m := Nat.ceil_pos.mpr (by positivity)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm2 : (2 : ℝ) / x3 ≤ (m : ℝ) := Nat.le_ceil _
  have hkey : (2 : ℝ) ≤ x3 * ((m : ℝ) + 1) := by
    have h1 := mul_le_mul_of_nonneg_left
      (le_trans hm2 (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)) hx3.le
    have h2 : x3 * (2 / x3) = 2 := by field_simp
    linarith
  have hdiv : (1 : ℝ) / ((m : ℝ) + 1) ≤ x3 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  let x4 : ℝ := x3 / (4 * (m : ℝ))
  have hx4 : (0 : ℝ) < x4 := div_pos hx3 (by positivity)
  have hpre : ∀ h : ℕ, ∃ N : ℕ, h ∈ Finset.Icc 1 m → ∀ x7 ≥ N,
      ((Set.Icc (1 : ℕ) x7 ∩ {x9 : ℕ | x9 ∈ A ∧ x9 + h ∈ A}).ncard : ℝ) ≤ x4 * (x7 : ℝ) := by
    intro h
    by_cases hh : h ∈ Finset.Icc 1 m
    · obtain ⟨N, hN⟩ := hA h (by have := (mem_Icc.mp hh).1; omega) x4 hx4
      exact ⟨N, fun _ => hN⟩
    · exact ⟨0, fun h2 => absurd h2 hh⟩
  choose N hN using hpre
  let N0 : ℕ := (Finset.Icc 1 m).sup N
  obtain ⟨x, hxN, hxd⟩ := h (max N0 ⌈4 / x3⌉₊)
  have hxN' : N0 ≤ x := le_trans (le_max_left _ _) hxN
  have hx4' : (4 : ℝ) / x3 ≤ (x : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_right N0 ⌈4 / x3⌉₊) hxN)
  have hx4x : (4 : ℝ) ≤ x3 * (x : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_left hx4' hx3.le
    have h2 : x3 * (4 / x3) = 4 := by field_simp
    linarith
  set s : Set ℕ := Set.Icc (1 : ℕ) x ∩ A
  have hfin : s.Finite := by
    refine (Finset.finite_toSet (Finset.Icc 1 x)).subset ?_
    intro a ha
    exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ha.1)
  set S : Finset ℕ := s.toFinset
  have hScard : (S.card : ℝ) = (s.ncard : ℝ) := by
    have h1 : (S : Set ℕ) = s := by simp [S]
    rw [← h1, Set.ncard_coe_finset]
  have hSmem : ∀ a ∈ S, 1 ≤ a ∧ a ≤ x := by
    intro a ha
    have ha' : a ∈ s := by simpa [S] using ha
    exact ha'.1
  have hcb := card_bound S m x hSmem
  have hcast : (S.card : ℝ) ≤ (x : ℝ) / ((m : ℝ) + 1) + 1 +
      ∑ h ∈ Finset.Icc 1 m, ((S.filter (fun a => a + h ∈ S)).card : ℝ) := by
    have h1 : (S.card : ℝ) ≤ ((x / (m + 1) + 1 +
        ∑ h ∈ Finset.Icc 1 m, (S.filter (fun a => a + h ∈ S)).card : ℕ) : ℝ) := by
      exact_mod_cast hcb
    have h2 : ((x / (m + 1) : ℕ) : ℝ) ≤ (x : ℝ) / ((m : ℝ) + 1) := by
      simpa using Nat.cast_div_le (α := ℝ) (m := x) (n := m + 1)
    push_cast at h1
    linarith
  have hdivx : (x : ℝ) / ((m : ℝ) + 1) ≤ x3 * (x : ℝ) / 2 := by
    calc (x : ℝ) / ((m : ℝ) + 1) = (x : ℝ) * (1 / ((m : ℝ) + 1)) := by ring
      _ ≤ (x : ℝ) * (x3 / 2) := mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg x)
      _ = x3 * (x : ℝ) / 2 := by ring
  have hsum : x3 * (x : ℝ) / 4 <
      ∑ h ∈ Finset.Icc 1 m, ((S.filter (fun a => a + h ∈ S)).card : ℝ) := by
    linarith
  have hex : ∃ h ∈ Finset.Icc 1 m,
      x3 * (x : ℝ) / (4 * (m : ℝ)) < ((S.filter (fun a => a + h ∈ S)).card : ℝ) := by
    by_contra! hall
    have h1 : ∑ h ∈ Finset.Icc 1 m, ((S.filter (fun a => a + h ∈ S)).card : ℝ) ≤
        ∑ _h ∈ Finset.Icc 1 m, x3 * (x : ℝ) / (4 * (m : ℝ)) := sum_le_sum fun h hh => hall h hh
    have hc : (Finset.Icc 1 m).card = m := by rw [Nat.card_Icc]; omega
    rw [sum_const, nsmul_eq_mul, hc] at h1
    have h2 : (m : ℝ) * (x3 * (x : ℝ) / (4 * (m : ℝ))) = x3 * (x : ℝ) / 4 := by
      field_simp
    linarith
  obtain ⟨h, hh, hgh⟩ := hex
  have hpos : 0 < h := by have := (mem_Icc.mp hh).1; omega
  set t : Set ℕ := Set.Icc (1 : ℕ) x ∩ {a : ℕ | a ∈ A ∧ a + h ∈ A}
  have hfinT : t.Finite := by
    refine (Finset.finite_toSet (Finset.Icc 1 x)).subset ?_
    intro a ha
    exact Finset.mem_coe.mpr (Finset.mem_Icc.mpr ha.1)
  have hsubS : ((S.filter (fun a => a + h ∈ S) : Finset ℕ) : Set ℕ) ⊆ t := by
    intro a ha
    have ha' := mem_filter.mp (mem_coe.mp ha)
    have h1 : a ∈ s := by simpa [S] using ha'.1
    have h2 : a + h ∈ s := by simpa [S] using ha'.2
    exact ⟨h1.1, h1.2, h2.2⟩
  have hncard : ((S.filter (fun a => a + h ∈ S)).card : ℝ) ≤ (t.ncard : ℝ) := by
    have h1 : (S.filter (fun a => a + h ∈ S)).card ≤ t.ncard := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsubS hfinT
    exact_mod_cast h1
  have hbad := hN h hh x (le_trans (Finset.le_sup (f := N) hh) hxN')
  have hx4x' : x4 * (x : ℝ) = x3 * (x : ℝ) / (4 * (m : ℝ)) := by
    dsimp [x4]; ring
  linarith


end Conjectures.Cuts.Task7f8d442fa7dc85f8d9180c28_aux

theorem Conjectures.Cuts.Task7f8d442fa7dc85f8d9180c28 :
∀ (x1 : Set ℕ), (∀ (x2 : ℕ), (0 : ℕ) < x2 → ∀ (x4 : ℝ), (0 : ℝ) < x4 → ∃ (x6 : ℕ), ∀ x7 ≥ x6, ↑(Set.Icc (1 : ℕ) x7 ∩ {x9 : ℕ | x9 ∈ x1 ∧ x9 + x2 ∈ x1}).ncard ≤ x4 * ↑x7) → ∀ (x3 : ℝ), (0 : ℝ) < x3 → ∃ (x5 : ℕ), ∀ x6 ≥ x5, ↑(Set.Icc (1 : ℕ) x6 ∩ x1).ncard ≤ x3 * ↑x6 := by
  intro x1 hx1 x3 hx3
  exact Conjectures.Cuts.Task7f8d442fa7dc85f8d9180c28_aux.main x1 hx1 x3 hx3
