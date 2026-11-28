import Conjectures.Goldbach.FareyInitialSieveLower

/-!
# Cut `L-goldbach-cut-b1827754475dd720a041a0cb`

For every sufficiently large even `n`, the number of central candidates `u` with both
`u` and `n - u` in the original candidate set and with at least one of `u`, `n - u` a
perfect square is at most `1/100` of the sieve volume `x4 n`.

Method.  The square condition pins `u` to a value `p^2` or `n - p^2` with `p ≤ √n`, so
the counted set has at most `2(√n + 1)` elements.  The sieve volume `x4 n` is exactly
`FareyBrun.mainTerm n n.sqrt`, which by `FareyBrun.terminal_floor_power` (adapted from
`Conjectures.Goldbach.FareyInitialSieveLower`, itself using the terminal floor of
`Conjectures.Goldbach.FareySieveTerminalFloor`) dominates `c n^(7/8)` for a fixed
`c > 0`.  Since `n^(7/8)` beats `√n`, the bound holds for all large even `n`.
-/

open scoped BigOperators
open Filter Real Finset

namespace Conjectures.Cuts.Taskb1827754475dd720a041a0cb_aux

/-- Squares in the central window: at most `√n + 1` of them. -/
private theorem card_squares_le (n : ℕ) :
    ((Finset.Icc ((n + 2) / 3) ((2 * n) / 3)).filter (fun u => u.sqrt ^ 2 = u)).card
      ≤ n.sqrt + 1 := by
  have hsub : (Finset.Icc ((n + 2) / 3) ((2 * n) / 3)).filter (fun u => u.sqrt ^ 2 = u) ⊆
      (Finset.Icc 0 n.sqrt).image (fun p => p ^ 2) := by
    intro u hu
    obtain ⟨huI, hsq⟩ := Finset.mem_filter.mp hu
    have hu2 : u ≤ (2 * n) / 3 := (Finset.mem_Icc.mp huI).2
    have hun : u ≤ n := by omega
    refine Finset.mem_image.mpr ⟨u.sqrt, Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, ?_⟩
    · exact Nat.sqrt_le_sqrt hun
    · exact hsq
  calc ((Finset.Icc ((n + 2) / 3) ((2 * n) / 3)).filter (fun u => u.sqrt ^ 2 = u)).card
      ≤ ((Finset.Icc 0 n.sqrt).image (fun p => p ^ 2)).card := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 0 n.sqrt).card := Finset.card_image_le
    _ = n.sqrt + 1 := by simp

/-- Complements of squares in the central window: at most `√n + 1` of them. -/
private theorem card_complement_squares_le (n : ℕ) :
    ((Finset.Icc ((n + 2) / 3) ((2 * n) / 3)).filter
        (fun u => (n - u).sqrt ^ 2 = n - u)).card ≤ n.sqrt + 1 := by
  have hsub : (Finset.Icc ((n + 2) / 3) ((2 * n) / 3)).filter
        (fun u => (n - u).sqrt ^ 2 = n - u) ⊆
      (Finset.Icc 0 n.sqrt).image (fun p => n - p ^ 2) := by
    intro u hu
    obtain ⟨huI, hsq⟩ := Finset.mem_filter.mp hu
    have hun : u ≤ n := by
      have hu2 : u ≤ (2 * n) / 3 := (Finset.mem_Icc.mp huI).2
      omega
    refine Finset.mem_image.mpr
      ⟨(n - u).sqrt, Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, ?_⟩
    · exact Nat.sqrt_le_sqrt (Nat.sub_le n u)
    · rw [hsq]
      omega
  calc ((Finset.Icc ((n + 2) / 3) ((2 * n) / 3)).filter
        (fun u => (n - u).sqrt ^ 2 = n - u)).card
      ≤ ((Finset.Icc 0 n.sqrt).image (fun p => n - p ^ 2)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.Icc 0 n.sqrt).card := Finset.card_image_le
    _ = n.sqrt + 1 := by simp

/-- The counted set has at most `2(√n+1)` elements. -/
private theorem card_count_le (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ (Finset.Icc ((n + 2) / 3) ((2 * n) / 3)).filter (fun u => u.sqrt ^ 2 = u) ∪
        (Finset.Icc ((n + 2) / 3) ((2 * n) / 3)).filter
          (fun u => (n - u).sqrt ^ 2 = n - u)) :
    (S.card : ℝ) ≤ 2 * ((n.sqrt : ℝ) + 1) := by
  have h1 := card_squares_le n
  have h2 := card_complement_squares_le n
  have hc : S.card ≤ (n.sqrt + 1) + (n.sqrt + 1) := by
    calc S.card ≤ ((Finset.Icc ((n + 2) / 3) ((2 * n) / 3)).filter (fun u => u.sqrt ^ 2 = u) ∪
          (Finset.Icc ((n + 2) / 3) ((2 * n) / 3)).filter
            (fun u => (n - u).sqrt ^ 2 = n - u)).card := Finset.card_le_card hS
      _ ≤ ((Finset.Icc ((n + 2) / 3) ((2 * n) / 3)).filter
            (fun u => u.sqrt ^ 2 = u)).card +
          ((Finset.Icc ((n + 2) / 3) ((2 * n) / 3)).filter
            (fun u => (n - u).sqrt ^ 2 = n - u)).card := Finset.card_union_le _ _
      _ ≤ (n.sqrt + 1) + (n.sqrt + 1) := Nat.add_le_add h1 h2
  have hr : (S.card : ℝ) ≤ ((n.sqrt + 1 : ℕ) : ℝ) + ((n.sqrt + 1 : ℕ) : ℝ) := by
    exact_mod_cast hc
  push_cast at hr
  linarith

end Conjectures.Cuts.Taskb1827754475dd720a041a0cb_aux

theorem Conjectures.Cuts.Taskb1827754475dd720a041a0cb :
    have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → ℕ := fun (x2 : ℕ) => ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | x2 x3 < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x4.sqrt) with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); ∃ (x5 : ℕ), ∀ (x6 : ℕ), x5 ≤ x6 → Even x6 → (↑{x9 ∈ {x9 ∈ x3 x6 | x6 - x9 ∈ x3 x6} | x9.sqrt ^ (2 : ℕ) = x9 ∨ (x6 - x9).sqrt ^ (2 : ℕ) = x6 - x9}.card : ℝ) ≤ (1 / 100 : ℝ) * x4 x6 := by
  intro x1 x2 x3 x4
  obtain ⟨c, hc, hmain⟩ := FareyBrun.terminal_floor_power
  have hgrow : ∀ᶠ n : ℕ in Filter.atTop, (400 : ℝ) / c ≤ (n : ℝ) ^ ((3 : ℝ) / 8) := by
    exact ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 8)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop ((400 : ℝ) / c)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hgrow
  refine ⟨max N 64, fun n hn heven => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hn64 : 64 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hpow : (400 : ℝ) / c ≤ (n : ℝ) ^ ((3 : ℝ) / 8) := hN n hnN
  have hmainn : c * (n : ℝ) ^ ((7 : ℝ) / 8) ≤ FareyBrun.mainTerm n n.sqrt :=
    hmain n hn64 heven
  have hx4 : x4 n = FareyBrun.mainTerm n n.sqrt := rfl
  -- the counted set
  set S : Finset ℕ := {x9 ∈ {x9 ∈ x3 n | n - x9 ∈ x3 n} |
      x9.sqrt ^ (2 : ℕ) = x9 ∨ (n - x9).sqrt ^ (2 : ℕ) = n - x9}
  have hsub : S ⊆ (Finset.Icc ((n + 2) / 3) ((2 * n) / 3)).filter
        (fun u => u.sqrt ^ 2 = u) ∪
      (Finset.Icc ((n + 2) / 3) ((2 * n) / 3)).filter
        (fun u => (n - u).sqrt ^ 2 = n - u) := by
    intro u hu
    obtain ⟨hu1, hsq⟩ := Finset.mem_filter.mp hu
    obtain ⟨hu2, -⟩ := Finset.mem_filter.mp hu1
    have huI : u ∈ Finset.Icc ((n + 2) / 3) ((2 * n) / 3) :=
      (Finset.mem_filter.mp hu2).1
    rw [Finset.mem_union]
    rcases hsq with h | h
    · exact Or.inl (Finset.mem_filter.mpr ⟨huI, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨huI, h⟩)
  have hcard : (S.card : ℝ) ≤ 2 * ((n.sqrt : ℝ) + 1) :=
    Conjectures.Cuts.Taskb1827754475dd720a041a0cb_aux.card_count_le n S hsub
  have hsqrt : (n.sqrt : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' n)
  have h400 : (4 : ℝ) ≤ (1 / 100 : ℝ) * c * (n : ℝ) ^ ((3 : ℝ) / 8) := by
    have hh := mul_le_mul_of_nonneg_left hpow hc.le
    have hcc : c * ((400 : ℝ) / c) = 400 := by field_simp
    linarith
  have hhalf : (1 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
  have hp : (n : ℝ) ^ ((7 : ℝ) / 8) = (n : ℝ) ^ ((1 : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 8) := by
    rw [← Real.rpow_add hn0]
    norm_num
  have hkey : 2 * ((n.sqrt : ℝ) + 1) ≤ (1 / 100 : ℝ) * (c * (n : ℝ) ^ ((7 : ℝ) / 8)) := by
    have hstep : 4 * (n : ℝ) ^ ((1 : ℝ) / 2) ≤
        ((1 / 100 : ℝ) * c * (n : ℝ) ^ ((3 : ℝ) / 8)) * (n : ℝ) ^ ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right h400 (by positivity)
    rw [hp]
    linarith
  have hvol : (1 / 100 : ℝ) * (c * (n : ℝ) ^ ((7 : ℝ) / 8)) ≤ (1 / 100 : ℝ) * x4 n := by
    rw [hx4]
    linarith
  linarith
