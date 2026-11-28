import Mathlib
import Conjectures.Goldbach.CentralBlockPrimeInput

/-!
# L-goldbach-cut-8ffdc3948dee7122ce13b3c9

Model mass lower bound.  For `n` even and large, the model mass

`M(n) = ∑ p in window, ∑ j < 3, θ(p) · w(n + 2j − 2 − p)`

is at least `c · n`, where the window is `3p ≤ 2n ≤ 6p`, `θ(p) = log p` on primes
and `w(q) = 15/4` when `q` is coprime to `30`.

Two ingredients:

* the Chebyshev mass of the interior block `[n/2, 2n/3]` is at least `n/12` for large `n`
  (the accepted module `Conjectures.Goldbach.CentralBlockPrimeInput`, itself a consequence of
  the prime number theorem for `θ`);
* for `n` even and `p` an odd prime, the three shifts `n − p − 2`, `n − p`, `n − p + 2` are
  odd and pairwise incongruent modulo `3` and no two differ by a multiple of `5`, so one of
  them is coprime to `30`; that shift alone contributes `(15/4) · log p`.

The second fact is a finite check over residues modulo `30`.
-/

namespace Conjectures.Cuts.Task8ffdc3948dee7122ce13b3c9_aux

/-- Among three consecutive odd shifts of a residue class, one is coprime to `30`. -/
lemma shift_coprime_fin : ∀ k ∈ Finset.range 30, k % 2 = 1 →
    ∃ j ∈ Finset.range 3, Nat.Coprime (k + 2 * j) 30 := by decide

/-- For every odd `m`, one of `m`, `m + 2`, `m + 4` is coprime to `30`. -/
lemma shift_coprime (m : ℕ) (hm : m % 2 = 1) :
    ∃ j ∈ Finset.range 3, Nat.Coprime (m + 2 * j) 30 := by
  have hk : m % 30 ∈ Finset.range 30 := Finset.mem_range.mpr (Nat.mod_lt m (by norm_num))
  have hkodd : m % 30 % 2 = 1 := by omega
  obtain ⟨j, hj, hcop⟩ := shift_coprime_fin _ hk hkodd
  refine ⟨j, hj, ?_⟩
  have hmod : (m + 2 * j) % 30 = (m % 30 + 2 * j) % 30 := by omega
  rw [← ZMod.coprime_mod_iff_coprime, hmod]
  exact (ZMod.coprime_mod_iff_coprime (m % 30 + 2 * j) 30).mpr hcop

/-- A single odd prime in the central window contributes at least `(15/4) · log p`. -/
lemma inner_lower (n p : ℕ) (hn : 12 ≤ n) (heven : n % 2 = 0) (hp : Nat.Prime p)
    (hlo : 2 * n ≤ 6 * p) (hhi : 3 * p ≤ 2 * n) :
    (15 / 4 : ℝ) * Real.log (p : ℝ) ≤
      ∑ j ∈ Finset.range 3,
        (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) *
          if (n + 2 * j - 2 - p).Coprime 30 then (15 / 4 : ℝ) else (0 : ℝ) := by
  have hp4 : 4 ≤ p := by omega
  have hpodd : p % 2 = 1 := by
    have h2 : p ≠ 2 := by omega
    have := hp.eq_two_or_odd
    omega
  have hmodd : (n - p - 2) % 2 = 1 := by omega
  obtain ⟨j, hj, hcop⟩ := shift_coprime (n - p - 2) hmodd
  have hval : n + 2 * j - 2 - p = n - p - 2 + 2 * j := by omega
  rw [Finset.mem_range] at hj
  have hnonneg : ∀ i ∈ Finset.range 3,
      (0 : ℝ) ≤ (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) *
          if (n + 2 * i - 2 - p).Coprime 30 then (15 / 4 : ℝ) else (0 : ℝ) := by
    intro i _
    have h1 : (0 : ℝ) ≤ (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) := by
      have hpl : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
      rw [ite_eq_left_iff.mpr (fun h => (h hp).elim)]
      exact Real.log_nonneg hpl
    have h2 : (0 : ℝ) ≤
        (if (n + 2 * i - 2 - p).Coprime 30 then (15 / 4 : ℝ) else (0 : ℝ)) := by
      split_ifs <;> norm_num
    exact mul_nonneg h1 h2
  have hsingle : (15 / 4 : ℝ) * Real.log (p : ℝ) ≤
      (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) *
        if (n + 2 * j - 2 - p).Coprime 30 then (15 / 4 : ℝ) else (0 : ℝ) := by
    rw [hval, ite_eq_left_iff.mpr (fun h => (h hp).elim),
      ite_eq_left_iff.mpr (fun h => (h hcop).elim)]
    rw [mul_comm]
  exact hsingle.trans (Finset.single_le_sum hnonneg (Finset.mem_range.mpr hj))

end Conjectures.Cuts.Task8ffdc3948dee7122ce13b3c9_aux

theorem Conjectures.Cuts.Task8ffdc3948dee7122ce13b3c9 :
    ∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∃ (x2 : ℕ), ∀ (x3 : ℕ), x2 ≤ x3 → Even x3 → x1 * ↑x3 ≤ ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)) with (3 : ℕ) * x6 ≤ (2 : ℕ) * x3 ∧ (2 : ℕ) * x3 ≤ (6 : ℕ) * x6, ∑ x7 ∈ Finset.range (3 : ℕ), (if Nat.Prime x6 then Real.log ↑x6 else (0 : ℝ)) * if (x3 + (2 : ℕ) * x7 - (2 : ℕ) - x6).Coprime (30 : ℕ) then (15 / 4 : ℝ) else (0 : ℝ) := by
  open Conjectures.Cuts.Task8ffdc3948dee7122ce13b3c9_aux in
  obtain ⟨c, hc, X, hX⟩ := Conjectures.Goldbach.CentralBlockPrimeInput
  refine ⟨(15 / 4 : ℝ) * c, by positivity, max X 12, ?_⟩
  intro n hn heven
  have hn12 : 12 ≤ n := le_trans (le_max_right X 12) hn
  have hnX : X ≤ n := le_trans (le_max_left X 12) hn
  have heven2 : n % 2 = 0 := Nat.even_iff.mp heven
  have hblock' : c * (n : ℝ) ≤
      ∑ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ n ≤ 2 * p ∧ 3 * p ≤ 2 * n),
        (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) := hX n hnX
  have hsub : (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ n ≤ 2 * p ∧ 3 * p ≤ 2 * n) ⊆
      (Finset.range (n + 1)).filter (fun p => 3 * p ≤ 2 * n ∧ 2 * n ≤ 6 * p) := by
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.2.2, by omega⟩
  have hf_nonneg : ∀ p ∈ (Finset.range (n + 1)).filter (fun p => 3 * p ≤ 2 * n ∧ 2 * n ≤ 6 * p),
      (0 : ℝ) ≤ ∑ j ∈ Finset.range 3,
        (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) *
          if (n + 2 * j - 2 - p).Coprime 30 then (15 / 4 : ℝ) else (0 : ℝ) := by
    intro p _
    refine Finset.sum_nonneg (fun j _ => ?_)
    have h1 : (0 : ℝ) ≤ (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) := by
      split_ifs with h
      · exact Real.log_nonneg (by exact_mod_cast h.one_le)
      · exact le_rfl
    have h2 : (0 : ℝ) ≤
        (if (n + 2 * j - 2 - p).Coprime 30 then (15 / 4 : ℝ) else (0 : ℝ)) := by
      split_ifs <;> norm_num
    exact mul_nonneg h1 h2
  have hmid : (15 / 4 : ℝ) *
      ∑ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ n ≤ 2 * p ∧ 3 * p ≤ 2 * n),
        (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) ≤
      ∑ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ n ≤ 2 * p ∧ 3 * p ≤ 2 * n),
        ∑ j ∈ Finset.range 3,
          (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) *
            if (n + 2 * j - 2 - p).Coprime 30 then (15 / 4 : ℝ) else (0 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    obtain ⟨_, hpp, h2p, h3p⟩ := hp
    have hlog : (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) = Real.log (p : ℝ) :=
      ite_eq_left_iff.mpr (fun h => (h hpp).elim)
    calc (15 / 4 : ℝ) * (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ))
        = (15 / 4 : ℝ) * Real.log (p : ℝ) := by rw [hlog]
      _ ≤ ∑ j ∈ Finset.range 3,
            (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) *
              if (n + 2 * j - 2 - p).Coprime 30 then (15 / 4 : ℝ) else (0 : ℝ) :=
          inner_lower n p hn12 heven2 hpp (by omega) h3p
  have hfin : (15 / 4 : ℝ) *
      ∑ p ∈ (Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ n ≤ 2 * p ∧ 3 * p ≤ 2 * n),
        (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) ≤
      ∑ p ∈ (Finset.range (n + 1)).filter (fun p => 3 * p ≤ 2 * n ∧ 2 * n ≤ 6 * p),
        ∑ j ∈ Finset.range 3,
          (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) *
            if (n + 2 * j - 2 - p).Coprime 30 then (15 / 4 : ℝ) else (0 : ℝ) :=
    hmid.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ => hf_nonneg i hi))
  calc ((15 / 4 : ℝ) * c) * (n : ℝ)
      = (15 / 4 : ℝ) * (c * (n : ℝ)) := by ring
    _ ≤ (15 / 4 : ℝ) *
        ∑ p ∈ (Finset.range (n + 1)).filter
            (fun p => Nat.Prime p ∧ n ≤ 2 * p ∧ 3 * p ≤ 2 * n),
          (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hblock' (by norm_num)
    _ ≤ ∑ p ∈ (Finset.range (n + 1)).filter (fun p => 3 * p ≤ 2 * n ∧ 2 * n ≤ 6 * p),
        ∑ j ∈ Finset.range 3,
          (if Nat.Prime p then Real.log (p : ℝ) else (0 : ℝ)) *
            if (n + 2 * j - 2 - p).Coprime 30 then (15 / 4 : ℝ) else (0 : ℝ) := hfin
