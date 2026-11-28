import Mathlib

theorem Task6e7eab5d6762d9537316b045_log_le_39 (n : ℕ) (hn : n ≤ (10 : ℕ) ^ (12 : ℕ)) :
    Nat.log 2 (n + 2) ≤ 39 := by
  have hlt : n + 2 < 2 ^ (40 : ℕ) := by
    have h : (10 : ℕ) ^ (12 : ℕ) + 2 < 2 ^ (40 : ℕ) := by norm_num
    omega
  have hlog := Nat.log_lt_of_lt_pow (b := 2) (x := 40) (y := n + 2) (by omega) hlt
  omega

theorem Task6e7eab5d6762d9537316b045_pow_eight_finite (m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ 39) :
    2 ^ (m + 1) ≤ m ^ 8 + 3 := by
  have htwo : ∀ b : ℕ, m ≤ b → 2 ^ (m + 1) ≤ 2 ^ (b + 1) := by
    intro b hb
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmono : ∀ a : ℕ, a ≤ m → a ^ 8 ≤ m ^ 8 := fun a ha => Nat.pow_le_pow_left ha 8
  by_cases h37 : 37 ≤ m
  · have h1' := htwo 39 h2
    have h2' := hmono 37 h37
    have hc : 2 ^ (39 + 1) ≤ 37 ^ 8 + 3 := by norm_num
    omega
  · by_cases h31 : 31 ≤ m
    · have h1' := htwo 36 (by omega)
      have h2' := hmono 31 h31
      have hc : 2 ^ (36 + 1) ≤ 31 ^ 8 + 3 := by norm_num
      omega
    · by_cases h21 : 21 ≤ m
      · have h1' := htwo 30 (by omega)
        have h2' := hmono 21 h21
        have hc : 2 ^ (30 + 1) ≤ 21 ^ 8 + 3 := by norm_num
        omega
      · by_cases h12 : 12 ≤ m
        · have h1' := htwo 20 (by omega)
          have h2' := hmono 12 h12
          have hc : 2 ^ (20 + 1) ≤ 12 ^ 8 + 3 := by norm_num
          omega
        · by_cases h5 : 5 ≤ m
          · have h1' := htwo 11 (by omega)
            have h2' := hmono 5 h5
            have hc : 2 ^ (11 + 1) ≤ 5 ^ 8 + 3 := by norm_num
            omega
          · by_cases h2m : 2 ≤ m
            · have h1' := htwo 4 (by omega)
              have h2' := hmono 2 h2m
              have hc : 2 ^ (4 + 1) ≤ 2 ^ 8 + 3 := by norm_num
              omega
            · have hm1 : m = 1 := by omega
              subst hm1
              norm_num

theorem Task6e7eab5d6762d9537316b045_n_le_log_pow_eight_aux_log_le_39 (n : ℕ)
    (hn : n ≤ (10 : ℕ) ^ (12 : ℕ)) : Nat.log 2 (n + 2) ≤ 39 := by
  have hlt : n + 2 < 2 ^ (40 : ℕ) := by
    have h : (10 : ℕ) ^ (12 : ℕ) + 2 < 2 ^ (40 : ℕ) := by norm_num
    omega
  have hlog := Nat.log_lt_of_lt_pow (b := 2) (x := 40) (y := n + 2) (by omega) hlt
  omega

theorem Task6e7eab5d6762d9537316b045_n_le_log_pow_eight_aux_pow (m : ℕ) (h1 : 1 ≤ m)
    (h2 : m ≤ 39) : 2 ^ (m + 1) ≤ m ^ 8 + 3 := by
  interval_cases m <;> norm_num

theorem Task6e7eab5d6762d9537316b045_n_le_log_pow_eight (n : ℕ) (hn : n ≤ (10 : ℕ) ^ (12 : ℕ)) :
    n ≤ (Nat.log 2 (n + 2)) ^ 8 := by
  have hm1 : 1 ≤ Nat.log 2 (n + 2) :=
    Nat.le_log_of_pow_le (by norm_num) (by omega : (2 : ℕ) ^ 1 ≤ n + 2)
  have hm39 : Nat.log 2 (n + 2) ≤ 39 :=
    Task6e7eab5d6762d9537316b045_n_le_log_pow_eight_aux_log_le_39 n hn
  have hpow := Task6e7eab5d6762d9537316b045_n_le_log_pow_eight_aux_pow (Nat.log 2 (n + 2)) hm1 hm39
  have hlt : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) (n + 2)
  omega

theorem Task6e7eab5d6762d9537316b045_dirichlet_rat (α : ℝ) (N : ℕ) (hN : 2 ≤ N) :
    ∃ q : ℚ, |α - (q : ℝ)| ≤ 1 / ((N : ℝ) * (q.den : ℝ)) ∧ q.den ≤ N := by
  have hN1 : 0 < N - 1 := by omega
  obtain ⟨q, hq, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hN1
  have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    exact_mod_cast (show N - 1 + 1 = N by omega)
  refine ⟨q, ?_, by omega⟩
  simpa [hcast] using hq

theorem Task6e7eab5d6762d9537316b045_dirichlet_nat (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1)
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ q a : ℕ, 1 ≤ q ∧ q ≤ N ∧ a ≤ q ∧ a.Coprime q ∧
      |α - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) * (N : ℝ)) := by
  obtain ⟨r, hr, hrden⟩ := Task6e7eab5d6762d9537316b045_dirichlet_rat α N hN
  have hden1 : 1 ≤ r.den := r.den_pos
  have hdenpos : (0 : ℝ) < (r.den : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hden1)
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hcast : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := Rat.cast_def r

  have hstrict : |α - (r : ℝ)| < 1 / (r.den : ℝ) := by
    have hlt : 1 / ((N : ℝ) * (r.den : ℝ)) < 1 / (r.den : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hnum0 : 0 ≤ r.num := by
    by_contra hneg
    push_neg at hneg
    have hnumle : r.num ≤ -1 := by omega
    have hnumr : (r.num : ℝ) ≤ -1 := by exact_mod_cast hnumle
    have hrle : (r : ℝ) ≤ -(1 / (r.den : ℝ)) := by
      rw [hcast, ← neg_div]
      exact div_le_div_of_nonneg_right hnumr hdenpos.le
    have hlow : 1 / (r.den : ℝ) ≤ α - (r : ℝ) := by linarith
    have hupp := le_abs_self (α - (r : ℝ))
    linarith
  have hnum1 : r.num ≤ (r.den : ℤ) := by
    by_contra hgt
    push_neg at hgt
    have hnumge : (r.den : ℤ) + 1 ≤ r.num := by omega
    have hnumr : (r.den : ℝ) + 1 ≤ (r.num : ℝ) := by exact_mod_cast hnumge
    have hrge : 1 + 1 / (r.den : ℝ) ≤ (r : ℝ) := by
      rw [hcast, le_div_iff₀ hdenpos]
      have hmul : (1 + 1 / (r.den : ℝ)) * (r.den : ℝ) = (r.den : ℝ) + 1 := by
        field_simp
      linarith
    have hlow : 1 / (r.den : ℝ) ≤ (r : ℝ) - α := by linarith
    have hupp := le_abs_self ((r : ℝ) - α)
    have habs : |(r : ℝ) - α| = |α - (r : ℝ)| := abs_sub_comm _ _
    linarith
  have hto : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hnum0
  have hnat : r.num.natAbs = r.num.toNat := by
    have h1 : ((r.num.natAbs : ℕ) : ℤ) = r.num := Int.natAbs_of_nonneg hnum0
    omega
  refine ⟨r.den, r.num.toNat, hden1, hrden, ?_, ?_, ?_⟩
  · omega
  · simpa [hnat] using r.reduced
  · have hact : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by exact_mod_cast hto
    rw [hact, ← hcast]
    simpa [mul_comm] using hr

theorem Task6e7eab5d6762d9537316b045_wide_arc_cover_aux_pow (m : ℕ) (h1 : 2 ≤ m) (h2 : m ≤ 39) :
    2 ^ (m + 1) ≤ m ^ 8 := by
  interval_cases m <;> norm_num

theorem Task6e7eab5d6762d9537316b045_wide_arc_cover_aux_n_le (n : ℕ) (hn2 : 2 ≤ n)
    (hn : n ≤ (10 : ℕ) ^ (12 : ℕ)) :
    n ≤ (Nat.log 2 (n + 2)) ^ 8 := by
  have hlog : 2 ≤ Nat.log 2 (n + 2) :=
    Nat.le_log_of_pow_le (by norm_num) (by omega : (2 : ℕ) ^ 2 ≤ n + 2)
  have hlt : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) := by
    simpa using Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (n + 2)
  rcases Nat.lt_or_ge (Nat.log 2 (n + 2)) 40 with h | h
  · have hpow := Task6e7eab5d6762d9537316b045_wide_arc_cover_aux_pow (Nat.log 2 (n + 2)) hlog (by omega)
    omega
  · have h39 : (39 : ℕ) ^ 8 ≤ (Nat.log 2 (n + 2)) ^ 8 :=
      Nat.pow_le_pow_left (by omega) 8
    have hbig : (10 : ℕ) ^ (12 : ℕ) ≤ (39 : ℕ) ^ 8 := by norm_num
    omega

theorem Task6e7eab5d6762d9537316b045_wide_arc_cover (n : ℕ) (hn2 : 2 ≤ n)
    (hn : n ≤ (10 : ℕ) ^ (12 : ℕ)) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) :
    ∃ q a : ℕ, 1 ≤ q ∧ q ≤ (Nat.log 2 (n + 2) ^ 2) ^ 2 ∧ a ≤ q ∧ a.Coprime q ∧
      |α - (a : ℝ) / (q : ℝ)| ≤
        ((Nat.log 2 (n + 2) ^ 2 : ℕ) : ℝ) ^ 2 / ((q : ℝ) * (n : ℝ)) := by
  have hQ4 : 4 ≤ Nat.log 2 (n + 2) ^ 2 := by
    have hlog : 2 ≤ Nat.log 2 (n + 2) :=
      Nat.le_log_of_pow_le (by norm_num) (by omega : (2 : ℕ) ^ 2 ≤ n + 2)
    nlinarith
  have hN : 2 ≤ (Nat.log 2 (n + 2) ^ 2) ^ 2 := by nlinarith
  obtain ⟨q, a, hq1, hq2, ha, hcop, hbound⟩ :=
    Task6e7eab5d6762d9537316b045_dirichlet_nat α h0 h1 ((Nat.log 2 (n + 2) ^ 2) ^ 2) hN
  refine ⟨q, a, hq1, hq2, ha, hcop, ?_⟩
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hq1)
  have hQpos : (0 : ℝ) < ((Nat.log 2 (n + 2) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (le_trans (by norm_num) hQ4))
  have hnle : n ≤ (Nat.log 2 (n + 2) ^ 2) ^ 4 := by
    have h := Task6e7eab5d6762d9537316b045_wide_arc_cover_aux_n_le n hn2 hn
    calc n ≤ (Nat.log 2 (n + 2)) ^ 8 := h
      _ = (Nat.log 2 (n + 2) ^ 2) ^ 4 := by ring
  have hnreal : (n : ℝ) ≤ ((Nat.log 2 (n + 2) ^ 2 : ℕ) : ℝ) ^ 4 := by exact_mod_cast hnle
  have hcast : (((Nat.log 2 (n + 2) ^ 2) ^ 2 : ℕ) : ℝ) = ((Nat.log 2 (n + 2) ^ 2 : ℕ) : ℝ) ^ 2 := by
    push_cast; ring
  rw [hcast] at hbound
  calc |α - (a : ℝ) / (q : ℝ)|
      ≤ 1 / ((q : ℝ) * ((Nat.log 2 (n + 2) ^ 2 : ℕ) : ℝ) ^ 2) := hbound
    _ ≤ ((Nat.log 2 (n + 2) ^ 2 : ℕ) : ℝ) ^ 2 / ((q : ℝ) * (n : ℝ)) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith

theorem Conjectures.Cuts.Task6e7eab5d6762d9537316b045 :
    have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp (↑((2 : ℝ) * Real.pi * x2) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), ↑(x4 x6) * x2 (↑x6 * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - ↑x8 / ↑x7| ≤ ↑(x4 x5) / (↑x7 * ↑x5)}; have x6 : ℕ → ℕ → ℝ := fun (x6 x7 : ℕ) => if x7 ^ (3 : ℕ) ≤ x6 then x1 x7 else (0 : ℝ); have x7 : ℕ → ℕ → ℝ := fun (x7 x8 : ℕ) => x1 x8 - x6 x7 x8; have x8 : ℕ → ℕ := fun (x8 : ℕ) => Max.max (1 : ℕ) (Nat.log (2 : ℕ) x8 / (2 : ℕ)); have x9 : ℕ → ℝ → ℝ := fun (x9 : ℕ) (x10 : ℝ) => (∑ x11 ∈ Finset.range (x8 x9), Real.cos ((2 : ℝ) * Real.pi * (2 : ℝ) ^ (x11 + (1 : ℕ)) * x10)) / ↑(x8 x9); have x10 : ℕ → Set ℝ := fun (x10 : ℕ) => {x11 : ℝ | x11 ∉ x5 x10 ∧ (1 / 2 : ℝ) < x9 x10 x11}; have x11 : ℕ → (ℕ → Prop) → Set ℝ := fun (x11 : ℕ) (x12 : ℕ → Prop) => {x13 : ℝ | ∃ (x14 : ℕ) (x15 : ℕ), (1 : ℕ) ≤ x14 ∧ x14 ≤ x4 x11 ^ (2 : ℕ) ∧ x15 ≤ x14 ∧ x15.Coprime x14 ∧ x12 x14 ∧ |x13 - ↑x15 / ↑x14| ≤ ↑(x4 x11) ^ (2 : ℕ) / (↑x14 * ↑x11)}; have x12 : ℕ → ℝ → ℝ := fun (x12 : ℕ) (x13 : ℝ) => ‖x3 x12 (x7 x12) x13‖ ^ (2 : ℕ); have x13 : ℕ → ℝ := fun (x13 : ℕ) => ↑x13 * ((1 : ℝ) + Real.log ↑x13) ^ (4 : ℕ); have x14 : Set ℝ → (ℝ → ℝ) → ℝ := fun (x14 : Set ℝ) (x15 : ℝ → ℝ) => intervalIntegral (x14.indicator x15) (0 : ℝ) (1 : ℝ) MeasureTheory.MeasureSpace.volume; ∀ x15 ≤ (10 : ℕ) ^ (12 : ℕ),   Even x15 →     ∀ (x18 : ℕ),       have x19 : ℝ := (2 : ℝ) ^ x18 * x13 x15;       (x19 * x14 ((x10 x15 \ x11 x15 fun (x20 : ℕ) => True) ∩ {x20 : ℝ | x19 < x12 x15 x20 ∧ x12 x15 x20 ≤ (2 : ℝ) * x19}) fun (x20 : ℝ) => (1 : ℝ)) ≤ ↑x15 / ((100000 : ℝ) * ((1 : ℝ) + Real.log ↑x15) ^ (2 : ℕ)) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 hx15 heven x18 x19
  have hzero :
      x14 ((x10 x15 \ x11 x15 fun (x20 : ℕ) => True) ∩
          {x20 : ℝ | x19 < x12 x15 x20 ∧ x12 x15 x20 ≤ (2 : ℝ) * x19})
        (fun (x20 : ℝ) => (1 : ℝ)) = 0 := by
    have hpt : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        ((x10 x15 \ x11 x15 fun (x20 : ℕ) => True) ∩
          {x20 : ℝ | x19 < x12 x15 x20 ∧ x12 x15 x20 ≤ (2 : ℝ) * x19}).indicator
            (fun (x20 : ℝ) => (1 : ℝ)) t = 0 := by
      intro t ht
      have ht01 : 0 ≤ t ∧ t ≤ 1 := by
        have : t ∈ Set.Icc (0 : ℝ) 1 := by simpa [Set.uIcc_of_le] using ht
        exact this
      by_cases hn0 : x15 = 0
      · have hband : t ∉ {x20 : ℝ | x19 < x12 x15 x20 ∧ x12 x15 x20 ≤ (2 : ℝ) * x19} := by
          intro hmem
          have hx19 : x19 = 0 := by
            simp [x19, x13, hn0]
          have h1 := hmem.1
          have h2 := hmem.2
          rw [hx19] at h1 h2
          linarith
        have hnot : t ∉ (x10 x15 \ x11 x15 fun (x20 : ℕ) => True) ∩
            {x20 : ℝ | x19 < x12 x15 x20 ∧ x12 x15 x20 ≤ (2 : ℝ) * x19} :=
          fun hmem => hband hmem.2
        exact Set.indicator_of_notMem hnot _
      · have hn2 : 2 ≤ x15 := by
          obtain ⟨r, hr⟩ := heven
          omega
        have hmem : t ∈ x11 x15 (fun (x20 : ℕ) => True) := by
          obtain ⟨q, a, hq1, hq2, ha, hcop, hbd⟩ :=
            Task6e7eab5d6762d9537316b045_wide_arc_cover x15 hn2 hx15 t ht01.1 ht01.2
          exact ⟨q, a, hq1, hq2, ha, hcop, trivial, hbd⟩
        have hnot : t ∉ (x10 x15 \ x11 x15 fun (x20 : ℕ) => True) ∩
            {x20 : ℝ | x19 < x12 x15 x20 ∧ x12 x15 x20 ≤ (2 : ℝ) * x19} := by
          intro hmem'
          exact hmem'.1.2 hmem
        exact Set.indicator_of_notMem hnot _
    show intervalIntegral _ (0 : ℝ) 1 MeasureTheory.MeasureSpace.volume = 0
    rw [intervalIntegral.integral_congr (fun t ht => hpt t ht), intervalIntegral.integral_zero]
  rw [hzero, mul_zero]
  have hlog : 0 ≤ 1 + Real.log (x15 : ℝ) := by
    rcases Nat.eq_zero_or_pos x15 with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ (x15 : ℝ) := by exact_mod_cast h
      have h2 := Real.log_nonneg h1
      linarith
  have hden : 0 < (100000 : ℝ) * ((1 : ℝ) + Real.log (x15 : ℝ)) ^ 2 := by positivity
  exact div_nonneg (Nat.cast_nonneg x15) hden.le
