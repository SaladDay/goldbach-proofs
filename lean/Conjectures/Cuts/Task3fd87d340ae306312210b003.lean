import Mathlib

/-!
# Premise 1/2 of the cut `L-goldbach-cut-fffb7eb7e6eec207cada90da`

The two side conditions `2 ≤ x6` and `x6 ≤ 2` force `x6 = 2`, so the base set
`x9 ⊆ Finset.Icc 1 2` has at most two elements.  The counted family is a filtered subset of
`x11.product x11`, where `x11 = Fintype.piFinset (fun _ : Fin 4 => x9)`, hence
`x11.card = x9.card ^ 4` and the count is at most `x9.card ^ 8`.  With `c = x9.card ≤ 2` we
have `c ^ 8 ≤ 16 * c ^ 4`, and since the exponent `if x1.natDegree = 3 then 5 else 4` is at
least `4` and `2 ^ x3 ≥ 1` for `x3 > 0`, this is at most `16 * 2 ^ x3 * c ^ e`.  The witness
is the constant `x5 = 16`; the polynomial hypothesis and the collision predicates are not
needed, only the chain of filter inclusions.
-/

namespace Conjectures.Cuts.Task3fd87d340ae306312210b003_aux

lemma card_le_of_subset {α : Type*} [DecidableEq α] {s t : Finset α} (h : s ⊆ t) :
    s.card ≤ t.card := Finset.card_le_card h

lemma card_piFinset_four (x9 : Finset ℕ) :
    (Fintype.piFinset (fun _ : Fin (4 : ℕ) => x9)).card = x9.card ^ (4 : ℕ) := by
  rw [Fintype.card_piFinset]
  simp

/-- Fourth power of a nonneg real is monotone. -/
lemma pow_four_le_pow_four {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ (4 : ℕ) ≤ b ^ (4 : ℕ) :=
  pow_le_pow_left₀ ha h 4

/-- Powers of a real `≥ 1` are monotone in the exponent. -/
lemma pow_four_le_pow_exp {c : ℝ} (hc : 1 ≤ c) {e : ℕ} (he : 4 ≤ e) :
    c ^ (4 : ℕ) ≤ c ^ e := pow_le_pow_right₀ hc he

lemma exp_ge_four (d : ℕ) : (4 : ℕ) ≤ if d = (3 : ℕ) then (5 : ℕ) else (4 : ℕ) := by
  split_ifs <;> omega

end Conjectures.Cuts.Task3fd87d340ae306312210b003_aux

theorem Conjectures.Cuts.Task3fd87d340ae306312210b003 :
∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 x6 ≤ (2 : ℕ) →                   ∀ x9 ⊆ Finset.Icc (1 : ℕ) x6,                     have x11 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x11 : Fin (4 : ℕ)) => x9;                     have x12 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x12 : Fin (4 : ℕ) → ℕ) => ∑ x13 : Fin (4 : ℕ), Polynomial.eval (↑(x12 x13)) x1;                     ↑{x13 ∈ x11.product x11 | x12 x13.1 = x12 x13.2 ∧ ∀ (x14 : Equiv.Perm (Fin (4 : ℕ))), x13.2 ≠ x13.1 ∘ ⇑x14}.card ≤ x5 * ↑x6 ^ x3 * ↑x9.card ^ if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ) := by
  intro x1 _ x3 hx3
  refine ⟨16, by norm_num, ?_⟩
  intro x6 hx6 hx6' x9 hx9 x11 x12
  have hx6eq : x6 = 2 := le_antisymm hx6' hx6
  have hsub : {x13 ∈ x11.product x11 | x12 x13.1 = x12 x13.2 ∧
      ∀ (x14 : Equiv.Perm (Fin (4 : ℕ))), x13.2 ≠ x13.1 ∘ ⇑x14} ⊆ x11.product x11 :=
    Finset.filter_subset _ _
  have h11 : x11.card = x9.card ^ (4 : ℕ) :=
    Conjectures.Cuts.Task3fd87d340ae306312210b003_aux.card_piFinset_four x9
  have hcard : {x13 ∈ x11.product x11 | x12 x13.1 = x12 x13.2 ∧
      ∀ (x14 : Equiv.Perm (Fin (4 : ℕ))), x13.2 ≠ x13.1 ∘ ⇑x14}.card ≤
      x9.card ^ (4 : ℕ) * x9.card ^ (4 : ℕ) := by
    calc _ ≤ (x11.product x11).card :=
          Conjectures.Cuts.Task3fd87d340ae306312210b003_aux.card_le_of_subset hsub
      _ = x11.card * x11.card := Finset.card_product x11 x11
      _ = x9.card ^ (4 : ℕ) * x9.card ^ (4 : ℕ) := by rw [h11]
  have hc : x9.card ≤ 2 := by
    calc x9.card ≤ (Finset.Icc (1 : ℕ) x6).card :=
          Conjectures.Cuts.Task3fd87d340ae306312210b003_aux.card_le_of_subset hx9
      _ = 2 := by rw [hx6eq]; decide
  have hcast : ((↑{x13 ∈ x11.product x11 | x12 x13.1 = x12 x13.2 ∧
      ∀ (x14 : Equiv.Perm (Fin (4 : ℕ))), x13.2 ≠ x13.1 ∘ ⇑x14}.card : ℕ) : ℝ) ≤
      (↑x9.card : ℝ) ^ (8 : ℕ) := by
    have h := hcard
    have h' : ((↑{x13 ∈ x11.product x11 | x12 x13.1 = x12 x13.2 ∧
        ∀ (x14 : Equiv.Perm (Fin (4 : ℕ))), x13.2 ≠ x13.1 ∘ ⇑x14}.card : ℕ) : ℝ) ≤
        (↑x9.card : ℝ) ^ (4 : ℕ) * (↑x9.card : ℝ) ^ (4 : ℕ) := by exact_mod_cast h
    linarith [show (↑x9.card : ℝ) ^ (4 : ℕ) * (↑x9.card : ℝ) ^ (4 : ℕ) =
        (↑x9.card : ℝ) ^ (8 : ℕ) by ring]
  have hbase : (1 : ℝ) ≤ (↑x6 : ℝ) ^ x3 := by
    rw [hx6eq]
    exact Real.one_le_rpow (by norm_num) hx3.le
  have hexp : (4 : ℕ) ≤ if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ) :=
    Conjectures.Cuts.Task3fd87d340ae306312210b003_aux.exp_ge_four x1.natDegree
  have key : (↑x9.card : ℝ) ^ (8 : ℕ) ≤
      16 * (↑x6 : ℝ) ^ x3 * (↑x9.card : ℝ) ^ (if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ)) := by
    rcases Nat.eq_zero_or_pos x9.card with h0 | hpos
    · have hz : (↑x9.card : ℝ) = 0 := by exact_mod_cast h0
      rw [hz]
      have h8 : (0 : ℝ) ^ (8 : ℕ) = 0 := by norm_num
      rw [h8]
      positivity
    · have hc1 : (1 : ℝ) ≤ (↑x9.card : ℝ) := by exact_mod_cast hpos
      have hc4 : (↑x9.card : ℝ) ^ (4 : ℕ) ≤ 16 := by
        calc (↑x9.card : ℝ) ^ (4 : ℕ) ≤ (2 : ℝ) ^ (4 : ℕ) :=
              Conjectures.Cuts.Task3fd87d340ae306312210b003_aux.pow_four_le_pow_four
                (Nat.cast_nonneg _) (by exact_mod_cast hc)
          _ = 16 := by norm_num
      have hce : (↑x9.card : ℝ) ^ (4 : ℕ) ≤
          (↑x9.card : ℝ) ^ (if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ)) :=
        Conjectures.Cuts.Task3fd87d340ae306312210b003_aux.pow_four_le_pow_exp hc1 hexp
      calc (↑x9.card : ℝ) ^ (8 : ℕ)
          = (↑x9.card : ℝ) ^ (4 : ℕ) * (↑x9.card : ℝ) ^ (4 : ℕ) := by ring
        _ ≤ 16 * (↑x9.card : ℝ) ^ (4 : ℕ) :=
            mul_le_mul_of_nonneg_right hc4 (by positivity)
        _ ≤ 16 * ((↑x6 : ℝ) ^ x3 *
              (↑x9.card : ℝ) ^ (if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ))) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            calc (↑x9.card : ℝ) ^ (4 : ℕ) = 1 * (↑x9.card : ℝ) ^ (4 : ℕ) := by ring
              _ ≤ (↑x6 : ℝ) ^ x3 *
                  (↑x9.card : ℝ) ^ (if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ)) :=
                  mul_le_mul hbase hce (by positivity) (by positivity)
        _ = 16 * (↑x6 : ℝ) ^ x3 *
              (↑x9.card : ℝ) ^ (if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ)) := by ring
  calc ((↑{x13 ∈ x11.product x11 | x12 x13.1 = x12 x13.2 ∧
      ∀ (x14 : Equiv.Perm (Fin (4 : ℕ))), x13.2 ≠ x13.1 ∘ ⇑x14}.card : ℕ) : ℝ)
      ≤ (↑x9.card : ℝ) ^ (8 : ℕ) := hcast
    _ ≤ 16 * (↑x6 : ℝ) ^ x3 *
        (↑x9.card : ℝ) ^ (if x1.natDegree = (3 : ℕ) then (5 : ℕ) else (4 : ℕ)) := key
