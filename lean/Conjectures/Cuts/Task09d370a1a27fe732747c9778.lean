import Mathlib

/-!
# Cut `L-goldbach-cut-09d370a1a27fe732747c9778`

Bound the common exceptional union over all ordered pairs of coefficients from one
uniform per-pair bound.

The union `x1.biUnion (fun x5 => x1.biUnion (fun x6 => x2 x5 x6))` is a double
`Finset.biUnion`, so `Finset.card_biUnion_le` applied twice gives
`(union).card ≤ ∑ x5 ∈ x1, ∑ x6 ∈ x1, (x2 x5 x6).card`.  The hypothesis bounds every
summand by the same real `x3`, so each inner sum is at most `x1.card * x3` and the outer
sum is at most `x1.card * (x1.card * x3) = x1.card ^ 2 * x3`.  The `x3`-hypothesis is
only used through its per-pair instances; no positivity assumption on `x3` is needed
(the empty `x1` case is vacuous and gives `0 ≤ 0`).
-/

theorem Conjectures.Cuts.Task09d370a1a27fe732747c9778 :
∀ (x1 : Finset ℕ) (x2 : ℕ → ℕ → Finset ℕ) (x3 : ℝ), (∀ x4 ∈ x1, ∀ x6 ∈ x1, ↑(x2 x4 x6).card ≤ x3) → ↑(x1.biUnion fun (x5 : ℕ) => x1.biUnion fun (x6 : ℕ) => x2 x5 x6).card ≤ ↑x1.card ^ (2 : ℕ) * x3 := by
  intro x1 x2 x3 h
  have h1 : (x1.biUnion fun x5 => x1.biUnion fun x6 => x2 x5 x6).card ≤
      ∑ x5 ∈ x1, (x1.biUnion fun x6 => x2 x5 x6).card := Finset.card_biUnion_le
  have h2 : ∀ x5 ∈ x1, (x1.biUnion fun x6 => x2 x5 x6).card ≤
      ∑ x6 ∈ x1, (x2 x5 x6).card := fun _ _ => Finset.card_biUnion_le
  have key : ∀ x5 ∈ x1,
      ((x1.biUnion fun x6 => x2 x5 x6).card : ℝ) ≤ (x1.card : ℝ) * x3 := by
    intro x5 hx5
    have hc := h2 x5 hx5
    have hcr : ((x1.biUnion fun x6 => x2 x5 x6).card : ℝ) ≤
        ∑ x6 ∈ x1, ((x2 x5 x6).card : ℝ) := by exact_mod_cast hc
    have hsum : (∑ x6 ∈ x1, ((x2 x5 x6).card : ℝ)) ≤ ∑ _x6 ∈ x1, x3 :=
      Finset.sum_le_sum (fun x6 hx6 => h x5 hx5 x6 hx6)
    have hconst : (∑ _x6 ∈ x1, x3) = (x1.card : ℝ) * x3 := by
      simp [Finset.sum_const, nsmul_eq_mul]
    linarith
  have hsum : (∑ x5 ∈ x1, ((x1.biUnion fun x6 => x2 x5 x6).card : ℝ)) ≤
      ∑ _x5 ∈ x1, (x1.card : ℝ) * x3 := Finset.sum_le_sum key
  have hconst : (∑ _x5 ∈ x1, (x1.card : ℝ) * x3) = (x1.card : ℝ) * ((x1.card : ℝ) * x3) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hcast : (((x1.biUnion fun x5 => x1.biUnion fun x6 => x2 x5 x6).card : ℝ)) ≤
      ∑ x5 ∈ x1, ((x1.biUnion fun x6 => x2 x5 x6).card : ℝ) := by exact_mod_cast h1
  have hpow : (x1.card : ℝ) * ((x1.card : ℝ) * x3) = (x1.card : ℝ) ^ (2 : ℕ) * x3 := by ring
  linarith
