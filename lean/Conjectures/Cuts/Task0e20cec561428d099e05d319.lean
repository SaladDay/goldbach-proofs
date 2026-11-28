import Mathlib

/-!
Dependence of the reservoir size and of the exceptional-window count on the mask
restricted to the window endpoint.

For a mask `m : ℕ → Bool` the reservoir at `n` is
`x1 m n = #{k ∈ Finset.Icc 1 n | m k = true ∧ Nat.Prime (n - k)}` and the exceptional
count of the window `(a, a + b]` at threshold `r` is
`x2 m a b r = #{n ∈ Finset.Ioc a (a + b) | Even n ∧ (x1 m n : ℝ) < r}`.

If two masks `m1`, `m2` agree on every index `k ≤ a + b`, then:

* the two counts of true entries on `Finset.Icc 1 a` agree, because every index of that
  finset is `≤ a ≤ a + b` (`Finset.filter_congr`);
* for every `n ∈ Finset.Ioc a (a + b)` the reservoirs `x1 m1 n` and `x1 m2 n` agree, since
  every index of `Finset.Icc 1 n` is `≤ n ≤ a + b`; hence the two filtered windows have the
  same cardinality (`Finset.filter_congr` again, after rewriting with the reservoir equality).

Quantifiers are exactly as stated: arbitrary masks, arbitrary window `a`, length `b`,
arbitrary real threshold `r` (no sign or size assumption on `r`), and the single hypothesis
that the masks agree up to `a + b`.  No estimate is needed: the statement is a pure
congruence of two filtered finsets.

Self-contained: Mathlib only, one private auxiliary lemma in the aux namespace.
Method adapted from the fleet proofs of the sibling cuts (filtered-cardinality congruences),
e.g. `L-goldbach-cut-e8cf2ce3af90d678946e0ff7` and `L-goldbach-cut-ecdd8286c6771351e50a0f23`.
-/

namespace Conjectures.Cuts.Task0e20cec561428d099e05d319_aux

/-- Equal masks up to the endpoint give equal reservoirs. -/
private lemma reservoir_congr {m1 m2 : ℕ → Bool} {a b : ℕ}
    (h : ∀ k ≤ a + b, m1 k = m2 k) (n : ℕ) (hn : n ≤ a + b) :
    {k ∈ Finset.Icc (1 : ℕ) n | m1 k = Bool.true ∧ Nat.Prime (n - k)}.card =
    {k ∈ Finset.Icc (1 : ℕ) n | m2 k = Bool.true ∧ Nat.Prime (n - k)}.card := by
  refine congrArg Finset.card (Finset.filter_congr (fun k hk => ?_))
  have hk' : k ≤ a + b := le_trans (Finset.mem_Icc.mp hk).2 hn
  rw [h k hk']

end Conjectures.Cuts.Task0e20cec561428d099e05d319_aux

theorem Conjectures.Cuts.Task0e20cec561428d099e05d319 :
    have x1 : (ℕ → Bool) → ℕ → ℕ := fun (x1 : ℕ → Bool) (x2 : ℕ) => {x3 ∈ Finset.Icc (1 : ℕ) x2 | x1 x3 = Bool.true ∧ Nat.Prime (x2 - x3)}.card; have x2 : (ℕ → Bool) → ℕ → ℕ → ℝ → ℕ := fun (x2 : ℕ → Bool) (x3 x4 : ℕ) (x5 : ℝ) => {x6 ∈ Finset.Ioc x3 (x3 + x4) | Even x6 ∧ ↑(x1 x2 x6) < x5}.card; ∀ (x3 x4 : ℕ → Bool) (x5 x6 : ℕ) (x7 : ℝ), (∀ x8 ≤ x5 + x6, x3 x8 = x4 x8) → {x9 ∈ Finset.Icc (1 : ℕ) x5 | x3 x9 = Bool.true}.card = {x9 ∈ Finset.Icc (1 : ℕ) x5 | x4 x9 = Bool.true}.card ∧ x2 x3 x5 x6 x7 = x2 x4 x5 x6 x7 := by
  show ∀ (m1 m2 : ℕ → Bool) (a b : ℕ) (r : ℝ), (∀ k ≤ a + b, m1 k = m2 k) →
      {n ∈ Finset.Icc (1 : ℕ) a | m1 n = Bool.true}.card =
        {n ∈ Finset.Icc (1 : ℕ) a | m2 n = Bool.true}.card ∧
      {n ∈ Finset.Ioc a (a + b) | Even n ∧
          ((↑({k ∈ Finset.Icc (1 : ℕ) n | m1 k = Bool.true ∧ Nat.Prime (n - k)}.card) : ℝ) < r)}.card =
      {n ∈ Finset.Ioc a (a + b) | Even n ∧
          ((↑({k ∈ Finset.Icc (1 : ℕ) n | m2 k = Bool.true ∧ Nat.Prime (n - k)}.card) : ℝ) < r)}.card
  intro m1 m2 a b r h
  refine ⟨?_, ?_⟩
  · refine congrArg Finset.card (Finset.filter_congr (fun n hn => ?_))
    have hn' : n ≤ a + b := le_trans (Finset.mem_Icc.mp hn).2 (Nat.le_add_right a b)
    rw [h n hn']
  · refine congrArg Finset.card (Finset.filter_congr (fun n hn => ?_))
    have hn' : n ≤ a + b := (Finset.mem_Ioc.mp hn).2
    have hc := Conjectures.Cuts.Task0e20cec561428d099e05d319_aux.reservoir_congr h n hn'
    rw [hc]
