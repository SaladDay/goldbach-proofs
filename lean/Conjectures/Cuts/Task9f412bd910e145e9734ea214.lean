import Mathlib

namespace Conjectures.Cuts.Task9f412bd910e145e9734ea214_aux

theorem card_eq_zero_iff_no_trial_divisor (x1 : ℕ) :
    {x2 ∈ Finset.Icc (2 : ℕ) x1.sqrt | x2 ∣ x1}.card = (0 : ℕ) ↔
      ∀ m, 2 ≤ m → m ≤ x1.sqrt → ¬ m ∣ x1 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h m hm2 hm
    exact h (Finset.mem_Icc.mpr ⟨hm2, hm⟩)
  · intro h m hm
    exact h m (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2

end Conjectures.Cuts.Task9f412bd910e145e9734ea214_aux

theorem Conjectures.Cuts.Task9f412bd910e145e9734ea214 :
    ∀ (x1 : ℕ), Nat.Prime x1 ↔ (2 : ℕ) ≤ x1 ∧
      {x2 ∈ Finset.Icc (2 : ℕ) x1.sqrt | x2 ∣ x1}.card = (0 : ℕ) := by
  intro x1
  rw [Nat.prime_def_le_sqrt,
    Conjectures.Cuts.Task9f412bd910e145e9734ea214_aux.card_eq_zero_iff_no_trial_divisor]
