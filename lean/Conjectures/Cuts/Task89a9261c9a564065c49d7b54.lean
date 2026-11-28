import Mathlib

/-!
Descent of a sum of two squares divisible by three by a factor of nine.

Squares modulo 3 are 0 or 1, so `3 ∣ a ^ 2 + b ^ 2` forces `a % 3 = b % 3 = 0`
(`three_dvd_left` and its mirror image).  Writing `a = 3 * a'` and `b = 3 * b'` gives
`a ^ 2 + b ^ 2 = 9 * (a' ^ 2 + b' ^ 2)`, i.e. nine divides the number and the quotient is again
a sum of two squares.  Conversely, if `9 ∣ x` and `x / 9 = c ^ 2 + d ^ 2`, then
`x = 9 * (x / 9) = (3 * c) ^ 2 + (3 * d) ^ 2`.  The hypothesis `3 ∣ x` is not needed in the
converse direction.

Self-contained: Mathlib only.
-/

namespace Conjectures.Cuts.Task89a9261c9a564065c49d7b54_aux

private lemma three_dvd_left {a b : ℕ} (h : (3 : ℕ) ∣ a ^ (2 : ℕ) + b ^ (2 : ℕ)) : (3 : ℕ) ∣ a := by
  have hmod : (a ^ (2 : ℕ) + b ^ (2 : ℕ)) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  by_contra ha0
  have ha : a % 3 = 1 ∨ a % 3 = 2 := by
    have hlt := Nat.mod_lt a (by decide : (0 : ℕ) < 3)
    have hne : ¬ (a % 3 = 0) := fun hz => ha0 (Nat.dvd_iff_mod_eq_zero.mpr hz)
    omega
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by
    have hlt := Nat.mod_lt b (by decide : (0 : ℕ) < 3)
    omega
  rcases ha with ha | ha <;> rcases hb with hb | hb | hb <;>
    simp [Nat.add_mod, Nat.pow_mod, ha, hb] at hmod

private lemma three_dvd_right {a b : ℕ} (h : (3 : ℕ) ∣ a ^ (2 : ℕ) + b ^ (2 : ℕ)) : (3 : ℕ) ∣ b := by
  have h' : (3 : ℕ) ∣ b ^ (2 : ℕ) + a ^ (2 : ℕ) := by
    rw [Nat.add_comm]; exact h
  exact three_dvd_left h'

end Conjectures.Cuts.Task89a9261c9a564065c49d7b54_aux

theorem Conjectures.Cuts.Task89a9261c9a564065c49d7b54 :
    ∀ (x1 : ℕ), (3 : ℕ) ∣ x1 → ((∃ (x3 : ℕ) (x4 : ℕ), x1 = x3 ^ (2 : ℕ) + x4 ^ (2 : ℕ)) ↔ (9 : ℕ) ∣ x1 ∧ ∃ (x3 : ℕ) (x4 : ℕ), x1 / (9 : ℕ) = x3 ^ (2 : ℕ) + x4 ^ (2 : ℕ)) := by
  intro x1 _hx3
  constructor
  · rintro ⟨a, b, hab⟩
    have h3a : (3 : ℕ) ∣ a := Conjectures.Cuts.Task89a9261c9a564065c49d7b54_aux.three_dvd_left (hab ▸ _hx3)
    have h3b : (3 : ℕ) ∣ b := Conjectures.Cuts.Task89a9261c9a564065c49d7b54_aux.three_dvd_right (hab ▸ _hx3)
    obtain ⟨a', rfl⟩ := h3a
    obtain ⟨b', rfl⟩ := h3b
    have hfact : ((3 : ℕ) * a') ^ (2 : ℕ) + ((3 : ℕ) * b') ^ (2 : ℕ) =
        (9 : ℕ) * (a' ^ (2 : ℕ) + b' ^ (2 : ℕ)) := by ring
    refine ⟨?_, a', b', ?_⟩
    · refine ⟨a' ^ (2 : ℕ) + b' ^ (2 : ℕ), ?_⟩
      rw [hab]; exact hfact
    · rw [hab, hfact, Nat.mul_div_cancel_left _ (by decide : (0 : ℕ) < 9)]
  · rintro ⟨h9, c, d, hcd⟩
    refine ⟨(3 : ℕ) * c, (3 : ℕ) * d, ?_⟩
    have hx : x1 = (9 : ℕ) * (x1 / (9 : ℕ)) := by rw [mul_comm, Nat.div_mul_cancel h9]
    rw [hx, hcd]
    ring

