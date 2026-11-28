import Mathlib

/-!
Solving the modulo-six equation on a compressed progression.

The multiplier `x1` is a unit modulo six, so `x1 % 6` is `1` or `5`.  Writing
`a = x3 % 6` and `b = x2 % 6` (both `< 6`), the target `(x1 * x3 + x2) % 6 = 4` reduces by
`Nat.add_mod` / `Nat.mul_mod` to a linear congruence in `a` and `b`:

* `x1 % 6 = 1`: `a + b ≡ 4 (mod 6)`, i.e. `a = (10 - b) % 6` (ten is four modulo six);
* `x1 % 6 = 5`: `-a + b ≡ 4 (mod 6)`, i.e. `a = (b + 2) % 6`.

The two congruences are discharged by `omega` from `a < 6`, `b < 6`.  The unit residue split
comes from coprimality with two and with three.

Self-contained: Mathlib only, one auxiliary lemma.
-/

namespace Conjectures.Cuts.Task8691fedee32e90b5ba19ee70_aux

/-- A natural number coprime to six is congruent to `1` or to `5` modulo six. -/
lemma unit_mod_six (x : ℕ) (h : x.Coprime 6) : x % 6 = 1 ∨ x % 6 = 5 := by
  have h2 : x % 2 ≠ 0 := by
    intro hd
    have hdv : (2 : ℕ) ∣ x := Nat.dvd_of_mod_eq_zero hd
    exact absurd (Nat.Coprime.of_dvd_left hdv h) (by decide)
  have h3 : x % 3 ≠ 0 := by
    intro hd
    have hdv : (3 : ℕ) ∣ x := Nat.dvd_of_mod_eq_zero hd
    exact absurd (Nat.Coprime.of_dvd_left hdv h) (by decide)
  omega

end Conjectures.Cuts.Task8691fedee32e90b5ba19ee70_aux

theorem Conjectures.Cuts.Task8691fedee32e90b5ba19ee70 :
    ∀ (x1 x2 x3 : ℕ), x1.Coprime (6 : ℕ) → ((x1 * x3 + x2) % (6 : ℕ) = (4 : ℕ) ↔ x3 % (6 : ℕ) = if x1 % (6 : ℕ) = (1 : ℕ) then ((10 : ℕ) - x2 % (6 : ℕ)) % (6 : ℕ) else (x2 % (6 : ℕ) + (2 : ℕ)) % (6 : ℕ)) := by
  intro x1 x2 x3 h
  have key : (x1 * x3 + x2) % (6 : ℕ) = ((((x1 % (6 : ℕ)) * (x3 % (6 : ℕ))) % (6 : ℕ)) + x2 % (6 : ℕ)) % (6 : ℕ) := by
    rw [Nat.add_mod, Nat.mul_mod]
  have ha : x3 % (6 : ℕ) < 6 := Nat.mod_lt _ (by norm_num)
  have hb : x2 % (6 : ℕ) < 6 := Nat.mod_lt _ (by norm_num)
  rw [key]
  rcases Conjectures.Cuts.Task8691fedee32e90b5ba19ee70_aux.unit_mod_six x1 h with h1 | h1
  · simp [h1]
    omega
  · simp [h1, show ¬ (5 : ℕ) = 1 by norm_num]
    omega
