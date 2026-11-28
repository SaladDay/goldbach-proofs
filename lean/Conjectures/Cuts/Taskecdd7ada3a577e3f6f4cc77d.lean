import Mathlib

/-!
Recover the reflected prime's prescribed residue from the admissible target class.

The target `x4` sits in the class `x2 + x3` modulo `x1`, with `x2, x3 < x1`.  A prime
`x8 ≤ x4` in the class `x2` therefore forces the reflection `x4 - x8` into the class `x3`:
`(x4 - x8) + x8 = x4`, so modulo `x1` the residues `(x4 - x8) % x1 + x2` and `x3 + x2`
agree, and cancelling `x2` (a constant summand) gives `(x4 - x8) % x1 ≡ x3`, which is an
equality because both sides are reduced.  Hence the two-prime representation with prescribed
classes is equivalent to the one-variable sieve over `x8 ∈ [2, x4]`.
-/

namespace Conjectures.Cuts.Taskecdd7ada3a577e3f6f4cc77d_aux

theorem reflected_residue {x1 x2 x3 x4 x8 : ℕ}
    (_h2 : x2 < x1) (h3 : x3 < x1)
    (h4 : x4 % x1 = (x2 + x3) % x1)
    (hmod8 : x8 % x1 = x2) (hle : x8 ≤ x4) :
    (x4 - x8) % x1 = x3 := by
  have hsum : (x4 - x8) + x8 = x4 := Nat.sub_add_cancel hle
  have hlhs : ((x4 - x8) % x1 + x2) % x1 = x4 % x1 := by
    calc ((x4 - x8) % x1 + x2) % x1
        = ((x4 - x8) % x1 + x8 % x1) % x1 := by rw [hmod8]
      _ = ((x4 - x8) + x8) % x1 := (Nat.add_mod _ _ _).symm
      _ = x4 % x1 := by rw [hsum]
  have hrhs : (x3 + x2) % x1 = x4 % x1 := by
    rw [h4, Nat.add_comm]
  have hme : Nat.ModEq x1 ((x4 - x8) % x1 + x2) (x3 + x2) := by
    show ((x4 - x8) % x1 + x2) % x1 = (x3 + x2) % x1
    rw [hlhs, hrhs]
  have hcanc : Nat.ModEq x1 ((x4 - x8) % x1) x3 :=
    Nat.ModEq.add_right_cancel' x2 hme
  have hlt : (x4 - x8) % x1 < x1 := Nat.mod_lt _ (by omega)
  have hred : ((x4 - x8) % x1) % x1 = x3 % x1 := hcanc
  rw [Nat.mod_mod, Nat.mod_eq_of_lt h3] at hred
  exact hred

end Conjectures.Cuts.Taskecdd7ada3a577e3f6f4cc77d_aux

theorem Conjectures.Cuts.Taskecdd7ada3a577e3f6f4cc77d :
∀ (x1 x2 x3 x4 : ℕ), x2 < x1 → x3 < x1 → x4 % x1 = (x2 + x3) % x1 → ((∃ (x8 : ℕ) (x9 : ℕ), Nat.Prime x8 ∧ Nat.Prime x9 ∧ x8 + x9 = x4 ∧ x8 % x1 = x2 ∧ x9 % x1 = x3) ↔ ∃ x8 ∈ Finset.Icc (2 : ℕ) x4, Nat.Prime x8 ∧ x8 % x1 = x2 ∧ Nat.Prime (x4 - x8)) := by
  intro x1 x2 x3 x4 h2 h3 h4
  constructor
  · rintro ⟨x8, x9, hp8, hp9, hsum, hmod8, hmod9⟩
    have hle : x8 ≤ x4 := by omega
    refine ⟨x8, Finset.mem_Icc.mpr ⟨hp8.two_le, hle⟩, hp8, hmod8, ?_⟩
    have hsub : x4 - x8 = x9 := by omega
    rw [hsub]
    exact hp9
  · rintro ⟨x8, hmem, hp8, hmod8, hp9⟩
    have hle : x8 ≤ x4 := (Finset.mem_Icc.mp hmem).2
    refine ⟨x8, x4 - x8, hp8, hp9, ?_, hmod8, ?_⟩
    · omega
    exact Conjectures.Cuts.Taskecdd7ada3a577e3f6f4cc77d_aux.reflected_residue h2 h3 h4 hmod8 hle
