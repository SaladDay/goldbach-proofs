import Mathlib

/-- The assigned statement of L-goldbach-cut-b7db3662848af6dc5dd43254 is false:
the right-hand side `x3 + x4 + ∑_{i<5} 2^(x5 i + 1)` is at least `2 + 2 + 5·2 = 14`
for every choice of the witnesses (primes are `≥ 2`, and each summand is `2^(k+1) ≥ 2`),
while the premise `Even x1` puts no lower bound on `x1` -- `x1 = 0` is even. -/
theorem refutes_L_goldbach_cut_b7db3662848af6dc5dd43254 :
    ¬ (∀ (x1 : ℕ), Even x1 → ∃ (x3 : ℕ) (x4 : ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧
        ∃ (x5 : Fin (5 : ℕ) → ℕ),
          x1 = x3 + x4 + ∑ x6 : Fin (5 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ))) := by
  intro h
  obtain ⟨x3, x4, hp3, hp4, x5, heq⟩ := h 0 ⟨0, rfl⟩
  have hsum : (10 : ℕ) ≤ ∑ x6 : Fin (5 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ)) := by
    calc (10 : ℕ) = ∑ _i : Fin (5 : ℕ), (2 : ℕ) := by simp
      _ ≤ ∑ x6 : Fin (5 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ)) := by
          apply Finset.sum_le_sum
          intro i _
          have h1 : 1 < (2 : ℕ) ^ (x5 i + 1) := Nat.one_lt_two_pow (by omega)
          omega
  have h3 : 2 ≤ x3 := hp3.two_le
  have h4 : 2 ≤ x4 := hp4.two_le
  omega

/-- Sharper form: no even number below `14` is representable, so the statement fails
on seven inputs (`0, 2, 4, 6, 8, 10, 12`), not only on `0`. -/
theorem refutes_small_even :
    ∀ (x1 : ℕ), Even x1 → x1 < 14 →
      ¬ ∃ (x3 : ℕ) (x4 : ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧
        ∃ (x5 : Fin (5 : ℕ) → ℕ),
          x1 = x3 + x4 + ∑ x6 : Fin (5 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ)) := by
  intro x1 _heven hlt ⟨x3, x4, hp3, hp4, x5, heq⟩
  have hsum : (10 : ℕ) ≤ ∑ x6 : Fin (5 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ)) := by
    calc (10 : ℕ) = ∑ _i : Fin (5 : ℕ), (2 : ℕ) := by simp
      _ ≤ ∑ x6 : Fin (5 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ)) := by
          apply Finset.sum_le_sum
          intro i _
          have h1 : 1 < (2 : ℕ) ^ (x5 i + 1) := Nat.one_lt_two_pow (by omega)
          omega
  have h3 : 2 ≤ x3 := hp3.two_le
  have h4 : 2 ≤ x4 := hp4.two_le
  omega

theorem Conjectures.Cuts.Refutee577c99dda4892a92437c1e8 : ¬ (∀ (x1 : ℕ), Even x1 → ∃ (x3 : ℕ) (x4 : ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧ ∃ (x5 : Fin (5 : ℕ) → ℕ), x1 = x3 + x4 + ∑ x6 : Fin (5 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ))) := by
  first
  | exact refutes_small_even
  | exact refutes_L_goldbach_cut_b7db3662848af6dc5dd43254
