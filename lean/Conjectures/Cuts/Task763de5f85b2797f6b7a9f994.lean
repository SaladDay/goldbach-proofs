import Mathlib

/-!
Separation of the summand three on the target `6 * x2 + 4`.

`x1 n` is the Chen condition `n` prime and `n + 2` with at most two prime factors counted
with multiplicity.  If `x4 + x5 = 6 * x2 + 4` with `x4, x5` Chen, then both are odd primes
(a summand `2` would force the other one to be the even prime `2`, giving `4 < 10`), so the
sum is `1` modulo `3` and the residues of the two primes modulo `3` are `(0, 1)`, `(1, 0)` or
`(2, 2)`.  In the first two cases the summand congruent to `0` modulo `3` is `3`, and the
other one is `6 * x2 + 1`; in the third case both primes are `5` modulo `6`, which writes
them as `6 * x4' + 5` and `6 * x5' + 5` with `x4' + x5' + 1 = x2`.  The converse is
immediate arithmetic.

Self-contained: Mathlib only.
-/

theorem Conjectures.Cuts.Task763de5f85b2797f6b7a9f994 :
    have x1 : ℕ → Prop := fun (x1 : ℕ) => Nat.Prime x1 ∧ (x1 + (2 : ℕ)).primeFactorsList.length ≤ (2 : ℕ); ∀ (x2 : ℕ), (1 : ℕ) ≤ x2 → ((∃ (x4 : ℕ) (x5 : ℕ), x1 x4 ∧ x1 x5 ∧ x4 + x5 = (6 : ℕ) * x2 + (4 : ℕ)) ↔ x1 ((6 : ℕ) * x2 + (1 : ℕ)) ∨ ∃ (x4 : ℕ) (x5 : ℕ), x4 + x5 + (1 : ℕ) = x2 ∧ x1 ((6 : ℕ) * x4 + (5 : ℕ)) ∧ x1 ((6 : ℕ) * x5 + (5 : ℕ))) := by
  intro x1 x2 hx2
  dsimp only [x1]
  constructor
  · rintro ⟨x4, x5, hx4, hx5, hsum⟩
    have hp4 : Nat.Prime x4 := hx4.1
    have hp5 : Nat.Prime x5 := hx5.1
    have h4ne : x4 ≠ 2 := by
      intro h
      have h5odd : x5 % 2 = 1 := Nat.odd_iff.mp (hp5.odd_of_ne_two (by omega))
      omega
    have h5ne : x5 ≠ 2 := by
      intro h
      have h4odd : x4 % 2 = 1 := Nat.odd_iff.mp (hp4.odd_of_ne_two (by omega))
      omega
    have h4odd : x4 % 2 = 1 := Nat.odd_iff.mp (hp4.odd_of_ne_two h4ne)
    have h5odd : x5 % 2 = 1 := Nat.odd_iff.mp (hp5.odd_of_ne_two h5ne)
    have h4m : x4 % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have h5m : x5 % 3 < 3 := Nat.mod_lt _ (by norm_num)
    by_cases h40 : x4 % 3 = 0
    · left
      have h3dvd : 3 ∣ x4 := Nat.dvd_of_mod_eq_zero h40
      have hx4eq : x4 = 3 := by
        rcases (Nat.dvd_prime hp4).mp h3dvd with h | h
        · omega
        · omega
      have hx5eq : x5 = 6 * x2 + 1 := by omega
      rw [← hx5eq]
      exact hx5
    · by_cases h41 : x4 % 3 = 1
      · left
        have h50 : x5 % 3 = 0 := by omega
        have h3dvd : 3 ∣ x5 := Nat.dvd_of_mod_eq_zero h50
        have hx5eq : x5 = 3 := by
          rcases (Nat.dvd_prime hp5).mp h3dvd with h | h
          · omega
          · omega
        have hx4eq : x4 = 6 * x2 + 1 := by omega
        rw [← hx4eq]
        exact hx4
      · right
        have h42 : x4 % 3 = 2 := by omega
        have h52 : x5 % 3 = 2 := by omega
        have h46 : x4 % 6 = 5 := by omega
        have h56 : x5 % 6 = 5 := by omega
        have hd4 : x4 = 6 * (x4 / 6) + x4 % 6 := (Nat.div_add_mod x4 6).symm
        have hd5 : x5 = 6 * (x5 / 6) + x5 % 6 := (Nat.div_add_mod x5 6).symm
        refine ⟨x4 / 6, x5 / 6, by omega, ?_, ?_⟩
        · have heq : 6 * (x4 / 6) + 5 = x4 := by omega
          rw [heq]
          exact hx4
        · have heq : 6 * (x5 / 6) + 5 = x5 := by omega
          rw [heq]
          exact hx5
  · rintro (h | ⟨x4, x5, hsum, hx4, hx5⟩)
    · refine ⟨3, 6 * x2 + 1, ?_, h, by omega⟩
      refine ⟨by norm_num, ?_⟩
      have h5 : (3 : ℕ) + 2 = 5 := by norm_num
      rw [h5, Nat.primeFactorsList_prime (by norm_num : Nat.Prime 5)]
      simp
    · exact ⟨6 * x4 + 5, 6 * x5 + 5, hx4, hx5, by omega⟩
