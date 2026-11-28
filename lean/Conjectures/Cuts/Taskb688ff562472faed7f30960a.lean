import Mathlib

namespace Conjectures.Cuts.Taskb688ff562472faed7f30960a_aux

/-- A prime dividing a product of two primes is one of them. -/
lemma prime_eq_of_dvd {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (h : p ∣ q) :
    p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp h

/-- In a representation `n = p + r * v` with `p, r, v` prime, `p ∣ n` and `r ∤ n`,
the summand `p` is the larger factor `v`. -/
lemma summand_eq {n p r v : ℕ} (hp : Nat.Prime p) (hr : Nat.Prime r) (hv : Nat.Prime v)
    (hn : n = p + r * v) (hpn : p ∣ n) (hnr : ¬ r ∣ n) : p = v := by
  have hprv : p ∣ r * v := by
    rw [hn] at hpn
    exact (Nat.dvd_add_self_left).mp hpn
  rcases ((Nat.Prime.dvd_mul hp).mp hprv) with h | h
  · exfalso
    have hpr : p = r := prime_eq_of_dvd hp hr h
    refine hnr ?_
    refine ⟨1 + v, ?_⟩
    rw [hn, hpr]
    ring
  · exact prime_eq_of_dvd hp hv h

end Conjectures.Cuts.Taskb688ff562472faed7f30960a_aux

theorem Conjectures.Cuts.Taskb688ff562472faed7f30960a :
    ∀ (x1 x2 x3 x4 x5 x6 x7 : ℕ), Nat.Prime x2 → Nat.Prime x3 → Nat.Prime x4 → x3 < x4 →
      ¬x3 ∣ x1 → x1 = x2 + x3 * x4 → x2 ∣ x1 → Nat.Prime x5 → Nat.Prime x6 → Nat.Prime x7 →
      x6 < x7 → ¬x6 ∣ x1 → x1 = x5 + x6 * x7 → x5 ∣ x1 → x2 = x5 := by
  intro x1 x2 x3 x4 x5 x6 x7 h2 h3 h4 h34 h3n h1 h2n h5 h6 h7 h67 h6n h1' h5n
  have h24 : x2 = x4 :=
    Conjectures.Cuts.Taskb688ff562472faed7f30960a_aux.summand_eq h2 h3 h4 h1 h2n h3n
  have h57 : x5 = x7 :=
    Conjectures.Cuts.Taskb688ff562472faed7f30960a_aux.summand_eq h5 h6 h7 h1' h5n h6n
  have hfac4 : x1 = x4 * (x3 + 1) := by rw [h1, h24]; ring
  have hfac7 : x1 = x7 * (x6 + 1) := by rw [h1', h57]; ring
  have hd4 : x4 ∣ x7 * (x6 + 1) := by rw [← hfac7]; exact ⟨x3 + 1, hfac4⟩
  have hd7 : x7 ∣ x4 * (x3 + 1) := by rw [← hfac4]; exact ⟨x6 + 1, hfac7⟩
  have h44 : x4 = x7 := by
    by_cases h : x4 = x7
    · exact h
    · have hd4' : x4 ∣ x6 + 1 := by
        rcases ((Nat.Prime.dvd_mul h4).mp hd4) with hh | hh
        · exact absurd (Conjectures.Cuts.Taskb688ff562472faed7f30960a_aux.prime_eq_of_dvd
            h4 h7 hh) h
        · exact hh
      have hd7' : x7 ∣ x3 + 1 := by
        rcases ((Nat.Prime.dvd_mul h7).mp hd7) with hh | hh
        · exact absurd (Conjectures.Cuts.Taskb688ff562472faed7f30960a_aux.prime_eq_of_dvd
            h7 h4 hh).symm h
        · exact hh
      have l4 : x4 ≤ x6 + 1 := Nat.le_of_dvd (Nat.succ_pos x6) hd4'
      have l7 : x7 ≤ x3 + 1 := Nat.le_of_dvd (Nat.succ_pos x3) hd7'
      have l34 : x3 + 1 ≤ x4 := h34
      omega
  rw [h24, h57]
  exact h44
