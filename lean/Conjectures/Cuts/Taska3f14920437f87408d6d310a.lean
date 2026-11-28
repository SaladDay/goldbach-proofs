import Mathlib
import PEqualNP.Outside.L_goldbach_arc_major_floor

namespace Conjectures.Cuts.Taska3f14920437f87408d6d310a_aux

noncomputable def w (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k:ℝ) else 0
noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x : ℝ) : ℂ) * Complex.I)
noncomputable def S (n : ℕ) (t : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), (w k : ℂ) * E ((k:ℝ)*t)
def Q (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2
def arcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ)/((q:ℝ)*(n:ℝ))}
noncomputable def f (n : ℕ) (t : ℝ) : ℂ := (S n t)^2 * E (-(n:ℝ)*t)
noncomputable def major (n : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1, (arcs n).indicator (f n) t

theorem floor_ex : ∃ (c : ℝ) (N : ℕ), 0 < c ∧ ∀ n : ℕ, N ≤ n → Even n → c*(n:ℝ) ≤ (major n).re :=
  PEqualNP.Outside.L_goldbach_arc_major_floor

theorem arcs_eq (n : ℕ) :
    {x10 : ℝ | ∃ (x11 : ℕ) (x12 : ℕ), (1 : ℕ) ≤ x11 ∧
      x11 ≤ Nat.log (2 : ℕ) (n + (2 : ℕ)) ^ (2 : ℕ) ∧ x12 ≤ x11 ∧ x12.Coprime x11 ∧
      |x10 - (↑x12 : ℝ) / ↑x11| ≤ (↑(Nat.log (2 : ℕ) (n + (2 : ℕ))) : ℝ) ^ (2 : ℕ) /
        (↑x11 * ↑n)} = arcs n := by
  unfold arcs Q
  ext t
  constructor
  · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
    exact ⟨q, a, h1, h2, h3, h4, by simpa only [Nat.cast_pow] using h5⟩
  · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
    exact ⟨q, a, h1, h2, h3, h4, by simpa only [Nat.cast_pow] using h5⟩

theorem coef_eq (k : ℕ) :
    (if Nat.Prime k then (↑(Real.log (↑k : ℝ)) : ℂ) else (0 : ℂ)) = (w k : ℂ) := by
  unfold w
  split_ifs <;> simp

theorem exp_eq (k : ℕ) (t : ℝ) :
    Complex.exp ((↑((2 : ℝ) * Real.pi * (↑k : ℝ) * t) : ℂ) * Complex.I) = E ((↑k : ℝ) * t) := by
  unfold E
  rw [show (2 : ℝ) * Real.pi * (↑k : ℝ) * t = 2 * Real.pi * ((↑k : ℝ) * t) by ring]

theorem exp_eq' (n : ℕ) (t : ℝ) :
    Complex.exp ((↑((2 : ℝ) * Real.pi * -(↑n : ℝ) * t) : ℂ) * Complex.I) = E (-(↑n : ℝ) * t) := by
  unfold E
  rw [show (2 : ℝ) * Real.pi * -(↑n : ℝ) * t = 2 * Real.pi * (-(↑n : ℝ) * t) by ring]

theorem f_eq (n : ℕ) (t : ℝ) :
    (∑ x11 ∈ Finset.range (n + (1 : ℕ)),
        (if Nat.Prime x11 then (↑(Real.log (↑x11 : ℝ)) : ℂ) else (0 : ℂ)) *
          Complex.exp ((↑((2 : ℝ) * Real.pi * (↑x11 : ℝ) * t) : ℂ) * Complex.I)) ^ (2 : ℕ) *
        Complex.exp ((↑((2 : ℝ) * Real.pi * -(↑n : ℝ) * t) : ℂ) * Complex.I) = f n t := by
  unfold f
  rw [exp_eq' n t]
  refine congrArg (fun z => z ^ (2 : ℕ) * E (-(↑n : ℝ) * t)) ?_
  unfold S
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coef_eq k, exp_eq k t]

theorem major_eq (n : ℕ) :
    (∫ (x9 : ℝ) in (0 : ℝ)..(1 : ℝ),
      {x10 : ℝ | ∃ (x11 : ℕ) (x12 : ℕ), (1 : ℕ) ≤ x11 ∧
        x11 ≤ Nat.log (2 : ℕ) (n + (2 : ℕ)) ^ (2 : ℕ) ∧ x12 ≤ x11 ∧ x12.Coprime x11 ∧
        |x10 - (↑x12 : ℝ) / ↑x11| ≤ (↑(Nat.log (2 : ℕ) (n + (2 : ℕ))) : ℝ) ^ (2 : ℕ) /
          (↑x11 * ↑n)}.indicator
        (fun (x10 : ℝ) =>
          (∑ x11 ∈ Finset.range (n + (1 : ℕ)),
            (if Nat.Prime x11 then (↑(Real.log (↑x11 : ℝ)) : ℂ) else (0 : ℂ)) *
              Complex.exp ((↑((2 : ℝ) * Real.pi * (↑x11 : ℝ) * x10) : ℂ) * Complex.I)) ^
            (2 : ℕ) *
            Complex.exp ((↑((2 : ℝ) * Real.pi * -(↑n : ℝ) * x10) : ℂ) * Complex.I)) x9) =
      major n := by
  unfold major
  rw [arcs_eq n]
  refine intervalIntegral.integral_congr fun t _ => ?_
  by_cases ht : t ∈ arcs n
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, f_eq n t]
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]

end Conjectures.Cuts.Taska3f14920437f87408d6d310a_aux

theorem Conjectures.Cuts.Taska3f14920437f87408d6d310a :
∃ (x1 : ℝ), (0 : ℝ) < x1 ∧ ∃ (x2 : ℕ), ∀ (x3 : ℕ), x2 ≤ x3 → ∀ (x5 : ℕ), x3 < x5 → x5 ≤ (2 : ℕ) * x3 → Even x5 → x1 * ↑x5 ≤ (∫ (x9 : ℝ) in (0 : ℝ)..(1 : ℝ), {x10 : ℝ | ∃ (x11 : ℕ) (x12 : ℕ), (1 : ℕ) ≤ x11 ∧ x11 ≤ Nat.log (2 : ℕ) (x5 + (2 : ℕ)) ^ (2 : ℕ) ∧ x12 ≤ x11 ∧ x12.Coprime x11 ∧ |x10 - ↑x12 / ↑x11| ≤ ↑(Nat.log (2 : ℕ) (x5 + (2 : ℕ))) ^ (2 : ℕ) / (↑x11 * ↑x5)}.indicator (fun (x10 : ℝ) => (∑ x11 ∈ Finset.range (x5 + (1 : ℕ)), (if Nat.Prime x11 then ↑(Real.log ↑x11) else (0 : ℂ)) * Complex.exp (↑((2 : ℝ) * Real.pi * ↑x11 * x10) * Complex.I)) ^ (2 : ℕ) * Complex.exp (↑((2 : ℝ) * Real.pi * -↑x5 * x10) * Complex.I)) x9).re := by
  obtain ⟨c, N, hc, hfloor⟩ := Conjectures.Cuts.Taska3f14920437f87408d6d310a_aux.floor_ex
  refine ⟨c, hc, N, fun x3 hx3 x5 hlt _ heven => ?_⟩
  have hN : N ≤ x5 := le_trans hx3 (le_of_lt hlt)
  rw [Conjectures.Cuts.Taska3f14920437f87408d6d310a_aux.major_eq x5]
  exact hfloor x5 hN heven
