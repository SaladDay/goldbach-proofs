import Mathlib

/-!
Worst reduced pair chosen simultaneously for every modulus of a finite set.

For a modulus `n ≥ 2` the set of reduced residues below `n` is nonempty (it contains `1`),
so the finite product of two copies of it attains the maximum of any real-valued function
on pairs of reduced residues.  Choosing one maximiser per element of the finite set of
moduli and leaving the function arbitrary elsewhere gives the required simultaneous choice.
-/

namespace Conjectures.Cuts.Task2381f715cb778cea010d810a_aux

theorem exists_pair (x2 : ℕ → ℕ → ℕ → ℝ) (n : ℕ) (hn : 2 ≤ n) :
    ∃ a b : ℕ, a < n ∧ b < n ∧ Nat.Coprime a n ∧ Nat.Coprime b n ∧
      ∀ x y : ℕ, x < n → y < n → Nat.Coprime x n → Nat.Coprime y n →
        x2 n x y ≤ x2 n a b := by
  classical
  set S : Finset ℕ := (Finset.range n).filter (fun x => Nat.Coprime x n)
  have h1 : (1 : ℕ) ∈ S := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩
    simp
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image (S ×ˢ S) (fun q => x2 n q.1 q.2)
    ⟨(1, 1), Finset.mem_product.mpr ⟨h1, h1⟩⟩
  have hp1 : p.1 ∈ S := (Finset.mem_product.mp hp).1
  have hp2 : p.2 ∈ S := (Finset.mem_product.mp hp).2
  have hp1' := Finset.mem_filter.mp hp1
  have hp2' := Finset.mem_filter.mp hp2
  refine ⟨p.1, p.2, Finset.mem_range.mp hp1'.1, Finset.mem_range.mp hp2'.1, hp1'.2, hp2'.2, ?_⟩
  intro x y hx hy hcx hcy
  have hxy : (x, y) ∈ S ×ˢ S := Finset.mem_product.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx, hcx⟩,
     Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hy, hcy⟩⟩
  exact hmax (x, y) hxy

end Conjectures.Cuts.Task2381f715cb778cea010d810a_aux

theorem Conjectures.Cuts.Task2381f715cb778cea010d810a :
∀ (x1 : Finset ℕ) (x2 : ℕ → ℕ → ℕ → ℝ), (∀ x3 ∈ x1, (2 : ℕ) ≤ x3) → ∃ (x4 : ℕ → ℕ) (x5 : ℕ → ℕ), ∀ x6 ∈ x1, x4 x6 < x6 ∧ x5 x6 < x6 ∧ (x4 x6).Coprime x6 ∧ (x5 x6).Coprime x6 ∧ ∀ (x8 x9 : ℕ), x8 < x6 → x9 < x6 → x8.Coprime x6 → x9.Coprime x6 → x2 x6 x8 x9 ≤ x2 x6 (x4 x6) (x5 x6) := by
  intro x1 x2 h
  classical
  have hex : ∀ n : ℕ, n ∈ x1 → ∃ a b : ℕ, a < n ∧ b < n ∧ Nat.Coprime a n ∧
      Nat.Coprime b n ∧ ∀ x y : ℕ, x < n → y < n → Nat.Coprime x n → Nat.Coprime y n →
        x2 n x y ≤ x2 n a b :=
    fun n hn => Conjectures.Cuts.Task2381f715cb778cea010d810a_aux.exists_pair x2 n (h n hn)
  let x4 : ℕ → ℕ := fun n => if hn : n ∈ x1 then Classical.choose (hex n hn) else 0
  let x5 : ℕ → ℕ := fun n =>
    if hn : n ∈ x1 then Classical.choose (Classical.choose_spec (hex n hn)) else 0
  refine ⟨x4, x5, fun x6 hx6 => ?_⟩
  have hx4 : x4 x6 = Classical.choose (hex x6 hx6) := by simp [x4, hx6]
  have hx5 : x5 x6 = Classical.choose (Classical.choose_spec (hex x6 hx6)) := by
    simp [x5, hx6]
  have hspec := Classical.choose_spec (Classical.choose_spec (hex x6 hx6))
  rw [hx4, hx5]
  exact hspec
