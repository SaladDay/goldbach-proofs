import Mathlib

/-!
Diagonal (König) extraction of a Boolean mask.

For a doubly indexed Boolean family `x1`, we build the tree of finite patterns that are
realised by arbitrarily late rows, and take a branch through it via
`exists_seq_forall_proj_of_forall_finite` (Kőnig's lemma, `Mathlib.Order.KonigLemma`).
-/

namespace Conjectures.Cuts.Task026d42ecaec0788098b50eeb_aux

variable (x1 : ℕ → ℕ → Bool)

/-- Patterns of length `i` realised by arbitrarily late rows of `x1`. -/
def Pat (i : ℕ) : Type :=
  {s : Fin i → Bool // ∀ N : ℕ, ∃ m ≥ N, ∀ k : Fin i, x1 m k = s k}

instance (i : ℕ) : Finite (Pat x1 i) :=
  Finite.of_injective (fun p : Pat x1 i => p.1) Subtype.val_injective

instance (i : ℕ) : Nonempty (Pat x1 i) := by
  obtain ⟨s, hs⟩ := Finite.exists_infinite_fiber (fun m : ℕ => (fun k : Fin i => x1 m k))
  refine ⟨⟨s, fun N => ?_⟩⟩
  obtain ⟨m, hms, hm⟩ := (Set.infinite_coe_iff.mp hs).exists_gt N
  exact ⟨m, le_of_lt hm, fun k => congrFun hms k⟩

/-- Restriction of a pattern to a shorter length. -/
def proj {i j : ℕ} (h : i ≤ j) (p : Pat x1 j) : Pat x1 i :=
  ⟨fun k => p.1 ⟨k, lt_of_lt_of_le k.isLt h⟩, fun N => by
    obtain ⟨m, hm, hm'⟩ := p.2 N
    exact ⟨m, hm, fun k => hm' ⟨k, lt_of_lt_of_le k.isLt h⟩⟩⟩

lemma proj_refl ⦃i : ℕ⦄ (a : Pat x1 i) : proj x1 (le_refl i) a = a := by
  apply Subtype.ext
  funext k
  rfl

lemma proj_trans ⦃i j l : ℕ⦄ (hij : i ≤ j) (hjl : j ≤ l) (a : Pat x1 l) :
    proj x1 hij (proj x1 hjl a) = proj x1 (hij.trans hjl) a := by
  apply Subtype.ext
  funext k
  rfl

lemma fiber_finite (i : ℕ) (a : Pat x1 i) :
    {b : Pat x1 (i + 1) | proj x1 (Nat.le_add_right i 1) b = a}.Finite :=
  Set.toFinite _

end Conjectures.Cuts.Task026d42ecaec0788098b50eeb_aux

theorem Conjectures.Cuts.Task026d42ecaec0788098b50eeb :
    ∀ (x1 : ℕ → ℕ → Bool), ∃ (x2 : ℕ → Bool), ∀ (x3 : ℕ), ∃ x4 ≥ x3, ∀ x5 ≤ x3, x1 x4 x5 = x2 x5 := by
  intro x1
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite
    (α := Conjectures.Cuts.Task026d42ecaec0788098b50eeb_aux.Pat x1)
    (Conjectures.Cuts.Task026d42ecaec0788098b50eeb_aux.proj x1)
    (Conjectures.Cuts.Task026d42ecaec0788098b50eeb_aux.proj_refl x1)
    (Conjectures.Cuts.Task026d42ecaec0788098b50eeb_aux.proj_trans x1)
    (Conjectures.Cuts.Task026d42ecaec0788098b50eeb_aux.fiber_finite x1)
  refine ⟨fun k => (f (k + 1)).1 ⟨k, Nat.lt_succ_self k⟩, fun x3 => ?_⟩
  obtain ⟨m, hm, hm'⟩ := (f (x3 + 1)).2 x3
  refine ⟨m, hm, fun x5 hx5 => ?_⟩
  have hcons : (f (x3 + 1)).1 ⟨x5, by omega⟩ = (f (x5 + 1)).1 ⟨x5, Nat.lt_succ_self x5⟩ := by
    have h := congrFun (congrArg Subtype.val (hf (show x5 + 1 ≤ x3 + 1 by omega)))
      ⟨x5, by omega⟩
    dsimp [Conjectures.Cuts.Task026d42ecaec0788098b50eeb_aux.proj] at h
    exact h
  have hrow : x1 m x5 = (f (x3 + 1)).1 ⟨x5, by omega⟩ := hm' ⟨x5, by omega⟩
  exact hrow.trans hcons
