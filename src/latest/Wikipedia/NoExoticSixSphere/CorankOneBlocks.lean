import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.Abel

/-!
# Actual block coordinates for operators near corank one

Split the source as `E × ℝ` and the target as `E × F`. When the leading
square block is invertible, eliminating that block leaves one residual vector
in `F`. The operator is injective exactly when this vector is nonzero.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.CorankOne

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

abbrev BlockMap (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] := (E × ℝ) →L[ℝ] E × F

def leading (L : BlockMap E F) : E →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E F).comp (L.comp (ContinuousLinearMap.inl ℝ E ℝ))

def bottom (L : BlockMap E F) : E →L[ℝ] F :=
  (ContinuousLinearMap.snd ℝ E F).comp (L.comp (ContinuousLinearMap.inl ℝ E ℝ))

def column (L : BlockMap E F) : E × F := L (0, 1)

def residual (L : BlockMap E F) : F :=
  (column L).2 - bottom L ((leading L).inverse (column L).1)

theorem block_apply (L : BlockMap E F) (x : E) (t : ℝ) :
    L (x, t) = (leading L x + t • (column L).1, bottom L x + t • (column L).2) := by
  have he : (x, t) = (x, 0) + t • (0, (1 : ℝ)) := by ext <;> simp
  calc
    L (x, t) = L (x, 0) + t • L (0, 1) := by rw [he, map_add, map_smul]
    _ = _ := rfl

theorem kernel_iff (L : BlockMap E F) (hL : (leading L).IsInvertible) (x : E) (t : ℝ) :
    L (x, t) = 0 ↔
      x = (-t) • (leading L).inverse (column L).1 ∧ t • residual L = 0 := by
  constructor
  · intro h
    have h₁ : leading L x + t • (column L).1 = 0 := by
      have he := congrArg Prod.fst h
      rwa [block_apply] at he
    have h₂ : bottom L x + t • (column L).2 = 0 := by
      have he := congrArg Prod.snd h
      rwa [block_apply] at he
    have hx : x = (-t) • (leading L).inverse (column L).1 := by
      apply hL.injective
      rw [map_smul, hL.self_apply_inverse]
      simpa only [neg_smul] using eq_neg_of_add_eq_zero_left h₁
    refine ⟨hx, ?_⟩
    rw [hx, map_smul, neg_smul] at h₂
    simpa only [residual, smul_sub, sub_eq_add_neg, smul_add, smul_neg, add_comm] using h₂
  · rintro ⟨hx, ht⟩
    rw [block_apply, hx]
    apply Prod.ext
    · change leading L ((-t) • (leading L).inverse (column L).1) + t • (column L).1 = 0
      rw [map_smul, hL.self_apply_inverse, neg_smul, neg_add_cancel]
    · change bottom L ((-t) • (leading L).inverse (column L).1) + t • (column L).2 = 0
      rw [map_smul, neg_smul]
      simpa only [residual, smul_sub, sub_eq_add_neg, smul_add, smul_neg, add_comm] using ht

theorem injective_iff_residual_ne_zero (L : BlockMap E F) (hL : (leading L).IsInvertible) :
    Injective L ↔ residual L ≠ 0 := by
  constructor
  · intro hi hr
    have hz : L (-(leading L).inverse (column L).1, 1) = 0 := by
      apply (kernel_iff L hL _ _).mpr
      simp [hr]
    have he := hi (hz.trans L.map_zero.symm)
    exact one_ne_zero (congrArg Prod.snd he)
  · intro hr
    apply (injective_iff_map_eq_zero _).mpr
    rintro ⟨x, t⟩ h
    obtain ⟨hx, ht⟩ := (kernel_iff L hL x t).mp h
    have ht₀ : t = 0 := (smul_eq_zero.mp ht).resolve_right hr
    rw [ht₀, neg_zero, zero_smul] at hx
    exact Prod.ext hx ht₀

theorem vector_eq_of_head_zero (L : BlockMap E F) (hL : (leading L).IsInvertible)
    (x : E) (hx : (L (x, 1)).1 = 0) :
    x = -(leading L).inverse (column L).1 := by
  have he : leading L x + (column L).1 = 0 := by
    simpa only [block_apply, one_smul] using hx
  apply hL.injective
  rw [map_neg, hL.self_apply_inverse]
  exact eq_neg_of_add_eq_zero_left he

theorem tail_eq_residual_of_head_zero (L : BlockMap E F) (hL : (leading L).IsInvertible)
    (x : E) (hx : (L (x, 1)).1 = 0) :
    (L (x, 1)).2 = residual L := by
  rw [block_apply, vector_eq_of_head_zero L hL x hx]
  simp only [map_neg, one_smul, residual]
  abel

end NoExoticSixSphere.CorankOne
