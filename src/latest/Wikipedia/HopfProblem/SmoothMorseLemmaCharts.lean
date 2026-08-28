import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Restrictions and translations of genuine smooth Morse charts

These constructions preserve the original smooth atlases and the literal
forward and inverse functions. Translation also preserves the actual
second Fréchet derivative, with no differentiability hypothesis needed
for the equality of the total derivative operations.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Restriction of an actual native smooth partial diffeomorphism to an
open subset of its original source. -/
def restrictChart (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞)
    (U : Set E) (hU : IsOpen U) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞ where
  __ := e.toOpenPartialHomeomorph.restrOpen U hU
  contMDiffOn_toFun := e.contMDiffOn_toFun.mono inter_subset_left
  contMDiffOn_invFun := e.contMDiffOn_invFun.mono inter_subset_left

@[simp] theorem restrictChart_source
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) (U : Set E) (hU : IsOpen U) :
    (restrictChart e U hU).source = e.source ∩ U := rfl

@[simp] theorem restrictChart_apply
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) (U : Set E) (hU : IsOpen U) (x : E) :
    restrictChart e U hU x = e x := rfl

@[simp] theorem restrictChart_symm_apply
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) (U : Set E) (hU : IsOpen U) (y : F) :
    (restrictChart e U hU).symm y = e.symm y := rfl

/-- Literal translation of the center to zero, with its original smooth inverse. -/
def translationToZero (a : E) : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ where
  toFun x := x - a
  invFun x := a + x
  left_inv x := by simp [sub_eq_add_neg]
  right_inv x := by simp [sub_eq_add_neg, add_assoc]
  contMDiff_toFun :=
    (show ContDiff ℝ ∞ (fun x : E => x - a) from contDiff_id.sub contDiff_const).contMDiff
  contMDiff_invFun :=
    (show ContDiff ℝ ∞ (fun x : E => a + x) from contDiff_const.add contDiff_id).contMDiff

@[simp] theorem translationToZero_apply (a x : E) : translationToZero a x = x - a := rfl

@[simp] theorem translationToZero_symm_apply (a x : E) :
    (translationToZero a).symm x = a + x := rfl

/-- An actual origin-centered chart becomes a chart at any chosen original point. -/
def translateChart (a : E) (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) :
    PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞ :=
  (translationToZero a).toPartialDiffeomorph.trans e

@[simp] theorem translateChart_apply (a : E)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) (x : E) :
    translateChart a e x = e (x - a) := rfl

@[simp] theorem translateChart_symm_apply (a : E)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) (y : F) :
    (translateChart a e).symm y = a + e.symm y := rfl

@[simp] theorem mem_translateChart_source (a : E)
    (e : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞) (x : E) :
    x ∈ (translateChart a e).source ↔ x - a ∈ e.source := by
  change (x ∈ univ ∧ x - a ∈ e.source) ↔ x - a ∈ e.source
  simp only [mem_univ, true_and]

/-- The actual Hessian of a translated function is the translated Hessian. -/
theorem hessian_comp_add_left (f : E → ℝ) (a x : E) :
    fderiv ℝ (fderiv ℝ (fun y => f (a + y))) x =
      fderiv ℝ (fderiv ℝ f) (a + x) := by
  have h : fderiv ℝ (fun y => f (a + y)) = fun y => fderiv ℝ f (a + y) :=
    funext fun y => fderiv_comp_add_left a
  rw [h, fderiv_comp_add_left]

end Wikipedia.HopfProblem.SmoothMorseLemma
