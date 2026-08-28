import Wikipedia.NoExoticSixSphere.NormalBundle
import Wikipedia.NoExoticSixSphere.SmoothFrame
import Wikipedia.NoExoticSixSphere.OpenSubsetDifferential

/-!

# Restrict the original embedding and full normal frame to a clopen subset

The open subset has its inherited atlas. Its inclusion has bijective
differential, so the restricted embedding has exactly the original tangent
image and normal projection range at each point. Transporting the original
frame across that equality keeps every ambient frame vector unchanged.
Closedness supplies the required closed embedding, without a new embedding
or a replacement smooth structure.
-/

noncomputable section

open Set Function Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ClopenEmbedding

open NoExoticSixSphere

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (e : EuclideanEmbedding n M) (U : Opens M) (hU : IsClosed (U : Set M))

def restrict : EuclideanEmbedding n U where
  ambientDimension := e.ambientDimension
  toFun := e.toFun ∘ Subtype.val
  smooth := e.smooth.comp contMDiff_subtype_val
  closedEmbedding := e.closedEmbedding.comp hU.isClosedEmbedding_subtypeVal
  injective_mfderiv x := by
    rw [mfderiv_comp x (e.smooth.mdifferentiableAt (by simp))
      ((contMDiff_subtype_val (I := 𝓡 n) (U := U) (n := ∞)).mdifferentiableAt (by simp))]
    exact (e.injective_mfderiv x.val).comp
      (mfderiv_openSubset_val_bijective (I := 𝓡 n) U x).injective

theorem restrict_toFun (x : U) : (restrict e U hU).toFun x = e.toFun x.val := rfl

theorem restrict_tangentImage (x : U) :
    (restrict e U hU).tangentImage x = e.tangentImage x.val := by
  change (mfderiv (𝓡 n) (𝓡 e.ambientDimension) (e.toFun ∘ Subtype.val) x).range =
    (mfderiv (𝓡 n) (𝓡 e.ambientDimension) e.toFun x.val).range
  rw [mfderiv_comp x (e.smooth.mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (I := 𝓡 n) (U := U) (n := ∞)).mdifferentiableAt (by simp))]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (mfderiv_openSubset_val_bijective (I := 𝓡 n) U x).surjective)

theorem restrict_normalProjection_range (x : U) :
    ((restrict e U hU).normalProjection x).range = (e.normalProjection x.val).range := by
  rw [(restrict e U hU).range_normalProjection, e.range_normalProjection]
  exact congrArg (fun V : Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) ↦ Vᗮ)
    (restrict_tangentImage e U hU x)

def restrictedFrameEquiv (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel) (x : U) :
    e.NormalModel ≃L[ℝ] ((restrict e U hU).normalProjection x).range :=
  (a.equiv x.val).trans
    (ContinuousLinearEquiv.ofEq _ _ (restrict_normalProjection_range e U hU x).symm)

theorem restrictedFrameEquiv_ambient
    (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel) (x : U) (v : e.NormalModel) :
    (restrictedFrameEquiv e U hU a x v).val = (a.equiv x.val v).val := rfl

theorem restrictedFrameEquiv_smooth
    (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel) :
    ContMDiff (𝓡 n)
      𝓘(ℝ, e.NormalModel →L[ℝ] EuclideanSpace ℝ (Fin (restrict e U hU).ambientDimension)) ∞
      (fun x : U ↦ ((restrict e U hU).normalProjection x).range.subtypeL.comp
        (restrictedFrameEquiv e U hU a x).toContinuousLinearMap) := by
  have he : (fun x : U ↦ ((restrict e U hU).normalProjection x).range.subtypeL.comp
      (restrictedFrameEquiv e U hU a x).toContinuousLinearMap) =
      (fun x : U ↦ (e.normalProjection x.val).range.subtypeL.comp
        (a.equiv x.val).toContinuousLinearMap) := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    exact restrictedFrameEquiv_ambient e U hU a x v
  rw [he]
  exact a.smooth.comp (contMDiff_subtype_val (I := 𝓡 n) (U := U))

def restrictNormalFrame (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel) :
    SmoothRangeFrame (𝓡 n) (restrict e U hU).normalProjection (restrict e U hU).NormalModel where
  equiv := restrictedFrameEquiv e U hU a
  smooth := restrictedFrameEquiv_smooth e U hU a

theorem restrictNormalFrame_ambient
    (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel) (x : U) (v : e.NormalModel) :
    ((restrictNormalFrame e U hU a).equiv x v).val = (a.equiv x.val v).val := rfl

end Wikipedia.HopfProblem.DegreeCollapse.ClopenEmbedding
