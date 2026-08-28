import Wikipedia.NoExoticSixSphere.QuaternionicHopfRadialEquations
import Wikipedia.NoExoticSixSphere.SphereFiberNormalFrame

/-!
# The fixed change between quaternionic and original model target coordinates

Both derivatives are taken at the same literal south pole, in the
original four-sphere atlas. Their ratio is a fixed continuous linear
equivalence; it is not a frame chosen separately at each source point.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

def modelSouthChart : PartialDiffeomorph (𝓡 4) 𝓘(ℝ, V 4) (Sphere 4) (V 4) ∞ :=
  modelChartPartialDiffeomorph (I := 𝓡 4) south

theorem modelSouthChart_mem : south ∈ modelSouthChart.source := mem_extChartAt_source south

theorem modelSouthChart_local :
    IsLocalDiffeomorphAt (𝓡 4) 𝓘(ℝ, V 4) ∞ modelSouthChart south :=
  ⟨modelSouthChart, modelSouthChart_mem, fun _ _ ↦ rfl⟩

theorem modelSouthChart_smooth : ContMDiffAt (𝓡 4) 𝓘(ℝ, V 4) ∞ modelSouthChart south :=
  modelSouthChart.contMDiffOn_toFun.contMDiffAt
    (modelSouthChart.open_source.mem_nhds modelSouthChart_mem)

def modelChartDerivativeAt (y : Sphere 4) : V 4 →L[ℝ] V 4 :=
  mfderiv (𝓡 4) 𝓘(ℝ, V 4) modelSouthChart y

def tailDerivativeAt (y : Sphere 4) : V 4 →L[ℝ] ℍ :=
  mfderiv (𝓡 4) 𝓘(ℝ, ℍ) tailCoordinates y

theorem modelChartDerivative_bijective : Function.Bijective (modelChartDerivativeAt south) :=
  ⟨(modelSouthChart_local.mfderivToContinuousLinearEquiv (by simp)).injective,
    (modelSouthChart_local.mfderivToContinuousLinearEquiv (by simp)).surjective⟩

def modelSouthDerivativeEquiv : V 4 ≃L[ℝ] V 4 :=
  (LinearEquiv.ofBijective (modelChartDerivativeAt south).toLinearMap
    modelChartDerivative_bijective).toContinuousLinearEquiv

def southTailDerivativeEquiv : V 4 ≃L[ℝ] ℍ :=
  (LinearEquiv.ofBijective tailDerivative.toLinearMap
    tailCoordinates_derivative_bijective).toContinuousLinearEquiv

def southTargetChange : ℍ ≃L[ℝ] V 4 :=
  southTailDerivativeEquiv.symm.trans modelSouthDerivativeEquiv

theorem southTargetChange_tailDerivative (v : V 4) :
    southTargetChange (tailDerivative v) = modelChartDerivativeAt south v := by
  change modelSouthDerivativeEquiv (southTailDerivativeEquiv.symm
    (southTailDerivativeEquiv v)) = modelSouthDerivativeEquiv v
  rw [ContinuousLinearEquiv.symm_apply_apply]

def augmentedTargetChange : SouthNormalModel ≃L[ℝ] WithLp 2 (ℝ × V 4) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℍ).trans
    (((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr southTargetChange).trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V 4)).symm)

theorem augmentedTargetChange_apply (r : ℝ) (w : ℍ) :
    augmentedTargetChange (WithLp.toLp 2 (r, w)) = WithLp.toLp 2 (r, southTargetChange w) := rfl

theorem augmentedTargetChange_symm_apply (r : ℝ) (w : V 4) :
    augmentedTargetChange.symm (WithLp.toLp 2 (r, w)) =
      WithLp.toLp 2 (r, southTargetChange.symm w) := rfl

end NoExoticSixSphere.QuaternionicHopf
