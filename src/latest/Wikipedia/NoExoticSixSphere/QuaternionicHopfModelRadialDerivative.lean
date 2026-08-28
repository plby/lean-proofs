import Wikipedia.NoExoticSixSphere.QuaternionicHopfTargetChange

/-!
# The original model-chart radial derivative factors through the quaternionic one

The chain rule is applied to the original Hopf map after its original
radial source retraction. Both target-coordinate derivatives are evaluated
at the literal south pole, so the comparison operator is constant on the fiber.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace NoExoticSixSphere.QuaternionicHopf

def radialHopfMap (a : Sphere 7) (z : V 8) : Sphere 4 :=
  sphereMap (SphereRadialRetraction.retract a z)

theorem radialHopfMap_coe (a x : Sphere 7) : radialHopfMap a x.val = sphereMap x := by
  rw [radialHopfMap, SphereRadialRetraction.retract_coe]

theorem contMDiffAt_radialHopfMap (a x : Sphere 7) :
    ContMDiffAt 𝓘(ℝ, V 8) (𝓡 4) ∞ (radialHopfMap a) x.val := by
  let : Fact (Module.finrank ℝ (V 8) = 7 + 1) := ⟨finrank_euclideanSpace_fin⟩
  exact (contMDiff_sphereMap (SphereRadialRetraction.retract a x.val)).comp x.val
    (SphereRadialRetraction.contMDiffAt_retract a (ne_zero_of_mem_unit_sphere x))

def radialHopfDerivative (a x : Sphere 7) : V 8 →L[ℝ] V 4 :=
  mfderiv 𝓘(ℝ, V 8) (𝓡 4) (radialHopfMap a) x.val

theorem radialTailExtension_nativeDerivative (a x : Sphere 7) (hx : sphereMap x = south) :
    fderiv ℝ (radialTailExtension a) x.val = tailDerivative.comp (radialHopfDerivative a x) := by
  have hF := (contMDiff_tailCoordinates (radialHopfMap a x.val)).mdifferentiableAt (by simp)
  have hR := (contMDiffAt_radialHopfMap a x).mdifferentiableAt (by simp)
  have hd := mfderiv_comp x.val hF hR
  rw [mfderiv_eq_fderiv] at hd
  change fderiv ℝ (radialTailExtension a) x.val =
    (tailDerivativeAt (radialHopfMap a x.val)).comp (radialHopfDerivative a x) at hd
  rw [radialHopfMap_coe, hx] at hd
  exact hd

def modelRadialCoordinates (a : Sphere 7) (z : V 8) : V 4 :=
  modelSouthChart (radialHopfMap a z)

theorem modelSouthChart_smooth_at_radial (a x : Sphere 7) (hx : sphereMap x = south) :
    ContMDiffAt (𝓡 4) 𝓘(ℝ, V 4) ∞ modelSouthChart (radialHopfMap a x.val) := by
  rw [radialHopfMap_coe, hx]
  exact modelSouthChart_smooth

theorem contDiffAt_modelRadialCoordinates (a x : Sphere 7) (hx : sphereMap x = south) :
    ContDiffAt ℝ ∞ (modelRadialCoordinates a) x.val :=
  ((modelSouthChart_smooth_at_radial a x hx).comp x.val
    (contMDiffAt_radialHopfMap a x)).contDiffAt

theorem modelRadialCoordinates_derivative (a x : Sphere 7) (hx : sphereMap x = south) :
    fderiv ℝ (modelRadialCoordinates a) x.val =
      (modelChartDerivativeAt south).comp (radialHopfDerivative a x) := by
  have hF := (modelSouthChart_smooth_at_radial a x hx).mdifferentiableAt (by simp)
  have hR := (contMDiffAt_radialHopfMap a x).mdifferentiableAt (by simp)
  have hd := mfderiv_comp x.val hF hR
  rw [mfderiv_eq_fderiv] at hd
  change fderiv ℝ (modelRadialCoordinates a) x.val =
    (modelChartDerivativeAt (radialHopfMap a x.val)).comp (radialHopfDerivative a x) at hd
  rw [radialHopfMap_coe, hx] at hd
  exact hd

def modelRadialTail (a : Sphere 7) : V 8 → V 4 :=
  SphereLevelEquations.extend a
    (CenteredChartCoordinates.coordinates sphereMap modelSouthChart south)

theorem contDiffAt_modelRadialTail (a x : Sphere 7) (hx : sphereMap x = south) :
    ContDiffAt ℝ ∞ (modelRadialTail a) x.val :=
  (contDiffAt_modelRadialCoordinates a x hx).sub contDiffAt_const

theorem modelRadialTail_derivative (a x : Sphere 7) (hx : sphereMap x = south) :
    fderiv ℝ (modelRadialTail a) x.val =
      southTargetChange.toContinuousLinearMap.comp (fderiv ℝ (radialTailExtension a) x.val) := by
  have h := ((contDiffAt_modelRadialCoordinates a x hx).differentiableAt
    (by simp)).hasFDerivAt.sub_const (modelSouthChart south)
  change HasFDerivAt (𝕜 := ℝ) (modelRadialTail a) _ x.val at h
  rw [h.fderiv, modelRadialCoordinates_derivative a x hx,
    radialTailExtension_nativeDerivative a x hx]
  apply ContinuousLinearMap.ext
  intro v
  change modelChartDerivativeAt south (radialHopfDerivative a x v) =
    southTargetChange (tailDerivative (radialHopfDerivative a x v))
  exact (southTargetChange_tailDerivative _).symm

end NoExoticSixSphere.QuaternionicHopf
