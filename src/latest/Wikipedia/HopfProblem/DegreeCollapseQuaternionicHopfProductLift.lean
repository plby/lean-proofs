import Wikipedia.HopfProblem.DegreeCollapseSphereFiniteEquationLift
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiniteProductFrame
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfInducedProductFrame
import Wikipedia.HopfProblem.DegreeCollapseRightInverseFrameHomotopy

/-!
# The full lifted Hopf product columns and their induced-frame comparison

Lift the already constructed finite columns through the actual inverse
chart and add the radial half-column. They form a smooth right inverse
of the original full sphere-fiber equations. Their normal projection is
the existing induced frame. A smooth transverse deformation retains the
equation identity and remains injective with the actual tangent columns.
-/

noncomputable section

open Filter
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfProductLift

open NoExoticSixSphere QuaternionicHopf SphereFiniteAmbientPoint
open QuaternionicHopfProductImmersion QuaternionicHopfProductDiffeomorph
open QuaternionicHopfInducedProductFrame QuaternionicHopfFiniteProductFrame

theorem suspendedTarget_center : QuaternionicHopfProductFiber.suspendedPoint = -spherePole 5 := by
  rw [QuaternionicHopfProductFiber.suspendedPoint, QuaternionicHopfFiniteFrame.target_center,
    slice_neg_pole]

theorem target_center : QuaternionicHopfProductFiber.point = -spherePole 10 := by
  change JamesSphere.pairing 5
    (QuaternionicHopfProductFiber.suspendedPoint, QuaternionicHopfProductFiber.suspendedPoint) = _
  rw [suspendedTarget_center, pairing_neg_poles]

theorem ambientPoint_squarePoint (p : Sphere 3 × Sphere 3) :
    ambientPoint 16 (squarePoint p) = ambientInclusion p :=
  congrArg Subtype.val (point_squarePoint p)

theorem smoothMap_finite_eventuallyEq (p : Sphere 3 × Sphere 3) :
    SphereFiniteRepresentative.value smoothMap =ᶠ[𝓝 (squarePoint p)]
      SphereFiniteRepresentative.value (SphereSmash.squareMap suspendedMap) := by
  apply SphereFiniteAmbientPoint.value_eventuallyEq
  rw [point_squarePoint]
  exact smoothMap_eventuallyEq_square (fiberInclusion p) (smoothMap_fiberInclusion p)

theorem smoothMap_finite_derivative (p : Sphere 3 × Sphere 3) :
    fderiv ℝ (SphereFiniteRepresentative.value smoothMap) (squarePoint p) =
      fderiv ℝ (SphereFiniteRepresentative.value (SphereSmash.squareMap suspendedMap))
        (squarePoint p) :=
  (smoothMap_finite_eventuallyEq p).fderiv_eq

theorem smoothMap_finite_rightInverse (p : Sphere 3 × Sphere 3) (w : V 10) :
    fderiv ℝ (SphereFiniteRepresentative.value smoothMap) (squarePoint p)
      (squareRightInverse p w) = w := by
  rw [smoothMap_finite_derivative]
  exact square_derivative_rightInverse p w

theorem smoothMap_finite_fiber (p : Sphere 3 × Sphere 3) :
    smoothMap (SphereFiniteRepresentative.point 16 (squarePoint p)) = -spherePole 10 := by
  rw [point_squarePoint, smoothMap_fiberInclusion, target_center]

def fullRightInverse (p : Sphere 3 × Sphere 3) : Normal →L[ℝ] V 17 :=
  SphereFiniteEquationLift.lift (squarePoint p) (squareRightInverse p)

theorem fullRightInverse_apply (p : Sphere 3 × Sphere 3) (w : Normal) :
    fullRightInverse p w = ((1 / 2 : ℝ) * w.fst) • ambientInclusion p +
      fderiv ℝ (ambientPoint 16) (squarePoint p) (squareRightInverse p w.snd) := by
  rw [fullRightInverse, SphereFiniteEquationLift.lift_apply, ambientPoint_squarePoint]

theorem contMDiff_fullRightInverse :
    ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, Normal →L[ℝ] V 17) ∞ fullRightInverse :=
  SphereFiniteEquationLift.contMDiff_lift contMDiff_squarePoint contMDiff_squareRightInverse

def equationDerivative (a : Sphere 16) (p : Sphere 3 × Sphere 3) : V 17 →L[ℝ] Normal :=
  fderiv ℝ (equations a) (ambientInclusion p)

theorem equations_fullRightInverse (a : Sphere 16) (p : Sphere 3 × Sphere 3) (w : Normal) :
    equationDerivative a p (fullRightInverse p w) = w := by
  have h := SphereFiniteEquationLift.equations_lift smoothMap smoothMap_contMDiff a
    (squarePoint p) (smoothMap_finite_fiber p) (squareRightInverse p)
    (smoothMap_finite_rightInverse p) w
  rw [← target_center, ambientPoint_squarePoint] at h
  exact h

theorem contMDiff_equationDerivative (a : Sphere 16) :
    ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, V 17 →L[ℝ] Normal) ∞ (equationDerivative a) :=
  NormalFrameOfEquations.contMDiff_equationDifferential contMDiff_ambientInclusion
    (contDiffAt_equations a)

theorem equationDerivative_original (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    equationDerivative a p = fderiv ℝ
      (SphereFiberNormalFrame.equations (SphereSmash.squareMap suspendedMap)
        QuaternionicHopfProductFiber.point a) (ambientInclusion p) :=
  SphereFiberEquationGerm.equations_fderiv_eq smoothMap (SphereSmash.squareMap suspendedMap)
    QuaternionicHopfProductFiber.point a (fiberInclusion p)
    (smoothMap_eventuallyEq_square (fiberInclusion p) (smoothMap_fiberInclusion p))

theorem original_equations_fullRightInverse
    (a : Sphere 16) (p : Sphere 3 × Sphere 3) (w : Normal) :
    fderiv ℝ (SphereFiberNormalFrame.equations (SphereSmash.squareMap suspendedMap)
      QuaternionicHopfProductFiber.point a) (ambientInclusion p) (fullRightInverse p w) = w := by
  rw [← equationDerivative_original]
  exact equations_fullRightInverse a p w

theorem projected_fullRightInverse (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    (NormalFrameOfEquations.ambientDifferential
      ((𝓡 3).prod (𝓡 3)) ambientInclusion p).rangeᗮ.starProjection.comp (fullRightInverse p) =
        (normalFrame a).ambient p := by
  have hproj : (NormalFrameOfEquations.ambientDifferential
      ((𝓡 3).prod (𝓡 3)) ambientInclusion p).rangeᗮ.starProjection =
        (equationDerivative a p).kerᗮ.starProjection :=
    congrArg (fun S : Submodule ℝ (V 17) ↦ Sᗮ.starProjection) (tangent_range_eq_kernel a p)
  rw [hproj, normalFrame_ambient]
  exact RightInverseFrameHomotopy.projection_rightInverse
    (equationDerivative a p) (fullRightInverse p) (equations_fullRightInverse a p)

def normalization (a : Sphere 16) : ℝ × (Sphere 3 × Sphere 3) → Normal →L[ℝ] V 17 :=
  RightInverseFrameHomotopy.normalize (equationDerivative a) fullRightInverse

theorem normalization_zero (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    normalization a (0, p) = fullRightInverse p :=
  RightInverseFrameHomotopy.normalize_zero (equationDerivative a) fullRightInverse p

theorem normalization_one (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    normalization a (1, p) = (normalFrame a).ambient p := by
  rw [normalization, RightInverseFrameHomotopy.normalize_one, normalFrame_ambient]
  rfl

theorem contMDiff_normalization (a : Sphere 16) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod ((𝓡 3).prod (𝓡 3)))
      𝓘(ℝ, Normal →L[ℝ] V 17) ∞ (normalization a) :=
  RightInverseFrameHomotopy.contMDiff_normalize
    (D := equationDerivative a) (R := fullRightInverse)
    (contMDiff_equationDerivative a) contMDiff_fullRightInverse (equations_fullRightInverse a)

theorem normalization_rightInverse (a : Sphere 16) (p : ℝ × (Sphere 3 × Sphere 3)) (w : Normal) :
    equationDerivative a p.2 (normalization a p w) = w :=
  RightInverseFrameHomotopy.normalize_rightInverse (equationDerivative a) fullRightInverse
    (equations_fullRightInverse a) p w

theorem normalization_original_rightInverse
    (a : Sphere 16) (p : ℝ × (Sphere 3 × Sphere 3)) (w : Normal) :
    fderiv ℝ (SphereFiberNormalFrame.equations (SphereSmash.squareMap suspendedMap)
      QuaternionicHopfProductFiber.point a) (ambientInclusion p.2) (normalization a p w) = w := by
  rw [← equationDerivative_original]
  exact normalization_rightInverse a p w

theorem normalization_with_tangent_injective
    (a : Sphere 16) (t : ℝ) (p : Sphere 3 × Sphere 3) :
    Function.Injective ((normalization a (t, p)).coprod
      (NormalFrameOfEquations.ambientDifferential
        ((𝓡 3).prod (𝓡 3)) ambientInclusion p)) := by
  have hA : ∀ v : V 3 × V 3, equationDerivative a p
      (NormalFrameOfEquations.ambientDifferential
        ((𝓡 3).prod (𝓡 3)) ambientInclusion p v) = 0 := by
    intro v
    change NormalFrameOfEquations.ambientDifferential
      ((𝓡 3).prod (𝓡 3)) ambientInclusion p v ∈
        (fderiv ℝ (equations a) (ambientInclusion p)).ker
    rw [← tangent_range_eq_kernel a p]
    exact ⟨v, rfl⟩
  have hS : ∀ w : Normal,
      equationDerivative a p (orthogonalRightInverse (equationDerivative a p) w) = w :=
    apply_orthogonalRightInverse (equationDerivative a p) (equations_fderiv_surjective a p)
  have h := RightInverseFrameHomotopy.blend_coprod_injective
    (E := V 17) (F := Normal) (K := V 3 × V 3) (equationDerivative a p)
    (fullRightInverse p) (orthogonalRightInverse (equationDerivative a p))
    (equations_fullRightInverse a p) hS
    (NormalFrameOfEquations.ambientDifferential
      ((𝓡 3).prod (𝓡 3)) ambientInclusion p) hA
    (ambientDifferential_injective p) t
  simpa only [normalization, RightInverseFrameHomotopy.normalize] using h

theorem normalization_one_original_frame (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    normalization a (1, p) = orthogonalRightInverse
      (fderiv ℝ (SphereFiberNormalFrame.equations (SphereSmash.squareMap suspendedMap)
        QuaternionicHopfProductFiber.point a) (ambientInclusion p)) :=
  (normalization_one a p).trans (normalFrame_original_equations a p)

theorem normalization_one_fiberDiffeomorph (a : Sphere 16) (p : Sphere 3 × Sphere 3) :
    letI := fiberAtlas;
    normalization a (1, p) =
      (SphereFiberNormalFrame.normalFrame smoothMap smoothMap_contMDiff
        QuaternionicHopfProductFiber.point smoothMap_regular 6 (by decide) a).ambient
          (fiberDiffeomorph p) := by
  let := fiberAtlas
  rw [normalization_one]
  exact normalFrame_fiberDiffeomorph a p

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfProductLift
