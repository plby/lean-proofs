import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiniteBalancedFrame
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiniteProductFrame

/-!
# The original suspension coordinate is the radial Hopf-frame coordinate

Retain the actual lineCoordinates permutations on source and target. The
additional real identity column becomes the radial half-column, while the
finite Hopf columns and global tangent columns lift to their proved
quaternionic formulas. The balanced contraction transports these exact
suspended columns, with no unstated coordinate identification.
-/

noncomputable section

open scoped Quaternion Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfSuspendedFrameCoordinates

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfFiniteFrame
open QuaternionicHopfFiniteProductFrame QuaternionicHopfFiniteBalancedFrame
open SphereFiniteRadialCoordinates
open FiniteSphereProductCharts hiding V

def fixedInput : V 8 ≃L[ℝ] WithLp 2 (ℝ × V 7) :=
  (lineCoordinates 7).symm.trans
    ((ContinuousLinearEquiv.prodComm ℝ (V 7) ℝ).trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V 7)).symm)

def normalCoordinates : V 5 ≃L[ℝ] WithLp 2 (ℝ × V 4) :=
  (lineCoordinates 4).symm.trans
    ((ContinuousLinearEquiv.prodComm ℝ (V 4) ℝ).trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ (V 4)).symm)

theorem normalCoordinates_apply (w : V 5) : normalCoordinates w = WithLp.toLp 2
    (((lineCoordinates 4).symm w).2, ((lineCoordinates 4).symm w).1) := rfl

def ambientCoordinates (u : V 7) : V 8 ≃L[ℝ] V 8 := fixedInput.trans (coordinateEquiv u)

def ambientOperator (u : V 7) : V 8 →L[ℝ] V 8 :=
  (coordinateOperator u).comp fixedInput.toContinuousLinearMap

theorem ambientCoordinates_apply (u : V 7) (w : V 8) :
    ambientCoordinates u w = coordinateOperator u (WithLp.toLp 2
      (((lineCoordinates 7).symm w).2, ((lineCoordinates 7).symm w).1)) := rfl

theorem ambientOperator_apply (u : V 7) (w : V 8) :
    ambientOperator u w = ambientCoordinates u w := rfl

theorem contDiff_ambientOperator : ContDiff ℝ ∞ ambientOperator :=
  contDiff_coordinateOperator.clm_comp contDiff_const

theorem ambientCoordinates_line (u v : V 7) (t : ℝ) :
    ambientCoordinates u (lineCoordinates 7 (v, t)) =
      coordinateOperator u (WithLp.toLp 2 (t, v)) := by
  rw [ambientCoordinates_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem suspendedRightInverse_apply (q : Sphere 3) (w : V 5) :
    suspendedRightInverse q w = lineCoordinates 7
      (rightInverse q ((lineCoordinates 4).symm w).1, ((lineCoordinates 4).symm w).2) := rfl

theorem ambient_suspendedNormal (q : Sphere 3) (w : V 5) :
    ambientCoordinates (finitePoint q) (suspendedRightInverse q w) =
      normal q (normalCoordinates w) := by
  rw [suspendedRightInverse_apply, ambientCoordinates_line, normalCoordinates_apply]
  exact (lift_eq_coordinates (finitePoint q) (rightInverse q)
    (WithLp.toLp 2 (((lineCoordinates 4).symm w).2, ((lineCoordinates 4).symm w).1))).symm

def suspendedTangent (q : Sphere 3) : V 3 →L[ℝ] V 8 :=
  (lineCoordinates 7).toContinuousLinearMap.comp
    ((ContinuousLinearMap.inl ℝ (V 7) ℝ).comp
      (SphereThreeTangentFrame.framedDerivative finitePoint q))

theorem suspendedTangent_apply (q : Sphere 3) (v : V 3) : suspendedTangent q v =
    lineCoordinates 7 (SphereThreeTangentFrame.framedDerivative finitePoint q v, 0) := rfl

theorem suspended_framedDerivative (q : Sphere 3) :
    SphereThreeTangentFrame.framedDerivative suspendedPoint q = suspendedTangent q := by
  let L : V 7 →L[ℝ] V 8 := (lineCoordinates 7).toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (V 7) ℝ)
  have h := SphereFiniteFramedCoordinates.framedDerivative_comp L L.contDiff
    finitePoint QuaternionicHopfFiniteNormal.contMDiff_finitePoint q
  rw [ContinuousLinearMap.fderiv] at h
  exact h

theorem ambient_suspendedTangent (q : Sphere 3) (v : V 3) :
    ambientCoordinates (finitePoint q) (suspendedTangent q v) =
      QuaternionicHopfSouthFiber.axis (SphereThreeTangentFrame.operator q.val v) := by
  rw [suspendedTangent_apply, ambientCoordinates_line, coordinateOperator_apply]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, mul_zero, zero_smul, zero_add]
  exact congrArg (fun L : V 3 →L[ℝ] V 8 ↦ L v)
    (QuaternionicHopfFiniteFrameLift.lifted_finite_tangent q)

theorem balanced_suspendedNormal (q : Sphere 3) (w : V 5) :
    balancedFrameContraction (0, q)
      (ambientCoordinates (finitePoint reference) (suspendedRightInverse reference w)) =
        ambientCoordinates (finitePoint q) (suspendedRightInverse q w) := by
  rw [ambient_suspendedNormal, ambient_suspendedNormal, balanced_normal]

theorem balanced_suspendedTangent (q : Sphere 3) (v : V 3) :
    balancedFrameContraction (0, q)
      (ambientCoordinates (finitePoint reference) (suspendedTangent reference v)) =
        ambientCoordinates (finitePoint q) (suspendedTangent q v) := by
  rw [ambient_suspendedTangent, ambient_suspendedTangent, balanced_tangent]

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfSuspendedFrameCoordinates
