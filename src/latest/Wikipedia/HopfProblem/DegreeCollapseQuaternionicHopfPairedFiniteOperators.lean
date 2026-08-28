import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiniteFactorFormulas
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfPairedFrameCoordinates

/-!
# The exact finite factor operators in paired quaternionic coordinates

Compute both operators in the retained outer radial and two suspension
blocks. After the proved coordinate changes, each variable block is exactly
the lifted quaternionic normal frame plus its original global tangent frame.
The other block contains only its fixed normal columns.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfPairedFiniteOperators

open NoExoticSixSphere QuaternionicHopf Stiefel
open QuaternionicHopfProductDiffeomorph QuaternionicHopfFramedFiber QuaternionicHopfFiberFactors
open QuaternionicHopfFiniteFactorOperators QuaternionicHopfFiniteFactorFormulas
open QuaternionicHopfFiniteProductFrame QuaternionicHopfSuspendedFrameCoordinates
open QuaternionicHopfFiniteBalancedFrame QuaternionicHopfPairedFrameCoordinates
open FiniteSphereProductCharts hiding V

local instance : ChartedSpace (V 6) Fiber := fiberAtlas
local instance : IsManifold (𝓡 6) ∞ Fiber := fiber_isManifold

def leftMap (a : Sphere 16) (r : Sphere 3) : C(Sphere 3, Monomorphism.Space 17 14) :=
  finiteMap (left r) (contMDiff_left r) a (left_mfderiv_injective r)

def rightMap (a : Sphere 16) (q : Sphere 3) : C(Sphere 3, Monomorphism.Space 17 14) :=
  finiteMap (right q) (contMDiff_right q) a (right_mfderiv_injective q)

theorem leftMap_value (a : Sphere 16) (r q : Sphere 3) :
    (leftMap a r q).val = QuaternionicHopfFiniteFactorOperators.finiteOperator (left r) q := rfl

theorem rightMap_value (a : Sphere 16) (q r : Sphere 3) :
    (rightMap a q r).val = QuaternionicHopfFiniteFactorOperators.finiteOperator (right q) r := rfl

def leftNormalInput (v : V 14) : V 5 := ((sumCoordinates 5).symm (normalInput v).snd).1

def rightNormalInput (v : V 14) : V 5 := ((sumCoordinates 5).symm (normalInput v).snd).2

theorem leftLinear_apply (v : V 8) : leftLinear v = sumCoordinates 8 (v, 0) := rfl

theorem rightLinear_apply (v : V 8) : rightLinear v = sumCoordinates 8 (0, v) := rfl

theorem leftMap_axes (a : Sphere 16) (r q : Sphere 3) (v : V 14) :
    axes ((leftMap a r q).val v) = ((normalInput v).fst,
      (suspendedRightInverse q (leftNormalInput v) + suspendedTangent q (tangentInput v),
        suspendedRightInverse r (rightNormalInput v))) := by
  rw [leftMap_value, axes_apply, finiteOperator_split]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [finiteRightInverse_left, finiteTangent_left, ContinuousLinearMap.comp_apply,
    squareRightInverse_apply, leftLinear_apply, ← map_add,
    ContinuousLinearEquiv.symm_apply_apply]
  simp only [leftNormalInput, rightNormalInput, Prod.mk_add_mk, add_zero]

theorem rightMap_axes (a : Sphere 16) (q r : Sphere 3) (v : V 14) :
    axes ((rightMap a q r).val v) = ((normalInput v).fst,
      (suspendedRightInverse q (leftNormalInput v),
        suspendedRightInverse r (rightNormalInput v) + suspendedTangent r (tangentInput v))) := by
  rw [rightMap_value, axes_apply, finiteOperator_split]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [finiteRightInverse_right, finiteTangent_right, ContinuousLinearMap.comp_apply,
    squareRightInverse_apply, rightLinear_apply, ← map_add,
    ContinuousLinearEquiv.symm_apply_apply]
  simp only [leftNormalInput, rightNormalInput, Prod.mk_add_mk, add_zero]

def finiteChartMap : C(Sphere 3, V 7) :=
  ⟨QuaternionicHopfFiniteFrame.finitePoint,
    QuaternionicHopfFiniteNormal.contMDiff_finitePoint.continuous⟩

theorem finiteChartMap_apply (q : Sphere 3) :
    finiteChartMap q = QuaternionicHopfFiniteFrame.finitePoint q := rfl

def leftTransport (a : Sphere 16) (r : Sphere 3) : C(Sphere 3, Monomorphism.Space 17 14) :=
  transport finiteChartMap (ContinuousMap.const _ (finiteChartMap r)) (leftMap a r)

def rightTransport (a : Sphere 16) (q : Sphere 3) : C(Sphere 3, Monomorphism.Space 17 14) :=
  transport (ContinuousMap.const _ (finiteChartMap q)) finiteChartMap (rightMap a q)

attribute [local irreducible] QuaternionicHopfPairedFrameCoordinates.operator
  leftMap rightMap finiteChartMap

theorem leftTransport_value (a : Sphere 16) (r q : Sphere 3) (v : V 14) :
    (leftTransport a r q).val v =
      operator (finiteChartMap q) (finiteChartMap r) ((leftMap a r q).val v) := rfl

theorem rightTransport_value (a : Sphere 16) (q r : Sphere 3) (v : V 14) :
    (rightTransport a q r).val v =
      operator (finiteChartMap q) (finiteChartMap r) ((rightMap a q r).val v) := rfl

theorem leftTransport_axes (a : Sphere 16) (r q : Sphere 3) (v : V 14) :
    axes ((leftTransport a r q).val v) = ((normalInput v).fst,
      (normal q (QuaternionicHopfSuspendedFrameCoordinates.normalCoordinates (leftNormalInput v)) +
          QuaternionicHopfSouthFiber.axis (SphereThreeTangentFrame.operator q.val (tangentInput v)),
        normal r
          (QuaternionicHopfSuspendedFrameCoordinates.normalCoordinates (rightNormalInput v)))) := by
  rw [leftTransport_value, axes_operator, leftMap_axes]
  dsimp only [Prod.fst, Prod.snd]
  rw [finiteChartMap_apply, finiteChartMap_apply, map_add,
    ambient_suspendedNormal, ambient_suspendedTangent, ambient_suspendedNormal]

theorem rightTransport_axes (a : Sphere 16) (q r : Sphere 3) (v : V 14) :
    axes ((rightTransport a q r).val v) = ((normalInput v).fst,
      (normal q (QuaternionicHopfSuspendedFrameCoordinates.normalCoordinates (leftNormalInput v)),
        normal r
            (QuaternionicHopfSuspendedFrameCoordinates.normalCoordinates (rightNormalInput v)) +
          QuaternionicHopfSouthFiber.axis
            (SphereThreeTangentFrame.operator r.val (tangentInput v)))) := by
  rw [rightTransport_value, axes_operator, rightMap_axes]
  dsimp only [Prod.fst, Prod.snd]
  rw [finiteChartMap_apply, finiteChartMap_apply, map_add,
    ambient_suspendedNormal, ambient_suspendedNormal, ambient_suspendedTangent]

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfPairedFiniteOperators
