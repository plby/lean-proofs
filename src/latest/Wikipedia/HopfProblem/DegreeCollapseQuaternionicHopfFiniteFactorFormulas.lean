import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiniteFactorOperators
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfSuspendedFrameCoordinates

/-!
# Exact normal and tangent formulas for the original two finite factors

Retain the actual product parametrization, line coordinates, sum coordinates,
and normal source split. Differentiate the two affine inclusions of one
factor in the product. Their global framed derivatives are precisely the
two original suspended tangent blocks, with the other block zero.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteFactorFormulas

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfProductDiffeomorph
open QuaternionicHopfFramedFiber QuaternionicHopfFiberFactors
open QuaternionicHopfFactorFrameComparison QuaternionicHopfFiniteProductFrame
open QuaternionicHopfFiniteFactorOperators QuaternionicHopfSuspendedFrameCoordinates
open FiniteSphereProductCharts hiding V

local instance : ChartedSpace (V 6) Fiber := fiberAtlas
local instance : IsManifold (𝓡 6) ∞ Fiber := fiber_isManifold

theorem parameter_left (r q : Sphere 3) : parameter (left r) q = (q, r) :=
  fiberDiffeomorph.symm_apply_apply (q, r)

theorem parameter_right (q r : Sphere 3) : parameter (right q) r = (q, r) :=
  fiberDiffeomorph.symm_apply_apply (q, r)

theorem coordinatePoint_left (r q : Sphere 3) : coordinatePoint (left r) q =
    sumCoordinates 8 (suspendedPoint q, suspendedPoint r) := by
  rw [coordinatePoint, parameter_left]
  rfl

theorem coordinatePoint_right (q r : Sphere 3) : coordinatePoint (right q) r =
    sumCoordinates 8 (suspendedPoint q, suspendedPoint r) := by
  rw [coordinatePoint, parameter_right]
  rfl

theorem finiteRightInverse_left (r q : Sphere 3) :
    finiteRightInverse (left r) q = squareRightInverse (q, r) := by
  rw [finiteRightInverse, parameter_left]

theorem finiteRightInverse_right (q r : Sphere 3) :
    finiteRightInverse (right q) r = squareRightInverse (q, r) := by
  rw [finiteRightInverse, parameter_right]

def leftLinear : V 8 →L[ℝ] V 16 :=
  (sumCoordinates 8).toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ (V 8) (V 8))

def rightLinear : V 8 →L[ℝ] V 16 :=
  (sumCoordinates 8).toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ (V 8) (V 8))

theorem finiteTangent_left (r q : Sphere 3) :
    finiteTangent (left r) q = leftLinear.comp (suspendedTangent q) := by
  let g : V 8 → V 16 := fun v ↦ sumCoordinates 8 (v, suspendedPoint r)
  have hg : ContDiff ℝ ∞ g := (sumCoordinates 8).contDiff.comp
    (contDiff_id.prodMk contDiff_const)
  have hd : fderiv ℝ g (suspendedPoint q) = leftLinear :=
    ((sumCoordinates 8).hasFDerivAt.comp (suspendedPoint q)
      ((hasFDerivAt_id (suspendedPoint q)).prodMk
        (hasFDerivAt_const (suspendedPoint r) (suspendedPoint q)))).fderiv
  have he : coordinatePoint (left r) = g ∘ suspendedPoint :=
    funext (coordinatePoint_left r)
  have h := SphereFiniteFramedCoordinates.framedDerivative_comp g hg
    suspendedPoint contMDiff_suspendedPoint q
  rw [← he, hd, suspended_framedDerivative] at h
  exact h

theorem finiteTangent_right (q r : Sphere 3) :
    finiteTangent (right q) r = rightLinear.comp (suspendedTangent r) := by
  let g : V 8 → V 16 := fun v ↦ sumCoordinates 8 (suspendedPoint q, v)
  have hg : ContDiff ℝ ∞ g := (sumCoordinates 8).contDiff.comp
    (contDiff_const.prodMk contDiff_id)
  have hd : fderiv ℝ g (suspendedPoint r) = rightLinear :=
    ((sumCoordinates 8).hasFDerivAt.comp (suspendedPoint r)
      ((hasFDerivAt_const (suspendedPoint q) (suspendedPoint r)).prodMk
        (hasFDerivAt_id (suspendedPoint r)))).fderiv
  have he : coordinatePoint (right q) = g ∘ suspendedPoint :=
    funext (coordinatePoint_right q)
  have h := SphereFiniteFramedCoordinates.framedDerivative_comp g hg
    suspendedPoint contMDiff_suspendedPoint r
  rw [← he, hd, suspended_framedDerivative] at h
  exact h

def normalInput (v : V 14) : WithLp 2 (ℝ × V 10) :=
  EuclideanTailCoordinates.split 10
    (EuclideanSpace.finAddEquivProd (n := 11) (m := 3) v).1

def tangentInput (v : V 14) : V 3 :=
  (EuclideanSpace.finAddEquivProd (n := 11) (m := 3) v).2

theorem finiteOperator_split (f : Sphere 3 → Fiber) (s : Sphere 3) (v : V 14) :
    EuclideanTailCoordinates.split 16 (QuaternionicHopfFiniteFactorOperators.finiteOperator f s v) =
      WithLp.toLp 2 ((normalInput v).fst,
        finiteRightInverse f s (normalInput v).snd + finiteTangent f s (tangentInput v)) := by
  change EuclideanTailCoordinates.split 16
    (SphereFiniteFramedCoordinates.finiteOperator
      (finiteRightInverse f s) (finiteTangent f s) v) = _
  rw [SphereFiniteFramedCoordinates.finiteOperator, OperatorSum.operator_apply, map_add,
    SphereFiniteFramedCoordinates.normalPart_apply,
    SphereFiniteFramedCoordinates.tangentPart_apply,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact add_zero _
  · rfl

theorem squareRightInverse_apply (p : Sphere 3 × Sphere 3) (w : V 10) :
    squareRightInverse p w = sumCoordinates 8
      (suspendedRightInverse p.1 ((sumCoordinates 5).symm w).1,
        suspendedRightInverse p.2 ((sumCoordinates 5).symm w).2) := by
  simp only [squareRightInverse, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.coe_prodMap', Prod.map_apply']

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfFiniteFactorFormulas
