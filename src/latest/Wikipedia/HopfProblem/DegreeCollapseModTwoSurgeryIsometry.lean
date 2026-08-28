import Wikipedia.HopfProblem.DegreeCollapseModTwoSurgeryParity
import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Native surgery realizes the quadratic orthogonal-complement quotient

Restrict the original geometric quadratic form to the actual orthogonal
complement. The proved surgery fibers show that the attaching line lies
in its quadratic radical. Lift this original form through that line,
retaining its value on every representative. The actual native homology
quotient equivalence is then a quadratic isometry to the geometric form
of the actual new manifold, with its constructed normal framing.
The required integral unit detector class is still supplied explicitly.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct SmoothCube
open SingularMayerVietoris PeriodTorusHigherHomology SphereHomologyCoefficients

attribute [local instance] modHomologyModule

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (d : SingularHomology M 3) (hd : detector f A hR d = 1)

def orthogonalQuadraticForm : QuadraticForm (ZMod 2) (LinearMap.ker (orthogonalFunctional e r m f)) :=
  (e.modTwoHomologyQuadraticForm a r m).comp (LinearMap.ker (orthogonalFunctional e r m f)).subtype

theorem orthogonalQuadraticForm_apply (x : LinearMap.ker (orthogonalFunctional e r m f)) :
    orthogonalQuadraticForm e a r m f x = e.modTwoHomologyParity a r m x := rfl

include A hR d hd in
theorem orthogonalAttaching_span_radical :
    Submodule.span (ZMod 2) {orthogonalAttachingClass e a r m f} ≤
      (orthogonalQuadraticForm e a r m f).radical := by
  intro x hx
  have hFx : modTwoSurgeryMap e a r m f A hR d hd x = 0 := by
    rw [← modTwoSurgeryMap_kernel e a r m f A hR d hd] at hx
    exact hx
  apply QuadraticMap.mem_radical_iff'.mpr
  constructor
  · change e.modTwoHomologyParity a r m x = 0
    have he := modTwoParity_eq_of_surgeryMap_eq e a r m f A hR d hd x 0
      (hFx.trans (map_zero (modTwoSurgeryMap e a r m f A hR d hd)).symm)
    exact he.trans (e.modTwoHomologyParity_zero a r m)
  · intro y
    change e.modTwoHomologyParity a r m (x + y).val = e.modTwoHomologyParity a r m y.val
    apply modTwoParity_eq_of_surgeryMap_eq e a r m f A hR d hd (x + y) y
    rw [map_add, hFx, zero_add]

def quotientQuadraticForm : QuadraticForm (ZMod 2)
    (LinearMap.ker (orthogonalFunctional e r m f) ⧸
      Submodule.span (ZMod 2) {orthogonalAttachingClass e a r m f}) :=
  (orthogonalQuadraticForm e a r m f).lift _ (orthogonalAttaching_span_radical e a r m f A hR d hd)

theorem quotientQuadraticForm_mk (x : LinearMap.ker (orthogonalFunctional e r m f)) :
    quotientQuadraticForm e a r m f A hR d hd (Submodule.Quotient.mk x) =
      e.modTwoHomologyParity a r m x := rfl

def nativeModTwoSurgeryIsometry :
    letI := UnitSurgery.targetChartedSpace A hR;
    letI := UnitSurgery.target_isManifold A hR;
    letI := UnitSurgery.compactSpace_target A hR;
    letI : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
      (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1;
    ∀ (r' : TubularRetraction (UnitSurgery.inducedEmbedding A hR)) (m' : UnitSurgery.Target A hR),
      letI : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
        (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m';
      (quotientQuadraticForm e a r m f A hR d hd).IsometryEquiv
        ((UnitSurgery.inducedEmbedding A hR).modTwoHomologyQuadraticForm
          (UnitSurgery.normalFraming A hR) r' m') := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1
  intro r' m'
  let : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m'
  refine {
    toLinearEquiv := modTwoSurgeryQuotientEquiv e a r m f A hR d hd
    map_app' := ?_ }
  intro x
  refine Quotient.inductionOn x ?_
  intro y
  exact (congrArg ((UnitSurgery.inducedEmbedding A hR).modTwoHomologyParity
    (UnitSurgery.normalFraming A hR) r' m')
    (modTwoSurgeryQuotientEquiv_mk e a r m f A hR d hd y)).trans
      ((modTwoSurgeryMap_parity e a r m f A hR d hd r' m' y).trans
        (quotientQuadraticForm_mk e a r m f A hR d hd y).symm)

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector
