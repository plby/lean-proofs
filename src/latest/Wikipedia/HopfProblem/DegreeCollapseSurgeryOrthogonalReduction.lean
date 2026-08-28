import Wikipedia.HopfProblem.DegreeCollapseDetectorIntersection
import Wikipedia.HopfProblem.DegreeCollapseIntegralKernelReduction
import Wikipedia.HopfProblem.DegreeCollapseGeometricSurgeryClass
import Wikipedia.NoExoticSixSphere.ModTwoHomologyQuadraticParity

/-!
# The integral surgery kernel reduces onto the actual orthogonal complement

The orthogonal complement is taken inside the original native mod-two H3
with its geometric intersection form. Its reduction map is the actual
coefficient map restricted to the exact integer detector kernel. A unit
detector class corrects every residue lift into that integer kernel.
The restricted kernel is precisely twice the integer kernel, and the
actual geometric attaching class reduces to the original sphere class.
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

def modTwoAttachingClass : ModHomology 2 M 3 := reductionHomologyMap 2 M 3 (integralSphereClass f)

def orthogonalFunctional : ModHomology 2 M 3 →ₗ[ZMod 2] ZMod 2 :=
  e.modTwoHomologyIntersection r m (modTwoAttachingClass f)

def orthogonalFunctionalInt : ModHomology 2 M 3 →ₗ[ℤ] ZMod 2 := by
  let F := (orthogonalFunctional e r m f).toAddMonoidHom
  exact {
    toFun := F
    map_add' := F.map_add
    map_smul' := by
      intro k x
      exact (congrArg F (int_smul_eq_zsmul (ModHomology 2 M 3).isModule k x)).trans
        (F.map_zsmul k x) }

theorem orthogonalFunctional_reduction (c : SingularHomology M 3) :
    orthogonalFunctional e r m f (reductionHomologyMap 2 M 3 c) = (detector f A hR c : ZMod 2) := by
  change e.modTwoHomologyIntersection r m
    (reductionHomologyMap 2 M 3 (integralSphereClass f)) (reductionHomologyMap 2 M 3 c) = _
  rw [modTwoHomologyIntersection_reduction]
  exact (detector_modTwo_eq_intersection e a r m f A hR c).symm

def orthogonalAttachingClass : LinearMap.ker (orthogonalFunctional e r m f) :=
  ⟨modTwoAttachingClass f, e.modTwoHomologyIntersection_self a r m _⟩

def kernelReduction : LinearMap.ker (detector f A hR) →ₗ[ℤ]
    LinearMap.ker (orthogonalFunctional e r m f) :=
  IntegralKernelReduction.reduction (reductionHomologyMap 2 M 3) (detector f A hR)
    (orthogonalFunctionalInt e r m f) (orthogonalFunctional_reduction e a r m f A hR)

theorem kernelReduction_val (x : LinearMap.ker (detector f A hR)) :
    (kernelReduction e a r m f A hR x).val = reductionHomologyMap 2 M 3 x := rfl

theorem kernelReduction_surjective (d : SingularHomology M 3) (hd : detector f A hR d = 1) :
    Surjective (kernelReduction e a r m f A hR) :=
  IntegralKernelReduction.reduction_surjective _ _ _ _
    (scalarImage_eq_reduction_ker 2 (by decide) M 3).symm
    (TwoConnectedCoefficients.middleReduction_surjective m) d hd

theorem kernelReduction_kernel : LinearMap.ker (kernelReduction e a r m f A hR) =
    scalarImage 2 (LinearMap.ker (detector f A hR)) :=
  IntegralKernelReduction.reduction_kernel _ _ _ _
    (scalarImage_eq_reduction_ker 2 (by decide) M 3).symm

theorem kernelReduction_attaching (d : SingularHomology M 3) (hd : detector f A hR d = 1) :
    kernelReduction e a r m f A hR (geometricAttachingClass f A hR d hd) =
      orthogonalAttachingClass e a r m f := Subtype.ext rfl

def kernelQuotientEquivOrthogonal (d : SingularHomology M 3) (hd : detector f A hR d = 1) :
    (LinearMap.ker (detector f A hR) ⧸ scalarImage 2 (LinearMap.ker (detector f A hR))) ≃ₗ[ℤ]
      LinearMap.ker (orthogonalFunctional e r m f) :=
  IntegralKernelReduction.quotientEquiv (reductionHomologyMap 2 M 3) (detector f A hR)
    (orthogonalFunctionalInt e r m f) (orthogonalFunctional_reduction e a r m f A hR)
    (scalarImage_eq_reduction_ker 2 (by decide) M 3).symm
    (TwoConnectedCoefficients.middleReduction_surjective m) d hd

theorem kernelQuotientEquivOrthogonal_mk (d : SingularHomology M 3) (hd : detector f A hR d = 1)
    (x : LinearMap.ker (detector f A hR)) :
    kernelQuotientEquivOrthogonal e a r m f A hR d hd (Submodule.Quotient.mk x) =
      kernelReduction e a r m f A hR x :=
  IntegralKernelReduction.quotientEquiv_mk _ _ _ _ _ _ _ _ x

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector
