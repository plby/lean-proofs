import Wikipedia.HopfProblem.DegreeCollapseSurgeryDetectorKernel
import Wikipedia.HopfProblem.DegreeCollapseExactKernelQuotient

/-!
# The actual native H3 is the detector kernel modulo the attaching class

Apply the exact kernel quotient to the original two end maps into the
rounded trace. Its map is onto actual native H3 and has kernel exactly
the span of the original attaching class lifted to the detector kernel.
The induced quotient equivalence retains its defining trace identity.
The only geometric extra hypothesis is a unit value of the detector.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open SmoothCube Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (d : SingularHomology M 3) (hd : detector f A hR d = 1)

def nativeLift : LinearMap.ker (detector f A hR) →ₗ[ℤ]
    SingularHomology (UnitSurgery.Target A hR) 3 :=
  ExactKernelQuotient.liftMap (singularHomologyMap (topMap A) 3)
    (singularHomologyMap (TraceBody.nativeTargetInclusion A hR) 3) (detector f A hR)
    (TraceBody.nativeTarget_homology_injective_three A hR) (old_class_lifts_iff f A hR d hd)

theorem nativeLift_trace (x : LinearMap.ker (detector f A hR)) :
    singularHomologyMap (TraceBody.nativeTargetInclusion A hR) 3 (nativeLift f A hR d hd x) =
      singularHomologyMap (topMap A) 3 x :=
  ExactKernelQuotient.liftMap_spec _ _ _ _ _ x

theorem nativeLift_surjective : Surjective (nativeLift f A hR d hd) :=
  ExactKernelQuotient.liftMap_surjective _ _ _ _ _
    (TraceCoreAttachment.topMap_homology_surjective_three f A hR)

theorem nativeLift_eq_of_trace (x : LinearMap.ker (detector f A hR))
    (y : SingularHomology (UnitSurgery.Target A hR) 3)
    (hy : singularHomologyMap (TraceBody.nativeTargetInclusion A hR) 3 y =
      singularHomologyMap (topMap A) 3 x) : nativeLift f A hR d hd x = y :=
  TraceBody.nativeTarget_homology_injective_three A hR
    ((nativeLift_trace f A hR d hd x).trans hy.symm)

def nativeAttachingClass : LinearMap.ker (detector f A hR) :=
  ⟨TraceCoreAttachment.originalSphereClass f, attachingClass_detector_zero f A hR d hd⟩

theorem nativeLift_kernel : LinearMap.ker (nativeLift f A hR d hd) =
    Submodule.span ℤ {nativeAttachingClass f A hR d hd} :=
  ExactKernelQuotient.liftMap_kernel _ _ _ _ _
    (TraceCoreAttachment.originalSphereClass f) (TraceCoreAttachment.topMap_three_kernel f A hR)

def nativeMiddleQuotientEquiv :
    (LinearMap.ker (detector f A hR) ⧸ Submodule.span ℤ {nativeAttachingClass f A hR d hd}) ≃ₗ[ℤ]
      SingularHomology (UnitSurgery.Target A hR) 3 :=
  ExactKernelQuotient.quotientEquiv (singularHomologyMap (topMap A) 3)
    (singularHomologyMap (TraceBody.nativeTargetInclusion A hR) 3) (detector f A hR)
    (TraceBody.nativeTarget_homology_injective_three A hR) (old_class_lifts_iff f A hR d hd)
    (TraceCoreAttachment.originalSphereClass f) (TraceCoreAttachment.topMap_three_kernel f A hR)
    (TraceCoreAttachment.topMap_homology_surjective_three f A hR)

theorem nativeMiddleQuotientEquiv_mk (x : LinearMap.ker (detector f A hR)) :
    nativeMiddleQuotientEquiv f A hR d hd (Submodule.Quotient.mk x) = nativeLift f A hR d hd x :=
  ExactKernelQuotient.quotientEquiv_mk _ _ _ _ _ _ _ _ x

theorem nativeMiddleQuotientEquiv_trace (x : LinearMap.ker (detector f A hR)) :
    singularHomologyMap (TraceBody.nativeTargetInclusion A hR) 3
      (nativeMiddleQuotientEquiv f A hR d hd (Submodule.Quotient.mk x)) =
        singularHomologyMap (topMap A) 3 x := by
  rw [nativeMiddleQuotientEquiv_mk, nativeLift_trace]

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector
