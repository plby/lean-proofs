import Wikipedia.HopfProblem.DegreeCollapseSurgeryQuadraticQuotient
import Wikipedia.HopfProblem.DegreeCollapseCubeSphereGenerator

/-!
# The surgery quotient uses the actual geometric sphere class

The proved cubical generator comparison identifies the span used by the
trace sequence with that of the actual geometric sphere class. Thus the
native lift kills precisely that geometric class's span. The original
geometric parity on the actual attaching sphere vanishes as well. The
unit detector hypothesis is retained throughout.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct SmoothCube
open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (d : SingularHomology M 3) (hd : detector f A hR d = 1)

include d hd in
theorem geometricClass_detector_zero : detector f A hR (integralSphereClass f) = 0 := by
  have hm : integralSphereClass f ∈ Submodule.span ℤ {TraceCoreAttachment.originalSphereClass f} := by
    rw [← CubeSphereGenerator.image_span f]
    exact Submodule.subset_span (mem_singleton _)
  have hle : Submodule.span ℤ {TraceCoreAttachment.originalSphereClass f} ≤
      LinearMap.ker (detector f A hR) := by
    apply Submodule.span_le.mpr
    intro x hx
    rw [mem_singleton_iff.mp hx]
    exact attachingClass_detector_zero f A hR d hd
  exact hle hm

def geometricAttachingClass : LinearMap.ker (detector f A hR) :=
  ⟨integralSphereClass f, geometricClass_detector_zero f A hR d hd⟩

theorem geometricAttachingClass_eq_or_neg :
    geometricAttachingClass f A hR d hd = nativeAttachingClass f A hR d hd ∨
      geometricAttachingClass f A hR d hd = -nativeAttachingClass f A hR d hd := by
  rcases CubeSphereGenerator.standard_or_negative with hp | hn
  · left
    apply Subtype.ext
    change singularHomologyMap f 3 integralCubeSphereClass = singularHomologyMap f 3 (unitSphereTopClass 2)
    rw [hp]
  · right
    apply Subtype.ext
    change singularHomologyMap f 3 integralCubeSphereClass = -singularHomologyMap f 3 (unitSphereTopClass 2)
    rw [hn, map_neg]

theorem geometricAttaching_span : Submodule.span ℤ {geometricAttachingClass f A hR d hd} =
    Submodule.span ℤ {nativeAttachingClass f A hR d hd} := by
  rcases geometricAttachingClass_eq_or_neg f A hR d hd with hp | hn
  · rw [hp]
  · rw [hn]
    simpa only [Set.neg_singleton] using
      (Submodule.span_neg (R := ℤ) {nativeAttachingClass f A hR d hd})

theorem nativeLift_kernel_geometric : LinearMap.ker (nativeLift f A hR d hd) =
    Submodule.span ℤ {geometricAttachingClass f A hR d hd} := by
  rw [geometricAttaching_span, nativeLift_kernel]

def geometricMiddleQuotientEquiv :
    (LinearMap.ker (detector f A hR) ⧸ Submodule.span ℤ {geometricAttachingClass f A hR d hd}) ≃ₗ[ℤ]
      SingularHomology (UnitSurgery.Target A hR) 3 :=
  (Submodule.quotEquivOfEq _ _ (geometricAttaching_span f A hR d hd)).trans
    (nativeMiddleQuotientEquiv f A hR d hd)

theorem geometricMiddleQuotientEquiv_mk (x : LinearMap.ker (detector f A hR)) :
    geometricMiddleQuotientEquiv f A hR d hd (Submodule.Quotient.mk x) = nativeLift f A hR d hd x := by
  change nativeMiddleQuotientEquiv f A hR d hd
    (Submodule.quotEquivOfEq _ _ (geometricAttaching_span f A hR d hd) (Submodule.Quotient.mk x)) = _
  rw [Submodule.quotEquivOfEq_mk, nativeMiddleQuotientEquiv_mk]

include A hR d hd in
theorem attachingSphere_geometricParity_zero (r : TubularRetraction e) (m : M)
    [Subsingleton (π_ 2 M m)] : e.geometricSphereParity a r f = 0 := by
  have hx : geometricAttachingClass f A hR d hd - 0 ∈
      Submodule.span ℤ {nativeAttachingClass f A hR d hd} := by
    rw [sub_zero, ← geometricAttaching_span f A hR d hd]
    exact Submodule.subset_span (mem_singleton _)
  have h := parity_eq_of_sub_mem f A hR d hd r m (geometricAttachingClass f A hR d hd) 0 hx
  change e.integralHomologyParity a r m (integralSphereClass f) = e.integralHomologyParity a r m 0 at h
  rw [integralHomologyParity_sphereClass, integralHomologyParity_zero] at h
  exact h

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector
