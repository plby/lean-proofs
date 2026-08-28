import Wikipedia.HopfProblem.DegreeCollapseSurgeryHomologyParity

/-!
# The geometric parity descends to the exact surgery quotient

The original geometric parity is constant on the actual fibers of the
native lift. It therefore descends from the original detector kernel
modulo the actual attaching class. The quotient value is defined from
original representatives, and is proved equal to the actual new parity
under the constructed homology equivalence, for every tubular retraction.
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

theorem nativeLift_eq_of_sub_mem (x y : LinearMap.ker (detector f A hR))
    (hxy : x - y ∈ Submodule.span ℤ {nativeAttachingClass f A hR d hd}) :
    nativeLift f A hR d hd x = nativeLift f A hR d hd y := by
  rw [← nativeLift_kernel f A hR d hd] at hxy
  change nativeLift f A hR d hd (x - y) = 0 at hxy
  rw [map_sub] at hxy
  exact sub_eq_zero.mp hxy

variable (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]

theorem parity_eq_of_nativeLift_eq (x y : LinearMap.ker (detector f A hR))
    (hxy : nativeLift f A hR d hd x = nativeLift f A hR d hd y) :
    e.integralHomologyParity a r m x = e.integralHomologyParity a r m y := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1
  obtain ⟨r'⟩ := (UnitSurgery.inducedEmbedding A hR).nonempty_tubularRetraction
    (UnitSurgery.normalFraming A hR)
  let m' : UnitSurgery.Target A hR := Classical.choice inferInstance
  let : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m'
  rw [← nativeLift_parity f A hR d hd r m r' m' x,
    ← nativeLift_parity f A hR d hd r m r' m' y, hxy]

theorem parity_eq_of_sub_mem (x y : LinearMap.ker (detector f A hR))
    (hxy : x - y ∈ Submodule.span ℤ {nativeAttachingClass f A hR d hd}) :
    e.integralHomologyParity a r m x = e.integralHomologyParity a r m y :=
  parity_eq_of_nativeLift_eq f A hR d hd r m x y (nativeLift_eq_of_sub_mem f A hR d hd x y hxy)

def quotientParity :
    (LinearMap.ker (detector f A hR) ⧸ Submodule.span ℤ {nativeAttachingClass f A hR d hd}) →
      ZMod 2 :=
  Quotient.lift (fun x : LinearMap.ker (detector f A hR) ↦ e.integralHomologyParity a r m x)
    (fun x y hxy ↦ parity_eq_of_sub_mem f A hR d hd r m x y
      ((Submodule.quotientRel_def _).mp hxy))

theorem quotientParity_mk (x : LinearMap.ker (detector f A hR)) :
    quotientParity f A hR d hd r m (Submodule.Quotient.mk x) = e.integralHomologyParity a r m x :=
  rfl

theorem quotientParity_zero : quotientParity f A hR d hd r m 0 = 0 := by
  change e.integralHomologyParity a r m 0 = 0
  exact e.integralHomologyParity_zero a r m

theorem nativeMiddleQuotientEquiv_parity :
    letI := UnitSurgery.targetChartedSpace A hR;
    letI := UnitSurgery.target_isManifold A hR;
    letI := UnitSurgery.compactSpace_target A hR;
    letI : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
      (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1;
    ∀ (r' : TubularRetraction (UnitSurgery.inducedEmbedding A hR)) (m' : UnitSurgery.Target A hR),
      letI : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
        (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m';
      ∀ x : LinearMap.ker (detector f A hR) ⧸ Submodule.span ℤ {nativeAttachingClass f A hR d hd},
        (UnitSurgery.inducedEmbedding A hR).integralHomologyParity
          (UnitSurgery.normalFraming A hR) r' m' (nativeMiddleQuotientEquiv f A hR d hd x) =
        quotientParity f A hR d hd r m x := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1
  intro r' m'
  let : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m'
  intro x
  refine Quotient.inductionOn x ?_
  intro y
  exact (congrArg ((UnitSurgery.inducedEmbedding A hR).integralHomologyParity
    (UnitSurgery.normalFraming A hR) r' m')
    (nativeMiddleQuotientEquiv_mk f A hR d hd y)).trans
      ((nativeLift_parity f A hR d hd r m r' m' y).trans
        (quotientParity_mk f A hR d hd r m y).symm)

include A hR d hd in
theorem attachingClass_parity_zero :
    e.integralHomologyParity a r m (TraceCoreAttachment.originalSphereClass f) = 0 := by
  have h : nativeAttachingClass f A hR d hd - 0 ∈
      Submodule.span ℤ {nativeAttachingClass f A hR d hd} := by
    rw [sub_zero]
    exact Submodule.subset_span (mem_singleton _)
  have he := parity_eq_of_sub_mem f A hR d hd r m (nativeAttachingClass f A hR d hd) 0 h
  exact he.trans (e.integralHomologyParity_zero a r m)

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector
