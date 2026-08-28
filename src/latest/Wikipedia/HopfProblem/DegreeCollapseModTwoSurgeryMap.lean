import Wikipedia.HopfProblem.DegreeCollapseSurgeryOrthogonalReduction
import Wikipedia.HopfProblem.DegreeCollapseExactReductionQuotient

/-!
# The actual mod-two surgery quotient is the orthogonal complement modulo its sphere

Descend the checked integer surgery lift through the actual coefficient
reductions on both ends. The resulting map on the actual orthogonal
complement is onto and has kernel the mod-two span of the actual attaching
sphere. This constructs the genuine F2-linear quotient equivalence and
retains its formula on every integral detector-kernel representative.
The integral unit detector class remains a hypothesis.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct SmoothCube
open SingularMayerVietoris PeriodTorusHigherHomology SphereHomologyCoefficients

attribute [local instance] modHomologyModule

theorem mem_span_int_iff_modTwo {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (a x : V) :
    x ∈ Submodule.span ℤ {a} ↔ x ∈ Submodule.span (ZMod 2) {a} := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp h
    apply Submodule.mem_span_singleton.mpr
    refine ⟨(k : ZMod 2), ?_⟩
    rw [Int.cast_smul_eq_zsmul]
    exact hk
  · intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective c
    rw [Int.cast_smul_eq_zsmul] at hc
    exact Submodule.mem_span_singleton.mpr ⟨k, hc⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (d : SingularHomology M 3) (hd : detector f A hR d = 1)

def modTwoSurgeryMapInt : LinearMap.ker (orthogonalFunctional e r m f) →ₗ[ℤ]
    ModHomology 2 (UnitSurgery.Target A hR) 3 :=
  ExactReduction.inducedMap (nativeLift f A hR d hd) (kernelReduction e a r m f A hR)
    (reductionHomologyMap 2 (UnitSurgery.Target A hR) 3)
    (kernelReduction_kernel e a r m f A hR)
    (scalarImage_eq_reduction_ker 2 (by decide) (UnitSurgery.Target A hR) 3).symm
    (kernelReduction_surjective e a r m f A hR d hd)

def modTwoSurgeryMap : LinearMap.ker (orthogonalFunctional e r m f) →ₗ[ZMod 2]
    ModHomology 2 (UnitSurgery.Target A hR) 3 :=
  (modTwoSurgeryMapInt e a r m f A hR d hd).toAddMonoidHom.toZModLinearMap 2

theorem modTwoSurgeryMap_reduction (x : LinearMap.ker (detector f A hR)) :
    modTwoSurgeryMap e a r m f A hR d hd (kernelReduction e a r m f A hR x) =
      reductionHomologyMap 2 (UnitSurgery.Target A hR) 3 (nativeLift f A hR d hd x) :=
  ExactReduction.inducedMap_reduction _ _ _
    (kernelReduction_kernel e a r m f A hR)
    (scalarImage_eq_reduction_ker 2 (by decide) (UnitSurgery.Target A hR) 3).symm
    (kernelReduction_surjective e a r m f A hR d hd) x

theorem modTwoSurgeryMap_surjective : Surjective (modTwoSurgeryMap e a r m f A hR d hd) := by
  have htwo := FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) := htwo.1
  let m' : UnitSurgery.Target A hR := Classical.choice inferInstance
  let : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') := htwo.2.1 m'
  exact ExactReduction.inducedMap_surjective _ _ _
    (kernelReduction_kernel e a r m f A hR)
    (scalarImage_eq_reduction_ker 2 (by decide) (UnitSurgery.Target A hR) 3).symm
    (kernelReduction_surjective e a r m f A hR d hd)
    (nativeLift_surjective f A hR d hd) (TwoConnectedCoefficients.middleReduction_surjective m')

theorem modTwoSurgeryMapInt_kernel : LinearMap.ker (modTwoSurgeryMapInt e a r m f A hR d hd) =
    Submodule.span ℤ {orthogonalAttachingClass e a r m f} := by
  have h := ExactReduction.inducedMap_kernel (nativeLift f A hR d hd)
    (kernelReduction e a r m f A hR) (reductionHomologyMap 2 (UnitSurgery.Target A hR) 3)
    (kernelReduction_kernel e a r m f A hR)
    (scalarImage_eq_reduction_ker 2 (by decide) (UnitSurgery.Target A hR) 3).symm
    (kernelReduction_surjective e a r m f A hR d hd) (geometricAttachingClass f A hR d hd)
    (nativeLift_kernel_geometric f A hR d hd) (nativeLift_surjective f A hR d hd)
  rw [kernelReduction_attaching] at h
  exact h

theorem modTwoSurgeryMap_kernel : LinearMap.ker (modTwoSurgeryMap e a r m f A hR d hd) =
    Submodule.span (ZMod 2) {orthogonalAttachingClass e a r m f} := by
  ext x
  change x ∈ LinearMap.ker (modTwoSurgeryMapInt e a r m f A hR d hd) ↔ _
  rw [modTwoSurgeryMapInt_kernel, mem_span_int_iff_modTwo]

def modTwoSurgeryQuotientEquiv :
    (LinearMap.ker (orthogonalFunctional e r m f) ⧸
      Submodule.span (ZMod 2) {orthogonalAttachingClass e a r m f}) ≃ₗ[ZMod 2]
        ModHomology 2 (UnitSurgery.Target A hR) 3 :=
  (Submodule.quotEquivOfEq _ _ (modTwoSurgeryMap_kernel e a r m f A hR d hd).symm).trans
    ((modTwoSurgeryMap e a r m f A hR d hd).quotKerEquivOfSurjective
      (modTwoSurgeryMap_surjective e a r m f A hR d hd))

theorem modTwoSurgeryQuotientEquiv_mk (x : LinearMap.ker (orthogonalFunctional e r m f)) :
    modTwoSurgeryQuotientEquiv e a r m f A hR d hd (Submodule.Quotient.mk x) =
      modTwoSurgeryMap e a r m f A hR d hd x := by
  change (modTwoSurgeryMap e a r m f A hR d hd).quotKerEquivOfSurjective
    (modTwoSurgeryMap_surjective e a r m f A hR d hd)
    (Submodule.quotEquivOfEq _ _ (modTwoSurgeryMap_kernel e a r m f A hR d hd).symm
      (Submodule.Quotient.mk x)) = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

theorem modTwoSurgeryQuotientEquiv_reduction (x : LinearMap.ker (detector f A hR)) :
    modTwoSurgeryQuotientEquiv e a r m f A hR d hd
      (Submodule.Quotient.mk (kernelReduction e a r m f A hR x)) =
        reductionHomologyMap 2 (UnitSurgery.Target A hR) 3 (nativeLift f A hR d hd x) := by
  rw [modTwoSurgeryQuotientEquiv_mk, modTwoSurgeryMap_reduction]

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector
