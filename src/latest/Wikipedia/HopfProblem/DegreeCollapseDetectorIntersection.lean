import Wikipedia.HopfProblem.DegreeCollapseDetectorModTwo
import Wikipedia.HopfProblem.DegreeCollapseHomologyFramedRepresentative
import Wikipedia.HopfProblem.DegreeCollapseSurgeryDetectorKernel

/-!
# The actual integer detector reduces to geometric intersection on H3

Construct a full framed representative of each actual integral class and
make it transverse by an ambient isotopy. The marked-detector formula
and the genuine intersection count then agree modulo two. Hurewicz and
homotopy invariance retain the original class. No detector unit value or
global nondegeneracy hypothesis is used in this comparison.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open EuclideanEmbedding SmoothCube Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [T2Space M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]

include a in
theorem FramedNormal.markedDetector_modTwo_eq_intersection
    (A : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M) (c : SingularHomology M 3) :
    (DualCover.markedDetector (E := Vector 4) A (ContinuousLinearEquiv.refl ℝ (Vector 3)) c : ZMod 2) =
      e.integralHomologyIntersection r m
        (integralSphereClass (FramedSurgery.coreMap (E := Vector 4) A)) c := by
  obtain ⟨B, hB⟩ := FramedRepresentative.exists_homology_framed_representative e a m c
  obtain ⟨ψ, hiso, ht⟩ := NativeTransversality.exists_ambient_transverse_diffeomorph
    (FramedSurgery.contMDiff_coreMap (E := Vector 4) B)
    (FramedSurgery.contMDiff_coreMap (E := Vector 4) A) (by simp)
  let B' := B.postcompose ψ
  let g := FramedSurgery.coreMap (E := Vector 4) B'
  have H : (FramedSurgery.coreMap (E := Vector 4) B).Homotopic g :=
    hiso.comp_homotopic (FramedSurgery.coreMap (E := Vector 4) B)
  have hgclass : integralSphereClass g = c := (integralSphereClass_homotopic H).symm.trans hB
  have hgood : MutualSheets.Good (D := Vector 3) (E := Vector 6)
      (FramedSurgery.coreMap (E := Vector 4) A) g :=
    ⟨FramedSurgery.contMDiff_coreMap (E := Vector 4) B', FramedCore.injective_core B',
      FramedCore.injective_core_derivative B', ht⟩
  have hfin : (DualCover.crossings (E := Vector 4) A g).Finite :=
    MutualSheets.finite_crossingPoints (by simp) (by simp)
      (FramedSurgery.contMDiff_coreMap (E := Vector 4) A) (FramedCore.injective_core A) hgood
  let j : (ℝ × Vector 3) ≃L[ℝ] Vector 4 :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  have hcount := FramedNormal.markedDetector_modTwo_transverse A j g hgood.1 hgood.2.2.2 hfin
  have hinter := e.sphereIntersectionNumber_eq_parity r g
    (FramedSurgery.coreMap (E := Vector 4) A) hgood.1
    (FramedSurgery.contMDiff_coreMap (E := Vector 4) A)
    (fun x y h ↦ hgood.2.2.2 x y h.symm)
  have hhom := e.integralHomologyIntersection_integralSphereClass r m g
    (FramedSurgery.coreMap (E := Vector 4) A)
  rw [hgclass] at hcount hhom
  exact hcount.trans (hinter.symm.trans (hhom.symm.trans
    (e.integralHomologyIntersection_comm r m _ _)))

namespace SurgeryDetector

open EuclideanEmbedding.FramedAttachingProduct

variable [Subsingleton (SingularHomology M 2)]
  (f : C(Sphere 3, M)) (A : EuclideanEmbedding.FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem detector_modTwo_eq_intersection (c : SingularHomology M 3) :
    (detector f A hR c : ZMod 2) = e.integralHomologyIntersection r m (integralSphereClass f) c := by
  have h := FramedNormal.markedDetector_modTwo_eq_intersection e a r m (UnitSurgery.face A hR) c
  rw [TraceBody.unitFace_coreMap_eq f A hR] at h
  exact h

theorem detector_kernel_orthogonal (x : LinearMap.ker (detector f A hR)) :
    e.integralHomologyIntersection r m (integralSphereClass f) x = 0 := by
  rw [← detector_modTwo_eq_intersection e a r m f A hR]
  change ((detector f A hR x.val : ℤ) : ZMod 2) = 0
  rw [show detector f A hR x.val = 0 from x.property, Int.cast_zero]

end SurgeryDetector
end Wikipedia.HopfProblem.DegreeCollapse
