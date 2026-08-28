import Wikipedia.HopfProblem.DegreeCollapseHomologyFramedRepresentative
import Wikipedia.HopfProblem.DegreeCollapseFramedDualHomology
import Wikipedia.NoExoticSixSphere.Topology.SimplyConnectedSphere

/-!
# Native surgery reduction from a unit value on actual middle homology

Third Hurewicz, the embedded representative construction, and the full
native framed tube realize the supplied H3 class. Coherent orientations
and all model identifications are constructed. The homological detector
criterion then constructs its single-intersection framed dual and proves
the actual surgery target's two-connectivity and rank drop. No geometric
dual, framed representative, transversality, or orientation is supplied.
The unit detector value itself remains an explicit hypothesis.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedDual

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct SmoothCube
open Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology OrbitPair.DeterminantSignCover

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem exists_framed_dual_of_unit_homology (c : SingularHomology M 3)
    (hc : DualCover.markedDetector (E := Vector 4) (UnitSurgery.face A hR)
      (ContinuousLinearEquiv.refl ℝ (Vector 3)) c = 1) :
    ∃ B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M, ∃ q u : Sphere 3,
      integralSphereClass (FramedSurgery.coreMap (E := Vector 4) B) = c ∧
      (∀ x y, f x = FramedSurgery.coreMap (E := Vector 4) B y ↔ x = q ∧ y = u) ∧
      Surjective ((mfderiv (𝓡 3) (𝓡 6) f q).coprod
        (mfderiv (𝓡 3) (𝓡 6) (FramedSurgery.coreMap (E := Vector 4) B) u)) := by
  let m : M := f (Stiefel.pole 3)
  let : Subsingleton (π_ 2 M m) :=
    (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv m).injective.subsingleton
  obtain ⟨B, hB⟩ := FramedRepresentative.exists_homology_framed_representative e a m c
  let : SimplyConnectedSpace (Sphere 3) := EuclideanSphere.simplyConnectedSpace 1
  let : LocallyPathConnectedSpace (Sphere 3) :=
    ChartedSpace.locallyPathConnectedSpace (Vector 3) (Sphere 3)
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace (Vector 6) M
  obtain ⟨oS⟩ := nonempty_orientation (tangentBundleCore (𝓡 3) (Sphere 3))
  obtain ⟨oM⟩ := nonempty_orientation (tangentBundleCore (𝓡 6) M)
  let j : (ℝ × Vector 3) ≃L[ℝ] Vector 4 := ContinuousLinearEquiv.ofFinrankEq
    (by simp [Module.finrank_prod])
  let K : (Vector 3 × Vector 3) ≃L[ℝ] Vector 6 := ContinuousLinearEquiv.ofFinrankEq
    (by simp [Module.finrank_prod])
  have hc' : DualCover.markedDetector (E := Vector 4) (UnitSurgery.face A hR)
      (ContinuousLinearEquiv.refl ℝ (Vector 3))
      (singularHomologyMap (FramedSurgery.coreMap (E := Vector 4) B) 3
        integralCubeSphereClass) = 1 := by
    change DualCover.markedDetector (E := Vector 4) (UnitSurgery.face A hR)
      (ContinuousLinearEquiv.refl ℝ (Vector 3)) (integralSphereClass _) = 1
    rw [hB]
    exact hc
  obtain ⟨B', q, u, H, hcross, ht⟩ := exists_framed_dual_of_detector_image
    oS oM j K f A hR B integralCubeSphereClass hc'
  exact ⟨B', q, u, (integralSphereClass_homotopic H).symm.trans hB, hcross, ht⟩

theorem compact_surgery_reduction_of_unit_homology (c : SingularHomology M 3)
    (hc : DualCover.markedDetector (E := Vector 4) (UnitSurgery.face A hR)
      (ContinuousLinearEquiv.refl ℝ (Vector 3)) c = 1) :
    SimplyConnectedSpace (UnitSurgery.Target A hR) ∧
      (∀ x : UnitSurgery.Target A hR, Subsingleton (π_ 2 (UnitSurgery.Target A hR) x)) ∧
      Module.finrank ℤ (SingularHomology (UnitSurgery.Target A hR) 3) + 2 ≤
        Module.finrank ℤ (SingularHomology M 3) := by
  obtain ⟨B, q, u, _, hcross, ht⟩ := exists_framed_dual_of_unit_homology f A hR c hc
  exact TraceBody.compact_dual_surgery_reduction f A hR B q u hcross ht

end Wikipedia.HopfProblem.DegreeCollapse.FramedDual
