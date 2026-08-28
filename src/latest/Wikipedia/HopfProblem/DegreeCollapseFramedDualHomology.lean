import Wikipedia.HopfProblem.DegreeCollapseFramedCountComparison
import Wikipedia.HopfProblem.DegreeCollapseDualCountHomology
import Wikipedia.HopfProblem.DegreeCollapseFramedDualReduction
import Wikipedia.SmoothSixDPoincare.GlobalAmbientTransversality

/-!
# Construct the actual framed dual from a unit homology-detector value

The marked detector is the genuine complement-and-tube homology map.
Its unit value gives a unit normal count, hence a unit intrinsic count.
Ambient transversality is constructed first and preserves the original
homology class. The full framed face is then transported by the finite
Whitney reduction. No initial transversality, local degrees, unit signed
count, or single-intersection dual is an additional geometric hypothesis.
Existence of a framed face with unit detector value remains to be proved.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedDual

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology OrbitPair.DeterminantSignCover

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [SimplyConnectedSpace M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (oS : Orientation (tangentBundleCore (𝓡 3) (Sphere 3)))
  (oM : Orientation (tangentBundleCore (𝓡 6) M))
  (j : (ℝ × Vector 3) ≃L[ℝ] Vector 4)
  (K : (Vector 3 × Vector 3) ≃L[ℝ] Vector 6)
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)

include j in
theorem dualCount_unit_of_detector_image
    (ht : ∀ x y, f y = FramedSurgery.coreMap (E := Vector 4) B x → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) (FramedSurgery.coreMap (E := Vector 4) B) x).coprod
        (mfderiv (𝓡 3) (𝓡 6) f y)))
    (c : SingularHomology (Sphere 3) 3)
    (hc : DualCover.markedDetector (E := Vector 4) (UnitSurgery.face A hR)
      (ContinuousLinearEquiv.refl ℝ (Vector 3))
      (singularHomologyMap (FramedSurgery.coreMap (E := Vector 4) B) 3 c) = 1) :
    (dualCount oS oM K f A hR B ht).natAbs = 1 := by
  let U := UnitSurgery.face A hR
  let g := FramedSurgery.coreMap (E := Vector 4) B
  have hu : FramedSurgery.coreMap (E := Vector 4) U = f := TraceBody.unitFace_coreMap_eq f A hR
  have hgood : MutualSheets.Good (D := Vector 3) (E := Vector 6)
      (FramedSurgery.coreMap (E := Vector 4) U) g := by
    rw [hu]
    exact dual_good f B ht
  have hfin : (DualCover.crossings (E := Vector 4) U g).Finite :=
    MutualSheets.finite_crossingPoints (by simp) (by simp)
      (FramedSurgery.contMDiff_coreMap (E := Vector 4) U) (FramedCore.injective_core U) hgood
  have hn := DualCover.normalCount_unit_of_detector_image (E := Vector 4) U j
    (ContinuousLinearEquiv.refl ℝ (Vector 3)) g hgood.1 hgood.2.2.2 hfin c hc
  have hcomp := FramedNormal.count_natAbs_eq U oS oM j K g hgood hfin
  have hcount := hcomp.symm.trans hn
  change (MutualSheets.signedCount oS oS oM K
    (FramedSurgery.coreMap (E := Vector 4) B) f _).natAbs = 1
  simpa only [hu] using hcount

include A hR in
theorem exists_transverse_dual_face :
    ∃ ψ : Diffeomorph (𝓡 6) (𝓡 6) M M ∞,
      SupportedDiffeomorph.IsotopicToIdentity ψ ∧
      (FramedSurgery.coreMap (E := Vector 4) B).Homotopic
        (FramedSurgery.coreMap (E := Vector 4) (B.postcompose ψ)) ∧
      ∀ x y, f y = FramedSurgery.coreMap (E := Vector 4) (B.postcompose ψ) x → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) (FramedSurgery.coreMap (E := Vector 4) (B.postcompose ψ)) x).coprod
          (mfderiv (𝓡 3) (𝓡 6) f y)) := by
  obtain ⟨ψ, hiso, ht⟩ := NativeTransversality.exists_ambient_transverse_diffeomorph
    (FramedSurgery.contMDiff_coreMap (E := Vector 4) B) (attaching_smooth f A hR) (by simp)
  refine ⟨ψ, hiso, hiso.comp_homotopic (FramedSurgery.coreMap (E := Vector 4) B), ?_⟩
  exact ht

include oS oM j K in
theorem exists_framed_dual_of_detector_image
    (c : SingularHomology (Sphere 3) 3)
    (hc : DualCover.markedDetector (E := Vector 4) (UnitSurgery.face A hR)
      (ContinuousLinearEquiv.refl ℝ (Vector 3))
      (singularHomologyMap (FramedSurgery.coreMap (E := Vector 4) B) 3 c) = 1) :
    ∃ B' : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M, ∃ q u : Sphere 3,
      (FramedSurgery.coreMap (E := Vector 4) B).Homotopic (FramedSurgery.coreMap (E := Vector 4) B') ∧
      (∀ x y, f x = FramedSurgery.coreMap (E := Vector 4) B' y ↔ x = q ∧ y = u) ∧
      Surjective ((mfderiv (𝓡 3) (𝓡 6) f q).coprod
        (mfderiv (𝓡 3) (𝓡 6) (FramedSurgery.coreMap (E := Vector 4) B') u)) := by
  obtain ⟨ψ, _, hhom, ht⟩ := exists_transverse_dual_face f A hR B
  have hc' : DualCover.markedDetector (E := Vector 4) (UnitSurgery.face A hR)
      (ContinuousLinearEquiv.refl ℝ (Vector 3))
      (singularHomologyMap (FramedSurgery.coreMap (E := Vector 4) (B.postcompose ψ)) 3 c) = 1 := by
    rw [← homotopic_homologyMap hhom 3]
    exact hc
  have hcount := dualCount_unit_of_detector_image oS oM j K f A hR (B.postcompose ψ) ht c hc'
  obtain ⟨φ, q, u, _, hhom', hcross, htrans⟩ :=
    exists_framed_single_dual_of_unit_count oS oM K f A hR (B.postcompose ψ) ht hcount
  exact ⟨(B.postcompose ψ).postcompose φ, q, u, hhom.trans hhom', hcross, htrans⟩

include oS oM j K in
theorem compact_surgery_reduction_of_detector_image
    [Subsingleton (SingularHomology M 2)]
    (c : SingularHomology (Sphere 3) 3)
    (hc : DualCover.markedDetector (E := Vector 4) (UnitSurgery.face A hR)
      (ContinuousLinearEquiv.refl ℝ (Vector 3))
      (singularHomologyMap (FramedSurgery.coreMap (E := Vector 4) B) 3 c) = 1) :
    SimplyConnectedSpace (UnitSurgery.Target A hR) ∧
      (∀ x : UnitSurgery.Target A hR, Subsingleton (π_ 2 (UnitSurgery.Target A hR) x)) ∧
      Module.finrank ℤ (SingularHomology (UnitSurgery.Target A hR) 3) + 2 ≤
        Module.finrank ℤ (SingularHomology M 3) := by
  obtain ⟨B', q, u, _, hcross, htrans⟩ :=
    exists_framed_dual_of_detector_image oS oM j K f A hR B c hc
  exact TraceBody.compact_dual_surgery_reduction f A hR B' q u hcross htrans

end Wikipedia.HopfProblem.DegreeCollapse.FramedDual
