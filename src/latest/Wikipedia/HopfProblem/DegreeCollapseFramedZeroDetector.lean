import Wikipedia.HopfProblem.DegreeCollapseHomologicalDualSurgery

/-!
# Actual disjoint framed representatives of the detector kernel

A zero value on an actual integral H3 class gives zero normal count for
its constructed framed representative. The cubical sphere class is
nonzero, as its genuine mod-two reduction is nonzero. The intrinsic
Whitney count is therefore zero. Finite ambient cancellation removes all
crossings with the fixed core, preserving the represented homology class.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open EuclideanEmbedding SmoothCube Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology OrbitPair.DeterminantSignCover

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) := ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩

theorem integralCubeSphereClass_ne_zero : integralCubeSphereClass ≠ 0 := by
  intro hz
  apply modTwoCubeSphereClass_ne_zero
  change SphereHomologyCoefficients.reductionHomologyMap 2 (Sphere 3) 3
    integralCubeSphereClass = 0
  rw [hz, map_zero]

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (A : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)

include e a in
theorem exists_framed_avoiding_of_zero_homology (c : SingularHomology M 3)
    (hc : DualCover.markedDetector (E := Vector 4) A
      (ContinuousLinearEquiv.refl ℝ (Vector 3)) c = 0) :
    ∃ B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M,
      integralSphereClass (FramedSurgery.coreMap (E := Vector 4) B) = c ∧
      Disjoint (range (FramedSurgery.coreMap (E := Vector 4) B))
        (range (FramedSurgery.coreMap (E := Vector 4) A)) := by
  let m : M := FramedSurgery.coreMap (E := Vector 4) A (Stiefel.pole 3)
  let : Subsingleton (π_ 2 M m) :=
    (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv m).injective.subsingleton
  obtain ⟨B, hB⟩ := exists_homology_framed_representative e a m c
  obtain ⟨ψ, hψ, ht⟩ := NativeTransversality.exists_ambient_transverse_diffeomorph
    (FramedSurgery.contMDiff_coreMap (E := Vector 4) B)
    (FramedSurgery.contMDiff_coreMap (E := Vector 4) A) (by simp)
  let B₁ := B.postcompose ψ
  let g := FramedSurgery.coreMap (E := Vector 4) B₁
  let f := FramedSurgery.coreMap (E := Vector 4) A
  have H : (FramedSurgery.coreMap (E := Vector 4) B).Homotopic g :=
    hψ.comp_homotopic (FramedSurgery.coreMap (E := Vector 4) B)
  have hgclass : integralSphereClass g = c := (integralSphereClass_homotopic H).symm.trans hB
  have hgood : MutualSheets.Good (D := Vector 3) (E := Vector 6) f g :=
    ⟨FramedSurgery.contMDiff_coreMap (E := Vector 4) B₁, FramedCore.injective_core B₁,
      FramedCore.injective_core_derivative B₁, ht⟩
  have hf := FramedSurgery.contMDiff_coreMap (E := Vector 4) A
  have hfi := FramedCore.injective_core A
  have hfd := FramedCore.injective_core_derivative A
  have hfin : (DualCover.crossings (E := Vector 4) A g).Finite :=
    MutualSheets.finite_crossingPoints (by simp) (by simp) hf hfi hgood
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
  have hc' : DualCover.markedDetector (E := Vector 4) A
      (ContinuousLinearEquiv.refl ℝ (Vector 3))
      (singularHomologyMap g 3 integralCubeSphereClass) = 0 := by
    change DualCover.markedDetector (E := Vector 4) A
      (ContinuousLinearEquiv.refl ℝ (Vector 3)) (integralSphereClass g) = 0
    rw [hgclass]
    exact hc
  have hn := DualCover.normalCount_zero_of_detector_image (E := Vector 4) A j
    (ContinuousLinearEquiv.refl ℝ (Vector 3)) g hgood.1 hgood.2.2.2 hfin
    integralCubeSphereClass integralCubeSphereClass_ne_zero hc'
  have hcomp := FramedNormal.count_natAbs_eq A oS oM j K g hgood hfin
  have hcount : (MutualSheets.signedCount oS oS oM K g f hfin).natAbs = 0 := by
    rw [hn, Int.natAbs_zero] at hcomp
    exact hcomp.symm
  obtain ⟨φ, g', hφ, heq, hgood', _, _, hcard⟩ :=
    MutualSheets.exists_minimal_crossing_sheet oS oS oM K (by simp) (by simp)
      g f hf hfi hfd hgood
  have hfin' := MutualSheets.finite_crossingPoints (by simp) (by simp) hf hfi hgood'
  have hempty : MutualSheets.crossingPoints g' f = ∅ :=
    (Set.ncard_eq_zero hfin').mp (hcard.trans hcount)
  let B' := B₁.postcompose φ
  have heq' : g' = FramedSurgery.coreMap (E := Vector 4) B' :=
    ContinuousMap.ext heq
  have H' : g.Homotopic (FramedSurgery.coreMap (E := Vector 4) B') := hφ.comp_homotopic g
  refine ⟨B', (integralSphereClass_homotopic H').symm.trans hgclass, ?_⟩
  rw [← heq']
  apply disjoint_left.mpr
  rintro z ⟨x, rfl⟩ hz
  have hx : x ∈ MutualSheets.crossingPoints g' f := hz
  rw [hempty] at hx
  exact hx

end Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative
