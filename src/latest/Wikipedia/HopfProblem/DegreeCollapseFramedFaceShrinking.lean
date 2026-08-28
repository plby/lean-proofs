import Wikipedia.HopfProblem.DegreeCollapseEmbeddedSphereFace
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Retain a framed sphere's exact core inside a prescribed open set

Restrict the actual native chart to an open neighborhood of its core.
Compactness supplies a uniform positive normal radius. Scaling the normal
parameter constructs a full closed face whose whole chart target lies in
that open set and whose core is exactly the original continuous map.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [T2Space M]
  (B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)

theorem exists_shrunk_face_in_open (U : Set M) (hU : IsOpen U)
    (hcore : ∀ s, FramedSurgery.coreMap (E := Vector 4) B s ∈ U) :
    ∃ B' : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M,
      FramedSurgery.coreMap (E := Vector 4) B' = FramedSurgery.coreMap (E := Vector 4) B ∧
      B'.chart.target ⊆ U := by
  let Φ := PartialChart.restrictTarget B.chart hU
  have hz (s : Sphere 3) : (s, (0 : Vector 3)) ∈ Φ.source := by
    refine ⟨B.source ⟨mem_univ _, by simp⟩, ?_⟩
    change B.chart (s, 0) ∈ U
    rw [B.point s ⟨0, by simp⟩]
    exact hcore s
  obtain ⟨ε, hε, hεsource⟩ := exists_uniform_closedProductTube Φ.open_source hz
  let L : Vector 3 ≃L[ℝ] Vector 3 :=
    (LinearEquiv.smulOfNeZero ℝ (Vector 3) (ε / 2) (half_pos hε).ne').toContinuousLinearEquiv
  have hL (v : Vector 3) (hv : v ∈ closedBall (0 : Vector 3) 1) :
      ‖L v‖ ≤ ε := by
    have hv' : ‖v‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hv
    change ‖(ε / 2) • v‖ ≤ ε
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    nlinarith
  let j : Sphere 3 × MorseHandle.UnitDisk (Vector 3) → Sphere 3 × Vector 3 :=
    fun p ↦ (p.1, L p.2.val)
  have hj : Continuous j := continuous_fst.prodMk
    (L.continuous.comp (continuous_subtype_val.comp continuous_snd))
  have hjs (p : Sphere 3 × MorseHandle.UnitDisk (Vector 3)) : j p ∈ Φ.source :=
    hεsource p.1 _ (hL p.2.val p.2.property)
  have hcont : Continuous (Φ ∘ j) := Φ.contMDiffOn.continuousOn.comp_continuous hj hjs
  have hinj : Injective (Φ ∘ j) := by
    intro p q he
    have hpq := Φ.injOn (hjs p) (hjs q) he
    apply Prod.ext
    · exact congrArg (Prod.fst : Sphere 3 × Vector 3 → Sphere 3) hpq
    · apply Subtype.ext
      exact L.injective (congrArg (Prod.snd : Sphere 3 × Vector 3 → Vector 3) hpq)
  let D := (Diffeomorph.refl (𝓡 3) (Sphere 3) ∞).prodCongr L.toDiffeomorph
  let B' : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M := {
    map := ⟨Φ ∘ j, hcont⟩
    closedEmbedding := hcont.isClosedEmbedding hinj
    chart := D.toPartialDiffeomorph.trans Φ
    source := fun p hp ↦ ⟨mem_univ _, hεsource p.1 _ (hL p.2 hp.2)⟩
    point := fun _ _ ↦ rfl }
  refine ⟨B', ContinuousMap.ext (fun s ↦ ?_), fun _ hy ↦ hy.1.2⟩
  change B.chart (s, L 0) = B.map (s, ⟨0, by simp⟩)
  rw [map_zero]
  exact B.point s ⟨0, by simp⟩

end Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative
