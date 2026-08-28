import Wikipedia.SmoothSixDPoincare.NativeAnnularLowerPatch
import Wikipedia.SmoothSixDPoincare.FramedSurgeryRetainedFaceSeparation
import Wikipedia.SmoothSixDPoincare.OpenSurgeryExterior

/-!
# The new patch, corner annulus, and open exterior cover the native framed boundary

An old-patch point either lies outside the full attaching face, belongs to
its strict interior, or has normal radius one. These cases give precisely
the open exterior, original new patch, and native annular patch.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open FramedSurgery MorseHandle

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (m n : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]
  [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
  (P : letI := RegularLevel.chartedSpace hf d.lower_regular
    SmoothBoundaryData (d.attachingSmoothFace hf m) n)

open Classical in
theorem nativeBelt_boundary_patch_cover :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI := P.charted
    ∀ z : d.FramedBoundary hf m n, z ∈ P.newPartial.target ∨
      z ∈ (d.annularBoundaryPartial m n hf P).target ∨
      z ∈ (boundaryPair (d.attachingSmoothFace hf m) n).newOpenExterior := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ := P.charted
  intro z
  rcases cover (d.attachingSmoothFace hf m) n z with ⟨x, rfl⟩ | ⟨y, rfl⟩
  · by_cases hx : x.val ∈ range (d.attachingSmoothFace hf m).map
    · obtain ⟨⟨u, v⟩, hp⟩ := hx
      have hv0 : v.val ≠ 0 := fun h => x.property
        (hp ▸ (face_mem_core_iff (d.attachingSmoothFace hf m) u v).mpr h)
      by_cases hv : ‖v.val‖ < 1
      · left
        let w : Overlap d.chart.NegativeCoordinates d.chart.PositiveCoordinates :=
          (u, ⟨v.val, hv0, hv⟩)
        have hold : oldOverlap (d.attachingSmoothFace hf m) w = x := Subtype.ext hp
        have he : P.newPartial (newOverlap m n w) = oldMap (d.attachingSmoothFace hf m) n x :=
          (P.new_point _).trans
            ((overlap_identification (d.attachingSmoothFace hf m) n w).symm.trans
              (congrArg (oldMap (d.attachingSmoothFace hf m) n) hold))
        rw [← he]
        apply P.newPartial.map_source
        rw [P.new_source]
        trivial
      · right; left
        have hn : ‖v.val‖ = 1 :=
          le_antisymm (mem_closedBall_zero_iff.mp v.property) (le_of_not_gt hv)
        let a : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates :=
          (u, ⟨v.val, by
            change (1 / 2 : ℝ) < ‖v.val‖ ∧ ‖v.val‖ < (3 / 2 : ℝ)
            rw [hn]
            norm_num⟩)
        have hlower : d.annularLowerPoint a = (d.attachingSmoothFace hf m).map (u, v) :=
          (d.attachingNeighborhood_eq_face_iff hf m (d.annularAttachingPoint a) (u, v)).mpr rfl
        have ha : d.annularOldPoint hf m a = x := Subtype.ext (hlower.trans hp)
        have he : d.annularBoundaryPartial m n hf P a = oldMap (d.attachingSmoothFace hf m) n x :=
          (d.annularBoundaryPartial_point m n hf P a).trans
            (congrArg (oldMap (d.attachingSmoothFace hf m) n) ha)
        rw [← he]
        apply (d.annularBoundaryPartial m n hf P).map_source
        rw [d.annularBoundaryPartial_source]
        trivial
    · right; right
      rintro ⟨q, hq⟩
      exact oldMap_ne_closedNewMap_of_not_mem (d.attachingSmoothFace hf m) n x hx
        (newFaceCoordinates d.chart.NegativeCoordinates d.chart.PositiveCoordinates q) hq.symm
  · left
    rw [← P.new_point y]
    apply P.newPartial.map_source
    rw [P.new_source]
    trivial

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
