import Wikipedia.SmoothSixDPoincare.NativeAnnularExteriorRealization

/-!
# The same native annular formula holds on both sides of the corner

Inside the open face, the original quotient overlap and the explicit belt
correction give the upper coordinate map. Outside, the original model
boundary-orbit theorem gives that very same map, including radius one.
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

open Classical in
theorem beltFramedBoundaryRealization_newMap :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ y : NewPatch d.chart.NegativeCoordinates d.chart.PositiveCoordinates,
      d.beltFramedBoundaryRealization hf m n (newMap (d.attachingSmoothFace hf m) n y) =
        d.beltClosedDiskMap (⟨y.1.val, (mem_ball_zero_iff.mp y.1.property).le⟩, y.2) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro y
  let z : ClosedNewFace d.chart.NegativeCoordinates d.chart.PositiveCoordinates :=
    (⟨y.1.val, ball_subset_closedBall y.1.property⟩, y.2)
  have hz : closedNewMap (d.attachingSmoothFace hf m) n z =
      newMap (d.attachingSmoothFace hf m) n y :=
    closedNewMap_open (d.attachingSmoothFace hf m) n y
  exact (congrArg (d.beltFramedBoundaryRealization hf m n) hz.symm).trans
    (d.beltFramedBoundaryRealization_newFace hf m n z)

open Classical in
theorem beltFramedBoundaryRealization_annularInside :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates,
      ‖z.2.val‖ < 1 →
      d.beltFramedBoundaryRealization hf m n
        (oldMap (d.attachingSmoothFace hf m) n (d.annularOldPoint hf m z)) =
        d.annularUpperPoint z := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro z hz
  let w : Overlap d.chart.NegativeCoordinates d.chart.PositiveCoordinates :=
    (z.1, ⟨z.2.val, surgeryAnnulus_ne_zero z.2, hz⟩)
  have hlow : d.annularLowerPoint z = (d.attachingSmoothFace hf m).map
      (z.1, ⟨z.2.val, mem_closedBall_zero_iff.mpr hz.le⟩) :=
    (d.attachingNeighborhood_eq_face_iff hf m (d.annularAttachingPoint z) _).mpr rfl
  have hold : oldOverlap (d.attachingSmoothFace hf m) w = d.annularOldPoint hf m z :=
    Subtype.ext hlow.symm
  let y := newOverlap m n w
  have hupper : d.beltClosedDiskMap
      (⟨y.1.val, (mem_ball_zero_iff.mp y.1.property).le⟩, y.2) = d.annularUpperPoint z := by
    apply congrArg (fun q : d.chart.beltSource d.radius d.radius_pos =>
      (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos q).val)
    apply Subtype.ext
    exact Prod.ext (Subtype.ext rfl) rfl
  exact (congrArg (fun x : oldPatch (d.attachingSmoothFace hf m) =>
    d.beltFramedBoundaryRealization hf m n (oldMap (d.attachingSmoothFace hf m) n x))
      hold.symm).trans
    ((congrArg (d.beltFramedBoundaryRealization hf m n)
      (overlap_identification (d.attachingSmoothFace hf m) n w)).trans
        ((d.beltFramedBoundaryRealization_newMap hf m n y).trans hupper))

open Classical in
theorem beltFramedBoundaryRealization_annular :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates,
      d.beltFramedBoundaryRealization hf m n
        (oldMap (d.attachingSmoothFace hf m) n (d.annularOldPoint hf m z)) =
        d.annularUpperPoint z := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro z
  by_cases hz : ‖z.2.val‖ < 1
  · exact d.beltFramedBoundaryRealization_annularInside hf m n z hz
  · exact d.beltFramedBoundaryRealization_annularOutside hf m n z (le_of_not_gt hz)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
