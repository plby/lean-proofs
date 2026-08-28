import Wikipedia.HopfProblem.DegreeCollapseSevenAttachingRoundingData

/-!
# The actual compact rounded attachment in the ambient Euclidean space

Add precisely the supported rounded collar region to the constructed
unrounded attachment. The new set is compact; in the uniform collar band
its exact domain is the regular rounded superlevel. Positive-height points
are unchanged. The global smooth boundary atlas and boundary identification
are not yet supplied by this set-level construction.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def addedParameters : Set ((Sphere 3 × Vector 4) × ℝ) :=
  {p | p.1.2 ∈ closedBall (0 : Vector 4) (outerRadius A) ∧
    p.2 ∈ Icc (-2 * (bump A).rOut) 0 ∧
    0 ≤ GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A) (p.1.2, p.2)}

theorem isCompact_addedParameters : IsCompact (addedParameters A) := by
  let B : Set ((Sphere 3 × Vector 4) × ℝ) :=
    ((univ : Set (Sphere 3)) ×ˢ closedBall (0 : Vector 4) (outerRadius A)) ×ˢ
      Icc (-2 * (bump A).rOut) 0
  have hB : IsCompact B :=
    (isCompact_univ.prod (isCompact_closedBall _ _)).prod isCompact_Icc
  have hc : Continuous (fun p : (Sphere 3 × Vector 4) × ℝ ↦
      GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A) (p.1.2, p.2)) :=
    (GeneralRoundedHandleCorner.contDiff_level _ _).continuous.comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have he : addedParameters A = B ∩ {p |
      0 ≤ GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A) (p.1.2, p.2)} := by
    ext p
    simp only [addedParameters, B, mem_inter_iff, mem_prod, mem_univ, true_and,
      mem_ofPred_eq, and_assoc]
  rw [he]
  exact hB.inter_right (isClosed_le continuous_const hc)

theorem addedParameters_subset_source : addedParameters A ⊆ A.tubeHeightCoordinates.source := by
  intro p hp
  apply (A.mem_tubeHeightCoordinates_source p).mpr
  exact (closedBall_subset_ball (outerRadius_lt A)) hp.1

theorem isCompact_addedImage : IsCompact (A.collarSheet '' addedParameters A) :=
  (isCompact_addedParameters A).image_of_continuousOn
    (A.contMDiffOn_collarSheet.continuousOn.mono (addedParameters_subset_source A))

def ambientSet : Set (Vector (e.ambientDimension + 6)) :=
  UnroundedTrace.ambientSet A ∪ A.collarSheet '' addedParameters A

theorem unrounded_subset : UnroundedTrace.ambientSet A ⊆ ambientSet A := subset_union_left

theorem isCompact_ambientSet : IsCompact (ambientSet A) :=
  (UnroundedTrace.isCompact_ambientSet A).union (isCompact_addedImage A)

theorem isClosed_ambientSet : IsClosed (ambientSet A) := (isCompact_ambientSet A).isClosed

theorem sheet_mem_iff (s : Sphere 3) {v : Vector 4}
    (hv : v ∈ ball (0 : Vector 4) A.radius) {t : ℝ} (ht : ‖t‖ ≤ collarHeight A) :
    A.collarSheet ((s, v), t) ∈ ambientSet A ↔
      0 ≤ GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A) (v, t) := by
  have hp : ((s, v), t) ∈ A.tubeHeightCoordinates.source :=
    (A.mem_tubeHeightCoordinates_source _).mpr hv
  constructor
  · rintro (hw | ⟨q, hq, he⟩)
    · exact GeneralRoundedHandleCorner.nonneg_of_corner (bump A)
        (UnroundedTrace.handleRadius_pos A).le ((sheet_mem_unrounded_iff A s hv ht).mp hw)
    · have hqp : q = ((s, v), t) :=
        A.injOn_collarSheet (addedParameters_subset_source A hq) hp he
      have hqlevel := hq.2.2
      rw [hqp] at hqlevel
      exact hqlevel
  · intro hL
    by_cases hcorner : 0 ≤ t ∨ v ∈ closedBall (0 : Vector 4) (UnroundedTrace.handleRadius A)
    · exact Or.inl ((sheet_mem_unrounded_iff A s hv ht).mpr hcorner)
    · obtain ⟨hti, hvhalf⟩ := not_or.mp hcorner
      have h := GeneralRoundedHandleCorner.added_point_bounds (bump A)
        (UnroundedTrace.handleRadius_pos A).le hL (lt_of_not_ge hti) hvhalf
      exact Or.inr ⟨((s, v), t),
        ⟨mem_outerBall A h.2.le, ⟨h.1.le, (lt_of_not_ge hti).le⟩, hL⟩, rfl⟩

theorem regular_corner_zero {p : Vector 4 × ℝ}
    (hp : GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A) p = 0) :
    Surjective (fderiv ℝ
      (GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A)) p) :=
  GeneralRoundedHandleCorner.regular_zero (bump A) (UnroundedTrace.handleRadius_pos A) hp

theorem positive_height_unchanged (m : M) {t : ℝ} (ht : 0 < t) :
    (HeightCylinder.heightCylinder e) (m, t) ∈ ambientSet A ↔
      (HeightCylinder.heightCylinder e) (m, t) ∈ UnroundedTrace.ambientSet A := by
  constructor
  · rintro (hp | ⟨q, hq, he⟩)
    · exact hp
    · have heq : (A.tube q.1, q.2) = (m, t) := (HeightCylinder.injective_heightCylinder e) he
      have hqt : q.2 = t := congrArg (Prod.snd : M × ℝ → ℝ) heq
      have hnonpos : q.2 ≤ 0 := hq.2.1.2
      rw [hqt] at hnonpos
      exact (not_lt_of_ge hnonpos ht).elim
  · intro hp
    exact unrounded_subset A hp

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
