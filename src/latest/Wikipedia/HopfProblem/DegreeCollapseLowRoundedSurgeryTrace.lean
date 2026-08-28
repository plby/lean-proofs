import Wikipedia.HopfProblem.DegreeCollapseLowAttachingRoundingData

/-!

# The actual compact rounded low-dimensional ambient attachment

Add precisely the supported rounded collar region to the actual unrounded
union. The result is compact. In the constructed uniform collar band its
domain is exactly the regular rounded superlevel. Positive-height points
remain unchanged. The global smooth atlas is a separate next construction.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def addedParameters : Set ((NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ) :=
  {p | p.1.2 ∈ closedBall (0 : Vector (7 - d)) (outerRadius A) ∧
    p.2 ∈ Icc (-2 * (bump A).rOut) 0 ∧
    0 ≤ GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A) (p.1.2, p.2)}

theorem isCompact_addedParameters : IsCompact (addedParameters A) := by
  let B : Set ((NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ) :=
    ((univ : Set (NoExoticSixSphere.Sphere d)) ×ˢ
      closedBall (0 : Vector (7 - d)) (outerRadius A)) ×ˢ
      Icc (-2 * (bump A).rOut) 0
  have hB : IsCompact B :=
    (isCompact_univ.prod (isCompact_closedBall _ _)).prod isCompact_Icc
  have hc : Continuous (fun p : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ ↦
      GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A) (p.1.2, p.2)) :=
    (GeneralRoundedHandleCorner.contDiff_level _ _).continuous.comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have he : addedParameters A = B ∩ {p |
      0 ≤ GeneralRoundedHandleCorner.level (bump A)
        (UnroundedTrace.handleRadius A) (p.1.2, p.2)} := by
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

def ambientSet : Set (Vector (e.ambientDimension + (1 + (1 + (d + 1))))) :=
  UnroundedTrace.ambientSet A ∪ A.collarSheet '' addedParameters A

theorem unrounded_subset : UnroundedTrace.ambientSet A ⊆ ambientSet A := subset_union_left

theorem isCompact_ambientSet : IsCompact (ambientSet A) :=
  (UnroundedTrace.isCompact_ambientSet A).union (isCompact_addedImage A)

theorem isClosed_ambientSet : IsClosed (ambientSet A) := (isCompact_ambientSet A).isClosed

theorem sheet_mem_iff (s : NoExoticSixSphere.Sphere d) {v : Vector (7 - d)}
    (hv : v ∈ ball (0 : Vector (7 - d)) A.radius) {t : ℝ} (ht : ‖t‖ ≤ collarHeight A) :
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
    by_cases hcorner : 0 ≤ t ∨ v ∈ closedBall (0 : Vector (7 - d)) (UnroundedTrace.handleRadius A)
    · exact Or.inl ((sheet_mem_unrounded_iff A s hv ht).mpr hcorner)
    · obtain ⟨hti, hvhalf⟩ := not_or.mp hcorner
      have h := GeneralRoundedHandleCorner.added_point_bounds (bump A)
        (UnroundedTrace.handleRadius_pos A).le hL (lt_of_not_ge hti) hvhalf
      exact Or.inr ⟨((s, v), t),
        ⟨mem_outerBall A h.2.le, ⟨h.1.le, (lt_of_not_ge hti).le⟩, hL⟩, rfl⟩

theorem regular_corner_zero {p : Vector (7 - d) × ℝ}
    (hp : GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A) p = 0) :
    Surjective (fderiv ℝ
      (GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A)) p) :=
  GeneralRoundedHandleCorner.regular_zero (bump A) (UnroundedTrace.handleRadius_pos A) hp

theorem positive_height_unchanged (m : M) {t : ℝ} (ht : 0 < t) :
    (LowHeightCylinder.heightCylinder d e) (m, t) ∈ ambientSet A ↔
      (LowHeightCylinder.heightCylinder d e) (m, t) ∈ UnroundedTrace.ambientSet A := by
  constructor
  · rintro (hp | ⟨q, hq, he⟩)
    · exact hp
    · have heq : (A.tube q.1, q.2) = (m, t) := (LowHeightCylinder.injective_heightCylinder d e) he
      have hqt : q.2 = t := congrArg (Prod.snd : M × ℝ → ℝ) heq
      have hnonpos : q.2 ≤ 0 := hq.2.1.2
      rw [hqt] at hnonpos
      exact (not_lt_of_ge hnonpos ht).elim
  · intro hp
    exact unrounded_subset A hp

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
