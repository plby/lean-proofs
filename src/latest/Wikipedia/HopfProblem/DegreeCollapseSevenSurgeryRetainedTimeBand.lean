import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryRegularTime
import Wikipedia.HopfProblem.DegreeCollapseSevenUnitSurgeryNormalFraming

/-!
# The actual surgery retains an open neighborhood of the entire zero seam

Below half the positive attachment margin, the original manifold lies in
the retained exterior. Its actual map into the canonical surgery is an
open smooth embedding and a diffeomorphism onto its image. The time value,
ambient point, and full induced normal-frame formula are retained exactly.
-/

noncomputable section

open Function Set Metric Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization RoundedTrace StabilizedSpanningDisk
open Wikipedia.SmoothSixDPoincare

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

def retainedTimeBand : Opens M :=
  ⟨{p | T.time p < T.margin / 2}, isOpen_lt T.smooth.continuous continuous_const⟩

theorem zero_mem_retainedTimeBand {p : M} (hp : T.time p = 0) : p ∈ retainedTimeBand A T := by
  change T.time p < T.margin / 2
  rw [hp]
  exact half_pos T.margin_pos

def retainedTimePoint (p : retainedTimeBand A T) : retainedExterior A :=
  ⟨p.val, by
    rintro ⟨⟨s, v⟩, hv, he⟩
    have h := T.tube_time s v ((closedBall_subset_closedBall (outerRadius_lt A).le) hv.2)
    rw [he] at h
    have hp : T.time p.val < T.margin / 2 := p.property
    linarith [T.margin_pos]⟩

theorem isOpenEmbedding_retainedTimePoint : IsOpenEmbedding (retainedTimePoint A T) :=
  IsOpenEmbedding.of_comp (retainedTimePoint A T)
    (retainedExterior A).isOpen.isOpenEmbedding_subtypeVal
    (retainedTimeBand A T).isOpen.isOpenEmbedding_subtypeVal

def retainedTimeMap : retainedTimeBand A T → Target A hR :=
  exteriorMap A hR ∘ retainedTimePoint A T

theorem isOpenEmbedding_retainedTimeMap : IsOpenEmbedding (retainedTimeMap A hR T) := by
  have he : IsOpenEmbedding (exteriorPoint A hR) :=
    IsOpenEmbedding.of_comp (exteriorPoint A hR)
      (OldPatch A hR).isOpen.isOpenEmbedding_subtypeVal
      (retainedExterior A).isOpen.isOpenEmbedding_subtypeVal
  exact (FramedSurgery.oldMap_isOpenEmbedding (E := Vector 4) (face A hR) 3).comp
    (he.comp (isOpenEmbedding_retainedTimePoint A T))

theorem isLocalDiffeomorphAt_retainedTimeMap (p : retainedTimeBand A T) :
    letI := targetChartedSpace A hR;
    IsLocalDiffeomorphAt (𝓡 7) (𝓡 7) ∞ (retainedTimeMap A hR T) p := by
  let := targetChartedSpace A hR
  have hi : IsLocalDiffeomorphAt (𝓡 7) (𝓡 7) ∞ (retainedTimePoint A T) p :=
    isLocalDiffeomorphAt_codRestrict (retainedExterior A)
      (fun q ↦ (retainedTimePoint A T q).property)
      (isLocalDiffeomorphAt_openSubset_val (I := 𝓡 7) (retainedTimeBand A T) p)
  exact hi.comp (𝓡 7) (Target A hR) (isLocalDiffeomorphAt_exteriorMap A hR _)

def retainedTimeImage : Opens (Target A hR) :=
  ⟨range (retainedTimeMap A hR T), (isOpenEmbedding_retainedTimeMap A hR T).isOpen_range⟩

def retainedTimeDiffeomorph : letI := targetChartedSpace A hR;
    retainedTimeBand A T ≃ₘ⟮𝓡 7, 𝓡 7⟯ retainedTimeImage A hR T := by
  let := targetChartedSpace A hR
  let g : retainedTimeBand A T → retainedTimeImage A hR T :=
    fun p ↦ ⟨retainedTimeMap A hR T p, mem_range_self p⟩
  apply IsLocalDiffeomorph.diffeomorphOfBijective (f := g)
  · intro p
    exact isLocalDiffeomorphAt_codRestrict (retainedTimeImage A hR T)
      (fun q ↦ mem_range_self q) (isLocalDiffeomorphAt_retainedTimeMap A hR T p)
  · constructor
    · intro p q he
      exact (isOpenEmbedding_retainedTimeMap A hR T).injective (congrArg Subtype.val he)
    · rintro ⟨p, q, rfl⟩
      exact ⟨q, rfl⟩

theorem retainedTimeDiffeomorph_point (p : retainedTimeBand A T) :
    letI := targetChartedSpace A hR;
    (retainedTimeDiffeomorph A hR T p).val = retainedTimeMap A hR T p := rfl

theorem timeFunction_retainedTimeMap (p : retainedTimeBand A T) :
    timeFunction A hR T (retainedTimeMap A hR T p) = T.time p.val :=
  SurgeryTimeProfile.profile_eq_self T.margin_pos p.property.le

theorem ambientMap_retainedTimeMap (p : retainedTimeBand A T) :
    ambientMap A hR (retainedTimeMap A hR T p) = HeightCylinder.heightCylinder e (p.val, 0) :=
  ambientMap_exterior A hR (retainedTimePoint A T p)

theorem inducedNormalFrame_retainedTimeMap (p : retainedTimeBand A T) :
    inducedNormalFrame A hR (retainedTimeMap A hR T p) = OrthogonalFrameAppend.operator
      (boundaryFrameOperator (a.orthonormal p.val).val) (-heightUnit e.ambientDimension) :=
  inducedNormalFrame_exterior A hR (retainedTimePoint A T p)

theorem compactSpace_positiveHalf : CompactSpace (PositiveHalf A hR T) := by
  let := targetChartedSpace A hR
  let := compactSpace_target A hR
  exact isCompact_iff_compactSpace.mp
    (isClosed_le continuous_const (contMDiff_timeFunction A hR T).continuous).isCompact

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
