import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryRegularTime

/-!

# An unchanged smooth neighborhood of the original zero seam

Below half the positive tube margin, the original manifold lies in the
retained exterior. Its native surgery map is an open smooth embedding and
a diffeomorphism onto its image. The original time, actual ambient point,
and the full signed induced frame are all retained exactly.
-/

noncomputable section

open Function Set Metric Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery

open NoExoticSixSphere GLOrthonormalization RoundedTrace SurgeryPair

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] [IsManifold (𝓡 7) ∞ M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)
  (hR : A.radius = 2) (T : TimeData A)

def retainedTimeBand : Opens M :=
  ⟨{p | T.time p < T.margin / 2}, isOpen_lt T.smooth.continuous continuous_const⟩

omit [CompactSpace M] [IsManifold (𝓡 7) ∞ M] in
theorem zero_mem_retainedTimeBand {p : M} (hp : T.time p = 0) :
    p ∈ retainedTimeBand A T := by
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

omit [IsManifold (𝓡 7) ∞ M] in
theorem isOpenEmbedding_retainedTimePoint : IsOpenEmbedding (retainedTimePoint A T) :=
  IsOpenEmbedding.of_comp (retainedTimePoint A T)
    (retainedExterior A).isOpen.isOpenEmbedding_subtypeVal
    (retainedTimeBand A T).isOpen.isOpenEmbedding_subtypeVal

def retainedTimeMap : retainedTimeBand A T → otherBoundaryPart A :=
  exteriorMap A ∘ retainedTimePoint A T

theorem isOpenEmbedding_retainedTimeMap : IsOpenEmbedding (retainedTimeMap A T) :=
  (isOpenEmbedding_exteriorMap A).comp (isOpenEmbedding_retainedTimePoint A T)

theorem isLocalDiffeomorphAt_exteriorMap (m : retainedExterior A) :
    letI := boundaryChartedSpace A;
    IsLocalDiffeomorphAt (𝓡 7) (𝓡 7) ∞ (exteriorMap A) m := by
  let := boundaryChartedSpace A
  have hd : IsLocalDiffeomorphAt (𝓡 7) (𝓡 7) ∞ (exteriorNativeDiffeomorph A) m :=
    ⟨(exteriorNativeDiffeomorph A).toPartialDiffeomorph, mem_univ m, Set.eqOn_refl _ _⟩
  exact hd.comp (𝓡 7) (otherBoundaryPart A)
    (isLocalDiffeomorphAt_openSubset_val (I := 𝓡 7) (nativeExteriorPart A)
      (exteriorNativeDiffeomorph A m))

theorem isLocalDiffeomorphAt_retainedTimeMap (p : retainedTimeBand A T) :
    letI := boundaryChartedSpace A;
    IsLocalDiffeomorphAt (𝓡 7) (𝓡 7) ∞ (retainedTimeMap A T) p := by
  let := boundaryChartedSpace A
  have hi : IsLocalDiffeomorphAt (𝓡 7) (𝓡 7) ∞ (retainedTimePoint A T) p :=
    isLocalDiffeomorphAt_codRestrict (retainedExterior A)
      (fun q ↦ (retainedTimePoint A T q).property)
      (isLocalDiffeomorphAt_openSubset_val (I := 𝓡 7) (retainedTimeBand A T) p)
  exact hi.comp (𝓡 7) (otherBoundaryPart A) (isLocalDiffeomorphAt_exteriorMap A _)

def retainedTimeImage : Opens (otherBoundaryPart A) :=
  ⟨range (retainedTimeMap A T), (isOpenEmbedding_retainedTimeMap A T).isOpen_range⟩

def retainedTimeDiffeomorph : letI := boundaryChartedSpace A;
    retainedTimeBand A T ≃ₘ⟮𝓡 7, 𝓡 7⟯ retainedTimeImage A T := by
  let := boundaryChartedSpace A
  let g : retainedTimeBand A T → retainedTimeImage A T :=
    fun p ↦ ⟨retainedTimeMap A T p, mem_range_self p⟩
  apply IsLocalDiffeomorph.diffeomorphOfBijective (f := g)
  · intro p
    exact isLocalDiffeomorphAt_codRestrict (retainedTimeImage A T)
      (fun q ↦ mem_range_self q) (isLocalDiffeomorphAt_retainedTimeMap A T p)
  · constructor
    · intro p q he
      have hv : retainedTimeMap A T p = retainedTimeMap A T q :=
        congrArg (fun z : retainedTimeImage A T ↦ z.val) he
      exact (isOpenEmbedding_retainedTimeMap A T).injective hv
    · rintro ⟨p, q, rfl⟩
      exact ⟨q, rfl⟩

theorem retainedTimeDiffeomorph_point (p : retainedTimeBand A T) :
    letI := boundaryChartedSpace A;
    (retainedTimeDiffeomorph A T p).val = retainedTimeMap A T p := rfl

theorem timeFunction_retainedTimeMap (p : retainedTimeBand A T) :
    timeFunction A hR T (retainedTimeMap A T p) = T.time p.val := by
  rw [retainedTimeMap, Function.comp_apply, timeFunction_exteriorMap]
  exact SurgeryTimeProfile.profile_eq_self T.margin_pos p.property.le

theorem ambient_retainedTimeMap (p : retainedTimeBand A T) :
    (retainedTimeMap A T p).val.val.val =
      LowHeightCylinder.heightCylinder d e (p.val, 0) := rfl

theorem inducedBoundaryFrame_retainedTimeMap (p : retainedTimeBand A T) :
    letI := boundaryChartedSpace A;
    inducedBoundaryFrame A (retainedTimeMap A T p).val =
      OrthogonalFrameAppend.operator (boundaryFrameOperator d (a.orthonormal p.val).val)
        (-heightUnit d e.ambientDimension) := by
  let := boundaryChartedSpace A
  exact inducedBoundaryFrame_exteriorNative A (retainedTimePoint A T p)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery
