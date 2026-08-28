import Wikipedia.SmoothSixDPoincare.FramedSurgeryClosedNewEmbedding

/-!
# The actual closed common exterior of framed surgery

Remove the interior of the original full attaching face. The remaining
closed exterior includes the common corner and maps into both boundary
presentations with its original point coordinates.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)

def faceInterior : Set X := A.chart '' ((univ : Set (UnitSphere E)) ×ˢ ball (0 : F) 1)

omit [FiniteDimensional ℝ E] [T2Space X] in
theorem isOpen_faceInterior : IsOpen (faceInterior A) := by
  apply A.chart.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_ball)
  exact fun _ hz => A.source ⟨hz.1, ball_subset_closedBall hz.2⟩

omit [FiniteDimensional ℝ E] [T2Space X] in
theorem face_mem_interior_iff (u : UnitSphere E) (v : MorseHandle.UnitDisk F) :
    A.map (u, v) ∈ faceInterior A ↔ ‖v.val‖ < 1 := by
  constructor
  · rintro ⟨⟨u', v'⟩, ⟨_, hv'⟩, he⟩
    have hsource : (u', v') ∈ A.chart.source :=
      A.source ⟨mem_univ _, ball_subset_closedBall hv'⟩
    have hsource' : (u, v.val) ∈ A.chart.source := A.source ⟨mem_univ _, v.property⟩
    have hp := A.chart.injOn hsource hsource' (he.trans (A.point u v).symm)
    have hval : v' = v.val := congrArg (fun p : UnitSphere E × F => p.2) hp
    rw [← hval]
    exact mem_ball_zero_iff.mp hv'
  · intro hv
    exact ⟨(u, v.val), ⟨mem_univ _, mem_ball_zero_iff.mpr hv⟩, A.point u v⟩

omit [FiniteDimensional ℝ E] [T2Space X] in
theorem core_subset_faceInterior : range (coreMap A) ⊆ faceInterior A := by
  rintro x ⟨u, rfl⟩
  exact (face_mem_interior_iff A u ⟨0, by simp⟩).mpr (by norm_num)

abbrev Exterior := {x : X // x ∉ faceInterior A}

def exteriorToOldPatch : C(Exterior A, oldPatch A) :=
  ⟨fun x => ⟨x.val, fun hx => x.property (core_subset_faceInterior A hx)⟩,
    continuous_subtype_val.subtype_mk _⟩

def exteriorOldMap : C(Exterior A, X) := ⟨Subtype.val, continuous_subtype_val⟩

omit [FiniteDimensional ℝ E] [T2Space X] in
theorem exteriorOldMap_isClosedEmbedding : IsClosedEmbedding (exteriorOldMap A) :=
  (isOpen_faceInterior A).isClosed_compl.isClosedEmbedding_subtypeVal

def exteriorCorner (q : UnitSphere E × UnitSphere F) : Exterior A :=
  ⟨A.map (q.1, ⟨q.2.val, sphere_subset_closedBall q.2.property⟩), by
    intro h
    have hn := (face_mem_interior_iff A q.1
      ⟨q.2.val, sphere_subset_closedBall q.2.property⟩).mp h
    rw [mem_sphere_zero_iff_norm.mp q.2.property] at hn
    exact lt_irrefl _ hn⟩

omit [FiniteDimensional ℝ E] [T2Space X] in
theorem exteriorOldMap_corner (q : UnitSphere E × UnitSphere F) :
    exteriorOldMap A (exteriorCorner A q) =
      A.map (q.1, ⟨q.2.val, sphere_subset_closedBall q.2.property⟩) := rfl

variable (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

def exteriorNewMap : C(Exterior A, Boundary A n) :=
  (oldMap A n).comp (exteriorToOldPatch A)

theorem exteriorNewMap_injective : Injective (exteriorNewMap A n) := by
  intro x y h
  have he := (oldMap_isOpenEmbedding A n).injective h
  exact Subtype.ext (congrArg (fun z : oldPatch A => z.val) he)

theorem exteriorNewMap_isClosedEmbedding [CompactSpace X] [FiniteDimensional ℝ F] :
    IsClosedEmbedding (exteriorNewMap A n) := by
  let _ : CompactSpace (Exterior A) :=
    isCompact_iff_compactSpace.mp (isOpen_faceInterior A).isClosed_compl.isCompact
  exact (exteriorNewMap A n).continuous.isClosedEmbedding (exteriorNewMap_injective A n)

theorem exteriorNewMap_corner (q : UnitSphere E × UnitSphere F) :
    exteriorNewMap A n (exteriorCorner A q) =
      closedNewMap A n (⟨q.1.val, sphere_subset_closedBall q.1.property⟩, q.2) :=
  (closedNewMap_corner A n q.1 q.2).symm

end Wikipedia.SmoothSixDPoincare.FramedSurgery
