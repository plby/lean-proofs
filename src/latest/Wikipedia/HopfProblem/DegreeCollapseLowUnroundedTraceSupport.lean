import Wikipedia.HopfProblem.DegreeCollapseLowUnroundedTraceFrame

/-!

# Original end and retained regions of the low-dimensional ambient attachment

The original upper end is embedded with its original stabilized columns.
A uniform height neighborhood avoids the handle. Outside any region containing
the attaching tube the entire original cylinder also misses the handle.
These are exact statements about the actual ambient union before rounding.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.UnroundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

theorem cylinder_mem_handle_iff (q : Cylinder A) :
    cylinderMap A q ∈ range (handleMap A) ↔
      ∃ s : NoExoticSixSphere.Sphere d, ∃ v : closedBall (0 : Vector (7 - d)) (handleRadius A),
        A.tube (s, v.val) = q.1 ∧ q.2.val = 0 := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨s, _, hm, ht⟩ :=
      (intersection_iff A p.1.property (handle_vector_mem A p) q.1 q.2.property).mp hp
    exact ⟨s, p.2, hm, ht⟩
  · rintro ⟨s, v, hm, ht⟩
    refine ⟨(⟨s.val, sphere_subset_closedBall s.property⟩, v), ?_⟩
    change A.map (s.val, v.val) = LowHeightCylinder.heightCylinder d e (q.1, q.2.val)
    rw [A.map_boundary s v.val
      ((closedBall_subset_closedBall (handleRadius_lt A).le) v.property), ht, ← hm,
      LowHeightCylinder.heightCylinder_zero]

def retainedRegion : Set (ambientSet A) :=
  Subtype.val ⁻¹' (range (handleMap A))ᶜ

theorem isOpen_retainedRegion : IsOpen (retainedRegion A) :=
  (isCompact_range (handleMap A).continuous).isClosed.isOpen_compl.preimage
    continuous_subtype_val

theorem retainedRegion_mem_cylinder {p : ambientSet A} (hp : p ∈ retainedRegion A) :
    p.val ∈ range (cylinderMap A) := p.property.resolve_right hp

theorem ambientSet_outside_handle :
    ambientSet A \ range (handleMap A) =
      range (cylinderMap A) \ range (handleMap A) := by
  ext y
  simp only [ambientSet, mem_sdiff, mem_union]
  tauto

def originalEnd : C(M, ambientSet A) where
  toFun m := ⟨LowHeightCylinder.heightCylinder d e (m, height A),
    Or.inl ⟨(m, ⟨height A, (height_pos A).le, le_rfl⟩), rfl⟩⟩
  continuous_toFun :=
    ((LowHeightCylinder.continuous_heightCylinder d e).comp
      (continuous_id.prodMk continuous_const)).subtype_mk _

theorem closedEmbedding_originalEnd : IsClosedEmbedding (originalEnd A) := by
  apply (originalEnd A).continuous.isClosedEmbedding
  intro m n h
  have hp : (m, height A) = (n, height A) :=
    LowHeightCylinder.injective_heightCylinder d e (congrArg Subtype.val h)
  exact congrArg Prod.fst hp

theorem originalEnd_mem_retainedRegion (m : M) : originalEnd A m ∈ retainedRegion A := by
  intro h
  obtain ⟨_, _, _, ht⟩ :=
    (cylinder_mem_handle_iff A (m, ⟨height A, (height_pos A).le, le_rfl⟩)).mp h
  exact (ne_of_gt (height_pos A)) ht

theorem originalEnd_columns (m : M) :
    columns A (originalEnd A m) = boundaryFrameOperator d (a.orthonormal m).val :=
  columns_cylinder A (m, ⟨height A, (height_pos A).le, le_rfl⟩)

theorem exists_upper_height_neighborhood :
    ∃ δ : ℝ, 0 < δ ∧ δ < height A ∧ ∀ m : M, ∀ t : ℝ, ‖t‖ ≤ δ →
      LowHeightCylinder.heightCylinder d e (m, height A + t) ∉ range (handleMap A) := by
  let F : M × ℝ → Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
    fun p ↦ LowHeightCylinder.heightCylinder d e (p.1, height A + p.2)
  have hF : Continuous F := (LowHeightCylinder.continuous_heightCylinder d e).comp
    (continuous_fst.prodMk (continuous_const.add continuous_snd))
  have hU : IsOpen (F ⁻¹' (range (handleMap A))ᶜ) :=
    (isCompact_range (handleMap A).continuous).isClosed.isOpen_compl.preimage hF
  have hcore (m : M) : (m, (0 : ℝ)) ∈ F ⁻¹' (range (handleMap A))ᶜ := by
    change LowHeightCylinder.heightCylinder d e (m, height A + 0) ∉ range (handleMap A)
    rw [add_zero]
    exact originalEnd_mem_retainedRegion A m
  obtain ⟨ε, hε, hεU⟩ := exists_uniform_closedProductTube hU hcore
  refine ⟨min ε (height A / 2), lt_min hε (half_pos (height_pos A)),
    (min_le_right _ _).trans_lt (half_lt_self (height_pos A)), ?_⟩
  intro m t ht
  exact hεU m t (ht.trans (min_le_left _ _))

theorem cylinder_outside_tube_region {O : Set M}
    (htube : ∀ s : NoExoticSixSphere.Sphere d, ∀ v ∈ closedBall (0 : Vector (7 - d)) A.radius,
      A.tube (s, v) ∈ O) (q : Cylinder A) (hq : q.1 ∉ O) :
    cylinderMap A q ∉ range (handleMap A) := by
  intro h
  obtain ⟨s, v, hm, _⟩ := (cylinder_mem_handle_iff A q).mp h
  apply hq
  rw [← hm]
  exact htube s v.val ((closedBall_subset_closedBall (handleRadius_lt A).le) v.property)

theorem cylinder_outside_region_retained {O : Set M}
    (htube : ∀ s : NoExoticSixSphere.Sphere d, ∀ v ∈ closedBall (0 : Vector (7 - d)) A.radius,
      A.tube (s, v) ∈ O) (q : Cylinder A) (hq : q.1 ∉ O) :
    (⟨cylinderMap A q, Or.inl ⟨q, rfl⟩⟩ : ambientSet A) ∈ retainedRegion A :=
  cylinder_outside_tube_region A htube q hq

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.UnroundedTrace
