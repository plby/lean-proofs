import Wikipedia.HopfProblem.DegreeCollapseLowRoundedSurgeryTrace

/-!

# Exact support preservation for the actual rounded low-dimensional attachment

The altered ambient set is compact and stays away from a uniform neighborhood
of the original upper end. Original cylinder points outside a region containing
the attaching tube also remain outside the altered set. These statements
retain the actual ambient points, before constructing their smooth atlas.
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

def alteredSet : Set (Vector (e.ambientDimension + (1 + (1 + (d + 1))))) :=
  range (UnroundedTrace.handleMap A) ∪ A.collarSheet '' addedParameters A

theorem isCompact_alteredSet : IsCompact (alteredSet A) :=
  (isCompact_range (UnroundedTrace.handleMap A).continuous).union (isCompact_addedImage A)

theorem ambientSet_eq_cylinder_union_altered :
    ambientSet A = range (UnroundedTrace.cylinderMap A) ∪ alteredSet A :=
  union_assoc _ _ _

def retainedRegion : Set (ambientSet A) := Subtype.val ⁻¹' (alteredSet A)ᶜ

theorem isOpen_retainedRegion : IsOpen (retainedRegion A) :=
  (isCompact_alteredSet A).isClosed.isOpen_compl.preimage continuous_subtype_val

theorem ambientSet_outside_altered :
    ambientSet A \ alteredSet A = range (UnroundedTrace.cylinderMap A) \ alteredSet A := by
  rw [ambientSet_eq_cylinder_union_altered]
  ext y
  simp only [mem_sdiff, mem_union]
  tauto

theorem heightCylinder_not_mem_added_of_pos (m : M) {t : ℝ} (ht : 0 < t) :
    LowHeightCylinder.heightCylinder d e (m, t) ∉ A.collarSheet '' addedParameters A := by
  rintro ⟨q, hq, he⟩
  have hp : (A.tube q.1, q.2) = (m, t) := LowHeightCylinder.injective_heightCylinder d e he
  have hqt : q.2 = t := congrArg Prod.snd hp
  exact (not_lt_of_ge (hqt ▸ hq.2.1.2)) ht

theorem addedImage_in_tube_region {O : Set M}
    (htube : ∀ s : NoExoticSixSphere.Sphere d, ∀ v ∈ closedBall (0 : Vector (7 - d)) A.radius,
      A.tube (s, v) ∈ O) {y : Vector (e.ambientDimension + (1 + (1 + (d + 1))))}
    (hy : y ∈ A.collarSheet '' addedParameters A) :
    ∃ m ∈ O, ∃ t ∈ Icc (-2 * (bump A).rOut) 0,
      LowHeightCylinder.heightCylinder d e (m, t) = y := by
  obtain ⟨q, hq, rfl⟩ := hy
  refine ⟨A.tube q.1, ?_, q.2, hq.2.1, rfl⟩
  exact htube q.1.1 q.1.2 ((closedBall_subset_closedBall (outerRadius_lt A).le) hq.1)

theorem cylinder_outside_tube_region {O : Set M}
    (htube : ∀ s : NoExoticSixSphere.Sphere d, ∀ v ∈ closedBall (0 : Vector (7 - d)) A.radius,
      A.tube (s, v) ∈ O) (q : UnroundedTrace.Cylinder A) (hq : q.1 ∉ O) :
    UnroundedTrace.cylinderMap A q ∉ alteredSet A := by
  rintro (hh | ha)
  · exact UnroundedTrace.cylinder_outside_tube_region A htube q hq hh
  · obtain ⟨m, hm, t, _, he⟩ := addedImage_in_tube_region A htube ha
    have hp : (m, t) = (q.1, q.2.val) := LowHeightCylinder.injective_heightCylinder d e he
    exact hq ((congrArg Prod.fst hp) ▸ hm)

def originalEnd : C(M, ambientSet A) where
  toFun m := ⟨LowHeightCylinder.heightCylinder d e (m, UnroundedTrace.height A),
    unrounded_subset A (UnroundedTrace.originalEnd A m).property⟩
  continuous_toFun :=
    ((LowHeightCylinder.continuous_heightCylinder d e).comp
      (continuous_id.prodMk continuous_const)).subtype_mk _

theorem closedEmbedding_originalEnd : IsClosedEmbedding (originalEnd A) := by
  apply (originalEnd A).continuous.isClosedEmbedding
  intro m n h
  have hp : (m, UnroundedTrace.height A) = (n, UnroundedTrace.height A) :=
    LowHeightCylinder.injective_heightCylinder d e (congrArg Subtype.val h)
  exact congrArg Prod.fst hp

theorem originalEnd_mem_retainedRegion (m : M) : originalEnd A m ∈ retainedRegion A := by
  rintro (hh | ha)
  · exact UnroundedTrace.originalEnd_mem_retainedRegion A m hh
  · exact heightCylinder_not_mem_added_of_pos A m (UnroundedTrace.height_pos A) ha

theorem exists_upper_height_neighborhood :
    ∃ δ : ℝ, 0 < δ ∧ δ < UnroundedTrace.height A ∧ ∀ m : M, ∀ t : ℝ, ‖t‖ ≤ δ →
      LowHeightCylinder.heightCylinder d e (m, UnroundedTrace.height A + t) ∉ alteredSet A := by
  obtain ⟨δ, hδ, hδH, hδavoid⟩ := UnroundedTrace.exists_upper_height_neighborhood A
  refine ⟨δ, hδ, hδH, ?_⟩
  intro m t ht
  rintro (hh | ha)
  · exact hδavoid m t ht hh
  · have htlo : -δ ≤ t := (abs_le.mp (by simpa only [Real.norm_eq_abs] using ht)).1
    exact heightCylinder_not_mem_added_of_pos A m (by linarith) ha

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
