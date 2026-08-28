import Wikipedia.HopfProblem.DegreeCollapseSevenRoundedSurgeryTrace

/-!
# The rounded attachment retains the original cylinder away from its support

The altered ambient set is compact. The original upper end has a uniform
height neighborhood disjoint from it. If the attaching tube lies in an open
region, every original cylinder point outside that region also avoids the
altered set. No boundary atlas is asserted by these set-level identifications.
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

def alteredSet : Set (Vector (e.ambientDimension + 6)) :=
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
    HeightCylinder.heightCylinder e (m, t) ∉ A.collarSheet '' addedParameters A := by
  rintro ⟨q, hq, he⟩
  have hp : (A.tube q.1, q.2) = (m, t) := HeightCylinder.injective_heightCylinder e he
  have hqt : q.2 = t := congrArg Prod.snd hp
  exact (not_lt_of_ge (hqt ▸ hq.2.1.2)) ht

theorem addedImage_in_tube_region {O : Set M}
    (htube : ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) A.radius,
      A.tube (s, v) ∈ O) {y : Vector (e.ambientDimension + 6)}
    (hy : y ∈ A.collarSheet '' addedParameters A) :
    ∃ m ∈ O, ∃ t ∈ Icc (-2 * (bump A).rOut) 0,
      HeightCylinder.heightCylinder e (m, t) = y := by
  obtain ⟨q, hq, rfl⟩ := hy
  refine ⟨A.tube q.1, ?_, q.2, hq.2.1, rfl⟩
  exact htube q.1.1 q.1.2 ((closedBall_subset_closedBall (outerRadius_lt A).le) hq.1)

theorem cylinder_outside_tube_region {O : Set M}
    (htube : ∀ s : Sphere 3, ∀ v ∈ closedBall (0 : Vector 4) A.radius,
      A.tube (s, v) ∈ O) (q : UnroundedTrace.Cylinder A) (hq : q.1 ∉ O) :
    UnroundedTrace.cylinderMap A q ∉ alteredSet A := by
  rintro (hh | ha)
  · exact UnroundedTrace.cylinder_outside_tube_region A htube q hq hh
  · obtain ⟨m, hm, t, _, he⟩ := addedImage_in_tube_region A htube ha
    have hp : (m, t) = (q.1, q.2.val) := HeightCylinder.injective_heightCylinder e he
    exact hq ((congrArg Prod.fst hp) ▸ hm)

def originalEnd : C(M, ambientSet A) where
  toFun m := ⟨HeightCylinder.heightCylinder e (m, UnroundedTrace.height A),
    unrounded_subset A (UnroundedTrace.originalEnd A m).property⟩
  continuous_toFun :=
    ((HeightCylinder.continuous_heightCylinder e).comp
      (continuous_id.prodMk continuous_const)).subtype_mk _

theorem closedEmbedding_originalEnd : IsClosedEmbedding (originalEnd A) := by
  apply (originalEnd A).continuous.isClosedEmbedding
  intro m n h
  have hp : (m, UnroundedTrace.height A) = (n, UnroundedTrace.height A) :=
    HeightCylinder.injective_heightCylinder e (congrArg Subtype.val h)
  exact congrArg Prod.fst hp

theorem originalEnd_mem_retainedRegion (m : M) : originalEnd A m ∈ retainedRegion A := by
  rintro (hh | ha)
  · exact UnroundedTrace.originalEnd_mem_retainedRegion A m hh
  · exact heightCylinder_not_mem_added_of_pos A m (UnroundedTrace.height_pos A) ha

theorem exists_upper_height_neighborhood :
    ∃ δ : ℝ, 0 < δ ∧ δ < UnroundedTrace.height A ∧ ∀ m : M, ∀ t : ℝ, ‖t‖ ≤ δ →
      HeightCylinder.heightCylinder e (m, UnroundedTrace.height A + t) ∉ alteredSet A := by
  obtain ⟨δ, hδ, hδH, hδavoid⟩ := UnroundedTrace.exists_upper_height_neighborhood A
  refine ⟨δ, hδ, hδH, ?_⟩
  intro m t ht
  rintro (hh | ha)
  · exact hδavoid m t ht hh
  · have htlo : -δ ≤ t := (abs_le.mp (by simpa only [Real.norm_eq_abs] using ht)).1
    exact heightCylinder_not_mem_added_of_pos A m (by linarith) ha

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.RoundedTrace
