import Wikipedia.HopfProblem.ThreefoldGluing

/-!
# Properness of the actual glued projection

Proper local maps glue to a proper global map when the local pieces are
the full inverse images of an open cover of the base.  No Hausdorffness
or local compactness of the glued space or of the base is assumed here:
closedness is local on the target, and each fibre is the continuous image
of a compact local fibre.
-/

noncomputable section

open Set Topology TopologicalSpace

universe u

namespace Wikipedia.HopfProblem.ThreefoldGluing.Data

variable {B : Type u} [TopologicalSpace B] (D : ThreefoldGluing.Data B)

/-- The restriction of the global projection is the local map in the
actual patch homeomorphism. -/
theorem restrictedProjection_eq (i : D.J) :
    (D.patch i : Set B).restrictPreimage D.projection =
      D.localProjection i ∘ (D.patchHomeomorph i).symm := by
  funext x
  simpa only [Function.comp_apply, Homeomorph.apply_symm_apply] using
    D.patchHomeomorph_projection i ((D.patchHomeomorph i).symm x)

theorem restrictedProjection_proper (i : D.J) (hi : IsProperMap (D.localProjection i)) :
    IsProperMap ((D.patch i : Set B).restrictPreimage D.projection) := by
  rw [D.restrictedProjection_eq]
  exact hi.comp (D.patchHomeomorph i).symm.isProperMap

/-- A global fibre is exactly the image of the corresponding fibre in
any local piece whose base patch contains the point. -/
theorem projection_fibre_eq_localImage (i : D.J) (b : D.patch i) :
    D.projection ⁻¹' {(b : B)} =
      D.inclusion i '' (D.localProjection i ⁻¹' {b}) := by
  ext x
  constructor
  · intro hx
    change D.projection x = (b : B) at hx
    have hi : x ∈ range (D.inclusion i) := by
      rw [D.inclusion_range]
      change D.projection x ∈ D.patch i
      rw [hx]
      exact b.property
    obtain ⟨z, rfl⟩ := hi
    refine ⟨z, ?_, rfl⟩
    change D.localProjection i z = b
    apply Subtype.ext
    exact (D.projection_inclusion i z).symm.trans hx
  · rintro ⟨z, hz, rfl⟩
    change D.localProjection i z = b at hz
    change D.projection (D.inclusion i z) = (b : B)
    exact (D.projection_inclusion i z).trans (congrArg Subtype.val hz)

/-- Proper local projections have compact global fibres. -/
theorem projection_fibre_compact
    (hproper : ∀ i : D.J, IsProperMap (D.localProjection i)) (b : B) :
    IsCompact (D.projection ⁻¹' {b}) := by
  obtain ⟨i, hi⟩ := D.cover.exists_mem b
  rw [D.projection_fibre_eq_localImage i ⟨b, hi⟩]
  exact ((hproper i).isCompact_preimage isCompact_singleton).image
    (D.inclusion_openEmbedding i).continuous

/-- Properness of all local maps implies properness of the constructed
global projection, without extra separation assumptions. -/
theorem projection_proper (hproper : ∀ i : D.J, IsProperMap (D.localProjection i)) :
    IsProperMap D.projection := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨D.projection_continuous, ?_, D.projection_fibre_compact hproper⟩
  apply D.cover.isClosedMap_iff_restrictPreimage.mpr
  intro i
  exact (D.restrictedProjection_proper i (hproper i)).isClosedMap

/-- Properness is equivalent to properness of every full local projection. -/
theorem projection_proper_iff :
    IsProperMap D.projection ↔ ∀ i : D.J, IsProperMap (D.localProjection i) := by
  constructor
  · intro hp i
    have hi := (hp.restrictPreimage (D.patch i : Set B)).comp
      (D.patchHomeomorph i).isProperMap
    simpa only [Function.comp_def, D.patchHomeomorph_projection] using hi
  · exact D.projection_proper

/-- A compact base and proper local projections give a compact glued space. -/
theorem compactSpace [CompactSpace B]
    (hproper : ∀ i : D.J, IsProperMap (D.localProjection i)) : CompactSpace D.Space := by
  constructor
  simpa only [preimage_univ] using (D.projection_proper hproper).isCompact_preimage
    (isCompact_univ : IsCompact (univ : Set B))

/-- Local surjectivity and the base cover imply global surjectivity. -/
theorem projection_surjective
    (hsurj : ∀ i : D.J, Function.Surjective (D.localProjection i)) :
    Function.Surjective D.projection := by
  intro b
  obtain ⟨i, hi⟩ := D.cover.exists_mem b
  obtain ⟨x, hx⟩ := hsurj i ⟨b, hi⟩
  exact ⟨D.inclusion i x, (D.projection_inclusion i x).trans (congrArg Subtype.val hx)⟩

/-- Since each piece is a full base-patch inverse image, global and local
surjectivity are equivalent as well. -/
theorem projection_surjective_iff :
    Function.Surjective D.projection ↔
      ∀ i : D.J, Function.Surjective (D.localProjection i) := by
  constructor
  · intro hs i b
    obtain ⟨x, hx⟩ := hs b.val
    have hi : x ∈ range (D.inclusion i) := by
      rw [D.inclusion_range]
      change D.projection x ∈ D.patch i
      rw [hx]
      exact b.property
    obtain ⟨z, rfl⟩ := hi
    refine ⟨z, Subtype.ext ?_⟩
    exact (D.projection_inclusion i z).symm.trans hx
  · exact D.projection_surjective

/-- A countable family of second-countable local pieces gives a
second-countable topology on the actual gluing. -/
theorem secondCountableSpace [Countable D.J]
    [∀ i, SecondCountableTopology (D.piece i)] : SecondCountableTopology D.Space := by
  let : ∀ i, SecondCountableTopology (range (D.inclusion i)) := fun i =>
    (D.inclusion_openEmbedding i).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply secondCountableTopology_of_countable_cover
    (U := fun i => range (D.inclusion i)) (fun i => (D.inclusion_openEmbedding i).isOpen_range)
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, y, hy⟩ := D.inclusion_jointly_surjective x
  exact Set.mem_iUnion.mpr ⟨i, y, hy⟩

/-- Over a compact base, second countability of the pieces suffices without
any countability assumption on the indexing type: a finite subcover of
base patches gives a finite open cover of the glued space. -/
theorem secondCountableSpace_of_compactBase [CompactSpace B]
    [∀ i, SecondCountableTopology (D.piece i)] : SecondCountableTopology D.Space := by
  classical
  obtain ⟨s, hs⟩ := D.cover.exists_finite_of_compactSpace
  let : ∀ i : s, SecondCountableTopology (range (D.inclusion i.val)) := fun i =>
    (D.inclusion_openEmbedding i.val).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply secondCountableTopology_of_countable_cover
    (U := fun i : s => range (D.inclusion i.val))
    (fun i => (D.inclusion_openEmbedding i.val).isOpen_range)
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := hs.exists_mem (D.projection x)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  rw [D.inclusion_range]
  exact hi

end Wikipedia.HopfProblem.ThreefoldGluing.Data
