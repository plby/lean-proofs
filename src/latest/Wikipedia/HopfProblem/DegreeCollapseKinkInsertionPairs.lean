import Wikipedia.HopfProblem.DegreeCollapseKinkInsertionFibers

/-!
# Exact global pair control for the inserted native kink

Full recognition of every original fiber in the target chart rules out
unintended intersections with the unchanged part of the original sphere.
The endpoint has precisely the old ordered pairs and the two new orders
of the explicit crossing; this is an equality of actual source-pair sets.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource.KinkPatchData

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization SupportedCusp

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {F : Sphere 3 → M} (P : KinkPatchData F)

theorem coordinates_of_inserted_pair {x y : Sphere 3} (hx : x ∈ P.sourcePatch)
    (he : P.insertedMap x = P.insertedMap y) :
    ∃ u v : Vector 3, x = shiftedSourceChart P.center u ∧
      y = shiftedSourceChart P.center v ∧
      scaledMap P.cutoff P.scale 1 u = scaledMap P.cutoff P.scale 1 v := by
  obtain ⟨u, hu, rfl⟩ := hx
  have huΦ := P.map_source (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) hu
  by_cases hy : y ∈ P.sourcePatch
  · obtain ⟨v, hv, rfl⟩ := hy
    have hvΦ := P.map_source (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1) hv
    rw [P.insertedMap_source hu, P.insertedMap_source hv] at he
    exact ⟨u, v, rfl, rfl, P.chart.injOn huΦ hvΦ he⟩
  · have hyK : y ∉ P.sourceSupport := fun h ↦ hy (P.sourceSupport_subset h)
    rw [P.insertedMap_source hu, P.insertedMap_fixed hyK] at he
    obtain ⟨v, hkv, hyv⟩ := (P.full_fibers _ huΦ y).mp he.symm
    have hvK : v ∉ scaledSupport P.cutoff P.scale := by
      intro hv
      apply hyK
      exact hyv.symm ▸ (show shiftedSourceChart P.center v ∈ P.sourceSupport from ⟨v, hv, rfl⟩)
    refine ⟨u, v, rfl, hyv, ?_⟩
    exact hkv.trans (scaledMap_eq_plane_off_support P.cutoff P.scale_pos.ne' 1 hvK).symm

theorem inserted_pair_at_patch {x y : Sphere 3} (hx : x ∈ P.sourcePatch) (hne : x ≠ y)
    (he : P.insertedMap x = P.insertedMap y) :
    (x = P.crossingPoint 1 ∧ y = P.crossingPoint (-1)) ∨
      (x = P.crossingPoint (-1) ∧ y = P.crossingPoint 1) := by
  obtain ⟨u, v, rfl, rfl, huv⟩ := P.coordinates_of_inserted_pair hx he
  rcases (scaledMap_endpoint_eq_iff P.cutoff P.scale_pos.ne' u v).mp huv with
    huv | ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact (hne (congrArg (shiftedSourceChart P.center) huv)).elim
  · exact Or.inl ⟨congrArg (shiftedSourceChart P.center) hu,
      congrArg (shiftedSourceChart P.center) hv⟩
  · exact Or.inr ⟨congrArg (shiftedSourceChart P.center) hu,
      congrArg (shiftedSourceChart P.center) hv⟩

theorem inserted_pair_iff {x y : Sphere 3} (hne : x ≠ y) :
    P.insertedMap x = P.insertedMap y ↔ F x = F y ∨
      (x = P.crossingPoint 1 ∧ y = P.crossingPoint (-1)) ∨
      (x = P.crossingPoint (-1) ∧ y = P.crossingPoint 1) := by
  constructor
  · intro he
    by_cases hx : x ∈ P.sourcePatch
    · exact Or.inr (P.inserted_pair_at_patch hx hne he)
    by_cases hy : y ∈ P.sourcePatch
    · rcases P.inserted_pair_at_patch hy hne.symm he.symm with h | h
      · exact Or.inr (Or.inr ⟨h.2, h.1⟩)
      · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
    · left
      have hxK : x ∉ P.sourceSupport := fun h ↦ hx (P.sourceSupport_subset h)
      have hyK : y ∉ P.sourceSupport := fun h ↦ hy (P.sourceSupport_subset h)
      rwa [P.insertedMap_fixed hxK, P.insertedMap_fixed hyK] at he
  · rintro (he | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · obtain ⟨hx, hy⟩ := P.original_pair_off_patch hne he
      have hxK : x ∉ P.sourceSupport := fun h ↦ hx (P.sourceSupport_subset h)
      have hyK : y ∉ P.sourceSupport := fun h ↦ hy (P.sourceSupport_subset h)
      rwa [P.insertedMap_fixed hxK, P.insertedMap_fixed hyK]
    · exact P.inserted_crossing
    · exact P.inserted_crossing.symm

theorem inserted_pairs : SphereSelfIntersections.pairs P.insertedMap =
    SphereSelfIntersections.pairs F ∪
      {(P.crossingPoint 1, P.crossingPoint (-1)), (P.crossingPoint (-1), P.crossingPoint 1)} := by
  ext p
  change (p.1 ≠ p.2 ∧ P.insertedMap p.1 = P.insertedMap p.2) ↔
    (p.1 ≠ p.2 ∧ F p.1 = F p.2) ∨
      p ∈ ({(P.crossingPoint 1, P.crossingPoint (-1)),
        (P.crossingPoint (-1), P.crossingPoint 1)} : Set (Sphere 3 × Sphere 3))
  simp only [mem_insert_iff, mem_singleton_iff, Prod.ext_iff]
  constructor
  · rintro ⟨hne, he⟩
    rcases (P.inserted_pair_iff hne).mp he with h | h | h
    · exact Or.inl ⟨hne, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨hne, he⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩)
    · exact ⟨hne, (P.inserted_pair_iff hne).mpr (Or.inl he)⟩
    · exact ⟨fun h ↦ P.crossingPoint_ne (hx.symm.trans (h.trans hy)),
        hx.symm ▸ hy.symm ▸ P.inserted_crossing⟩
    · exact ⟨fun h ↦ P.crossingPoint_ne (hy.symm.trans (h.symm.trans hx)),
        hx.symm ▸ hy.symm ▸ P.inserted_crossing.symm⟩

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource.KinkPatchData
