import StackExchange.Puzzling139335.N8.Pairs

/-!
# Equilateral side hulls from three used intrinsic types

This module transports the prototype's actual triangle containment into
each placement. The apex belongs to the piece, not merely to its hull.
-/

open Set

namespace Puzzling139335.N8

/-- A piece lies in a unit equilateral triangle erected inward on a named
square side, and contains that triangle's apex. -/
def HasEquilateralSideHull (P : Set Plane) (i : Fin 4) : Prop :=
  ∃ z : Plane, z ∈ P ∧
    dist (corner (i + 1)) z = 1 ∧ dist z (corner i) = 1 ∧
    P ⊆ convexHull ℝ ({corner i, corner (i + 1), z} : Set Plane)

theorem image_convexHull_triple (e : Plane ≃ᵃⁱ[ℝ] Plane) (a b c : Plane) :
    e '' convexHull ℝ ({a, b, c} : Set Plane) =
      convexHull ℝ ({e a, e b, e c} : Set Plane) := by
  simpa only [AffineEquiv.coe_coe, AffineIsometryEquiv.coe_toAffineEquiv,
    image_insert_eq, image_singleton] using
    e.toAffineEquiv.toAffineMap.image_convexHull ({a, b, c} : Set Plane)

theorem side_hull_of_source_triangle (d : SquareDissection) (i r : Fin 4)
    {a b c : Plane} (ha : d.placement i a = corner r)
    (hb : d.placement i b = corner (r + 1)) (hc : c ∈ d.piece 0)
    (hbc : dist b c = 1) (hca : dist c a = 1)
    (hsub : d.piece 0 ⊆ convexHull ℝ ({a, b, c} : Set Plane)) :
    HasEquilateralSideHull (d.piece i) r := by
  refine ⟨d.placement i c, ?_, ?_, ?_, ?_⟩
  · rw [← d.placement_image i]
    exact mem_image_of_mem _ hc
  · rw [← hb, (d.placement i).isometry.dist_eq]
    exact hbc
  · rw [← ha, (d.placement i).isometry.dist_eq]
    exact hca
  · rw [← d.placement_image i, ← ha, ← hb, ← image_convexHull_triple]
    exact image_mono hsub

/-- If the three intrinsic types have all three actual unit-side
placements, then every piece has an actual equilateral side hull. -/
theorem equilateral_side_hulls_of_three_types (d : SquareDissection)
    {s : Fin 4 → Fin 4} (hs : IsSideAssignment d s) {a b c : Plane}
    (htypes : d.usedCornerTypes = {a, b, c})
    (hab : UnitPairs.IsUnitSidePair (d.piece 0) a b)
    (hbc : UnitPairs.IsUnitSidePair (d.piece 0) b c)
    (hca : UnitPairs.IsUnitSidePair (d.piece 0) c a)
    (i : Fin 4) : HasEquilateralSideHull (d.piece i) (s i) := by
  classical
  have hsub := UnitPairs.subset_convexHull_of_three_unitSidePairs hab hbc hca
  have hu : d.intrinsicCorner i (s i) = a ∨
      d.intrinsicCorner i (s i) = b ∨ d.intrinsicCorner i (s i) = c := by
    have hmem := d.mem_usedCornerTypes.mpr
      ⟨i, s i, (hs i _).mpr (Or.inl rfl), rfl⟩
    rw [htypes] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  have hv : d.intrinsicCorner i (s i + 1) = a ∨
      d.intrinsicCorner i (s i + 1) = b ∨ d.intrinsicCorner i (s i + 1) = c := by
    have hmem := d.mem_usedCornerTypes.mpr
      ⟨i, s i + 1, (hs i _).mpr (Or.inr rfl), rfl⟩
    rw [htypes] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  have hne := (isUnitSidePair_intrinsic d hs i).ne
  have hgo (u v w : Plane) (hu : d.intrinsicCorner i (s i) = u)
      (hv : d.intrinsicCorner i (s i + 1) = v) (hw : w ∈ d.piece 0)
      (hvw : dist v w = 1) (hwu : dist w u = 1)
      (hset : ({u, v, w} : Set Plane) = {a, b, c}) :
      HasEquilateralSideHull (d.piece i) (s i) := by
    apply side_hull_of_source_triangle d i (s i)
      (a := u) (b := v) (c := w)
    · rw [← hu, d.placement_intrinsicCorner]
    · rw [← hv, d.placement_intrinsicCorner]
    · exact hw
    · exact hvw
    · exact hwu
    · rwa [hset]
  rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv
  · exact (hne (hu.trans hv.symm)).elim
  · exact hgo a b c hu hv hbc.2.1 hbc.2.2.1 hca.2.2.1 rfl
  · apply hgo a c b hu hv hab.2.1
    · simpa only [dist_comm] using hbc.2.2.1
    · simpa only [dist_comm] using hab.2.2.1
    · ext p
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
  · apply hgo b a c hu hv hbc.2.1
    · simpa only [dist_comm] using hca.2.2.1
    · simpa only [dist_comm] using hbc.2.2.1
    · ext p
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
  · exact (hne (hu.trans hv.symm)).elim
  · apply hgo b c a hu hv hab.1 hca.2.2.1 hab.2.2.1
    ext p
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  · apply hgo c a b hu hv hab.2.1 hab.2.2.1 hbc.2.2.1
    ext p
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  · apply hgo c b a hu hv hab.1
    · simpa only [dist_comm] using hab.2.2.1
    · simpa only [dist_comm] using hca.2.2.1
    · ext p
      simp only [mem_insert_iff, mem_singleton_iff]
      tauto
  · exact (hne (hu.trans hv.symm)).elim

end Puzzling139335.N8
