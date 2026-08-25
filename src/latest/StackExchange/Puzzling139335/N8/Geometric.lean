import StackExchange.Puzzling139335.N8.TrianglePacking
import StackExchange.Puzzling139335.N8.SideOwnership
import StackExchange.Puzzling139335.N8.Segments

/-!
# The geometric contradiction from three actual unit pairs

The four pieces have distinct assigned square sides. Accessibility forces
each whole side into its assigned piece. Because all three intrinsic pairs
occur, all three edges of the prototype's triangular hull are actual edges
in the prototype. The Jordan-region filling theorem makes the prototype a
whole triangle. Every placed unit equilateral triangle contains the square
center in its interior, contradicting disjointness of the pieces.
-/

open Set

namespace Puzzling139335.N8

theorem side_assignment_injective_of_equilateral_hulls (d : SquareDissection)
    {s : Fin 4 → Fin 4} (hs : IsSideAssignment d s)
    (hhull : ∀ i, HasEquilateralSideHull (d.piece i) (s i)) :
    Function.Injective s := by
  intro i j hijside
  by_contra hij
  apply no_two_equilateral_side_hull_pieces (d.jordan i) (d.jordan j)
    (d.piece_subset i) (d.piece_subset j) (d.disjoint_interiors hij)
    ((hs i _).mpr (Or.inl rfl)) ((hs i _).mpr (Or.inr rfl))
  · exact (hs j _).mpr (Or.inl hijside)
  · exact (hs j _).mpr (Or.inr (congrArg (fun a : Fin 4 => a + 1) hijside))
  · exact hhull i
  · exact hijside.symm ▸ hhull j

private theorem exists_external_corner_of_ne_sides (a b : Fin 4) (hab : a ≠ b) :
    ∃ c : Fin 4, c ≠ a ∧ c ≠ a + 1 ∧ (c = b ∨ c = b + 1) := by
  fin_cases a <;> fin_cases b
  all_goals first | exact (hab rfl).elim | decide

theorem full_sides_of_injective_side_assignment (d : SquareDissection)
    {s : Fin 4 → Fin 4} (hs : IsSideAssignment d s) (hinj : Function.Injective s)
    (i : Fin 4) : segment ℝ (corner (s i)) (corner (s i + 1)) ⊆ d.piece i := by
  apply d.side_subset_of_other_pieces_have_external_corner i (s i)
    ((hs i _).mpr (Or.inl rfl)) ((hs i _).mpr (Or.inr rfl))
  intro j hji
  obtain ⟨c, hca, hca1, hc⟩ :=
    exists_external_corner_of_ne_sides (s i) (s j) (hinj.ne (Ne.symm hji))
  exact ⟨c, hca, hca1, (hs j c).mpr hc⟩

/-- The geometric endpoint of the eight-incidence proof uses no area or
boundary-measure assumption. All pair occurrences are actual placements. -/
theorem no_dissection_of_three_side_pairs (d : SquareDissection)
    {s : Fin 4 → Fin 4} (hs : IsSideAssignment d s) {a b c : Plane}
    (htypes : d.usedCornerTypes = {a, b, c})
    (hab : UnitPairs.IsUnitSidePair (d.piece 0) a b)
    (hbc : UnitPairs.IsUnitSidePair (d.piece 0) b c)
    (hca : UnitPairs.IsUnitSidePair (d.piece 0) c a)
    (habpair : ∃ i, intrinsicPair d i = {a, b})
    (hbcpair : ∃ i, intrinsicPair d i = {b, c})
    (hcapair : ∃ i, intrinsicPair d i = {c, a}) : False := by
  classical
  have hhull := equilateral_side_hulls_of_three_types d hs htypes hab hbc hca
  have hsideinj := side_assignment_injective_of_equilateral_hulls d hs hhull
  have hfull := full_sides_of_injective_side_assignment d hs hsideinj
  have hsub := UnitPairs.subset_convexHull_of_three_unitSidePairs hab hbc hca
  have hnonzero := UnitPairs.sideDet_ne_zero_of_equidistant
    hab.2.2.1 hbc.2.2.1 hca.2.2.1
  obtain ⟨iab, hiab⟩ := habpair
  obtain ⟨ibc, hibc⟩ := hbcpair
  obtain ⟨ica, hica⟩ := hcapair
  have hwhole : d.piece 0 = convexHull ℝ ({a, b, c} : Set Plane) :=
    eq_triangle_of_three_segments (d.jordan 0) hsub hnonzero
      (intrinsic_segment_subset_of_side_subset d hs iab hiab (hfull iab))
      (intrinsic_segment_subset_of_side_subset d hs ibc hibc (hfull ibc))
      (intrinsic_segment_subset_of_side_subset d hs ica hica (hfull ica))
  have hconvex (i : Fin 4) : Convex ℝ (d.piece i) := by
    rw [← d.placement_image i, hwhole, image_convexHull_triple]
    exact convex_convexHull ℝ _
  have hcenter (i : Fin 4) : squareCenter ∈ interior (d.piece i) := by
    obtain ⟨z, hz, hbz, hza, _⟩ := hhull i
    have htriangle : convexHull ℝ ({corner (s i), corner (s i + 1), z} : Set Plane) ⊆
        d.piece i := by
      apply convexHull_min _ (hconvex i)
      intro p hp
      rcases hp with rfl | rfl | rfl
      · exact (hs i _).mpr (Or.inl rfl)
      · exact (hs i _).mpr (Or.inr rfl)
      · exact hz
    exact interior_mono htriangle
      (squareCenter_mem_interior_triangle_of_adjacent_corners (s i)
        (d.piece_subset i hz) hbz hza)
  exact disjoint_left.mp (d.disjoint_interiors (by decide : (0 : Fin 4) ≠ 1))
    (hcenter 0) (hcenter 1)

end Puzzling139335.N8
