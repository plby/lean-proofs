import StackExchange.Puzzling139335.RectangularHull.AnchoredBands
import StackExchange.Puzzling139335.RectangularHull.Congruence
import StackExchange.Puzzling139335.RectangularHull.DistinctHulls
import StackExchange.Puzzling139335.RectangularHull.MixedBands

/-!
# The two opposite cornered bands

If all four actual rectangular hulls have common side lengths `1,h`, with
`0 < h < 1`, exactly two pieces contain square corners. Their hulls are
opposite side bands. This uses the rectangular-hull classification and
the Jordan-region exclusions for equal or perpendicular band hulls.
-/

open Set

namespace Puzzling139335.RectangularHull

/-- Distinct pieces have distinct actual convex hulls. -/
theorem CommonFrames.piece_hull_injective {d : SquareDissection} (F : CommonFrames d) :
    Function.Injective (fun i => convexHull ℝ (d.piece i)) := by
  intro i j hij
  by_contra hne
  apply squareDissection_distinct_rectangular_hulls d hne (F.frame i) (F.hull_eq i)
  exact hij.symm.trans (F.hull_eq i)

/-- Classify a corner-bearing piece using its actual rectangular convex hull. -/
theorem CommonFrames.exists_sideBand_of_corner {d : SquareDissection}
    (F : CommonFrames d) {h : ℝ}
    (hfirst : ∀ i, ‖(F.frame i).first‖ = 1)
    (hsecond : ∀ i, ‖(F.frame i).second‖ = h)
    {i q : Fin 4} (hq : corner q ∈ d.piece i) :
    ∃ s : Fin 4, convexHull ℝ (d.piece i) = sideBand h s := by
  have hS : (F.frame i).carrier ⊆ unitSquare := by
    rw [← F.hull_eq i]
    exact convexHull_min (d.piece_subset i) convex_unitSquare
  have hqH := (F.frame i).subset_carrier_of_convexHull_eq (F.hull_eq i) hq
  obtain ⟨s, hs⟩ := (F.frame i).exists_sideBand_of_corner hS (hfirst i) (hsecond i) hqH
  exact ⟨s, (F.hull_eq i).trans hs⟩

/-- A band thinner than the square cannot contain both of these diagonal corners. -/
theorem sideBand_not_both_diagonal_corners {h : ℝ} (hh1 : h < 1) (s : Fin 4) :
    ¬ (corner 0 ∈ sideBand h s ∧ corner 2 ∈ sideBand h s) := by
  rintro ⟨hzero, htwo⟩
  change !₂[(0 : ℝ), 0] ∈ sideBand h s at hzero
  change !₂[(1 : ℝ), 1] ∈ sideBand h s at htwo
  fin_cases s
  all_goals norm_num [sideBand, closedAxisBox] at hzero htwo
  all_goals linarith

/-- Distinct pieces whose hulls are side bands must occupy opposite sides. -/
theorem CommonFrames.sideBand_eq_opposite_of_ne {d : SquareDissection}
    (F : CommonFrames d) {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    {i j s t : Fin 4} (hij : i ≠ j)
    (hi : convexHull ℝ (d.piece i) = sideBand h s)
    (hj : convexHull ℝ (d.piece j) = sideBand h t) : t = s + 2 := by
  rcases sideBand_hulls_same_or_opposite (d.jordan i) (d.jordan j)
    (d.disjoint_interiors hij) hh0 hh1 hi hj with hsame | hopp
  · rw [hsame] at hj
    exact (hij (F.piece_hull_injective (hi.trans hj.symm))).elim
  · exact hopp

/-- Exactly two pieces contain corners; their actual hulls are opposite bands. -/
theorem CommonFrames.exists_opposite_cornered_bands {d : SquareDissection}
    (F : CommonFrames d) {h : ℝ} (hh0 : 0 < h) (hh1 : h < 1)
    (hfirst : ∀ i, ‖(F.frame i).first‖ = 1)
    (hsecond : ∀ i, ‖(F.frame i).second‖ = h) :
    ∃ i j s : Fin 4, i ≠ j ∧
      convexHull ℝ (d.piece i) = sideBand h s ∧
      convexHull ℝ (d.piece j) = sideBand h (s + 2) ∧
      ∀ k, k ≠ i → k ≠ j → ∀ q, corner q ∉ d.piece k := by
  obtain ⟨i, hi⟩ := d.exists_piece_mem (corner_mem_unitSquare 0)
  obtain ⟨j, hj⟩ := d.exists_piece_mem (corner_mem_unitSquare 2)
  obtain ⟨s, his⟩ := F.exists_sideBand_of_corner hfirst hsecond hi
  obtain ⟨t, hjt⟩ := F.exists_sideBand_of_corner hfirst hsecond hj
  have hij : i ≠ j := by
    intro heq
    apply sideBand_not_both_diagonal_corners hh1 s
    constructor
    · rw [← his]
      exact subset_convexHull ℝ (d.piece i) hi
    · rw [← his, heq]
      exact subset_convexHull ℝ (d.piece j) hj
  have ht := F.sideBand_eq_opposite_of_ne hh0 hh1 hij his hjt
  rw [ht] at hjt
  refine ⟨i, j, s, hij, his, hjt, ?_⟩
  intro k hki hkj q hq
  obtain ⟨u, hku⟩ := F.exists_sideBand_of_corner hfirst hsecond hq
  have hu := F.sideBand_eq_opposite_of_ne hh0 hh1 hki.symm his hku
  rw [hu] at hku
  exact hkj (F.piece_hull_injective (hku.trans hjt.symm))

end Puzzling139335.RectangularHull
