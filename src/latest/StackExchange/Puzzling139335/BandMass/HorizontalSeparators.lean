import StackExchange.Puzzling139335.BandMass.QuarterHeights

/-!
# Horizontal separators give partitions at quarter heights

A connected interior avoiding one horizontal line lies entirely on one side
of that line.  Regular closedness extends this to the whole piece.  Thus a
line crossing no piece interior separates the pieces into two band packings,
and the weighted-mass argument determines its height.
-/

open Set

namespace Puzzling139335

/-- A Jordan region in the square whose interior avoids height `y` is
contained in one of the two closed bands determined by that height. -/
theorem IsJordanRegion.subset_horizontalBand_or_of_avoids_height
    {P : Set Plane} (hP : IsJordanRegion P) (hsub : P ⊆ unitSquare) {y : ℝ}
    (havoid : ∀ p ∈ interior P, p 1 ≠ y) :
    P ⊆ horizontalBand 0 y ∨ P ⊆ horizontalBand y 1 := by
  rcases hP.isConnected_interior.isPreconnected.mapsTo_Ioi_or_Iio
    (PiLp.continuous_apply 2 _ 1).continuousOn havoid with habove | hbelow
  · right
    rw [← hP.closure_interior]
    apply closure_minimal ?_ (isClosed_horizontalBand y 1)
    intro p hp
    have hpS := hsub (interior_subset hp)
    exact ⟨hpS.1, (habove hp).le, hpS.2.2⟩
  · left
    rw [← hP.closure_interior]
    apply closure_minimal ?_ (isClosed_horizontalBand 0 y)
    intro p hp
    have hpS := hsub (interior_subset hp)
    exact ⟨hpS.1, hpS.2.1, (hbelow hp).le⟩

/-- Avoidance of a horizontal line by every piece interior partitions the
pieces into those below the line and those above it. -/
theorem SquareDissection.exists_horizontalBand_partition_of_avoids_height
    (d : SquareDissection) {y : ℝ}
    (havoid : ∀ i, ∀ p ∈ interior (d.piece i), p 1 ≠ y) :
    ∃ s : Finset (Fin 4),
      (∀ i ∈ s, d.piece i ⊆ horizontalBand 0 y) ∧
      (∀ i ∉ s, d.piece i ⊆ horizontalBand y 1) := by
  classical
  have hside (i : Fin 4) :
      d.piece i ⊆ horizontalBand 0 y ∨ d.piece i ⊆ horizontalBand y 1 :=
    (d.jordan i).subset_horizontalBand_or_of_avoids_height (d.piece_subset i) (havoid i)
  refine ⟨Finset.univ.filter (fun i => d.piece i ⊆ horizontalBand 0 y), ?_, ?_⟩
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i hi
    apply (hside i).resolve_left
    intro hlo
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlo⟩)

/-- A horizontal line crossing no piece interior has height an integer
multiple of one quarter. -/
theorem SquareDissection.horizontal_separator_height_eq_nat_quarter
    (d : SquareDissection) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (havoid : ∀ i, ∀ p ∈ interior (d.piece i), p 1 ≠ y) :
    ∃ k : ℕ, k ≤ 4 ∧ y = (k : ℝ) / 4 := by
  obtain ⟨s, hbelow, habove⟩ := d.exists_horizontalBand_partition_of_avoids_height havoid
  refine ⟨s.card, ?_, d.horizontal_cut_height_eq_card_div_four s hy hbelow habove⟩
  simpa only [Fintype.card_fin] using Finset.card_le_univ s

/-- If the horizontal segment across the square lies in the union of the
piece frontiers, it meets no piece interior. -/
theorem SquareDissection.interiors_avoid_height_of_horizontal_frontier_cover
    (d : SquareDissection) {y : ℝ}
    (hfront : {p : Plane | p ∈ unitSquare ∧ p 1 = y} ⊆
      ⋃ i, frontier (d.piece i)) :
    ∀ i, ∀ p ∈ interior (d.piece i), p 1 ≠ y := by
  intro i p hp heq
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hfront ⟨d.piece_subset i (interior_subset hp), heq⟩)
  by_cases hij : i = j
  · subst j
    exact hj.2 hp
  · exact d.not_mem_other_piece hij hp ((d.jordan j).isClosed.frontier_subset hj)

/-- A horizontal segment across the square lying entirely in piece frontiers
must occur at one of the five integer quarter heights. -/
theorem SquareDissection.horizontal_frontier_separator_height_eq_nat_quarter
    (d : SquareDissection) {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (hfront : {p : Plane | p ∈ unitSquare ∧ p 1 = y} ⊆
      ⋃ i, frontier (d.piece i)) :
    ∃ k : ℕ, k ≤ 4 ∧ y = (k : ℝ) / 4 :=
  d.horizontal_separator_height_eq_nat_quarter hy
    (d.interiors_avoid_height_of_horizontal_frontier_cover hfront)

end Puzzling139335
