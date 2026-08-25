import StackExchange.Puzzling139335.RectangularHull.Interlacing

/-!
# Alternating contacts for perpendicular square bands

The boundary arc follows the bottom side and then the right side. A strict
bottom contact is inside this arc, while the top-left corner is outside it.
-/

open Set Schoenflies

namespace Puzzling139335.RectangularHull

private def bottomRightBoundaryArc (h : ℝ) : Set Plane :=
  segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ∪
    segment ℝ (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 h)

private lemma bottomRightBoundaryArc_isArc {h : ℝ} (hh : 0 < h) :
    IsArcBetween (bottomRightBoundaryArc h)
      (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 h) := by
  have hbottom : Schoenflies.Plane.mk 0 0 ≠ Schoenflies.Plane.mk 1 0 := by
    intro heq
    have := congrArg (fun p : Plane => p 0) heq
    norm_num at this
  have hright : Schoenflies.Plane.mk 1 0 ≠ Schoenflies.Plane.mk 1 h := by
    intro heq
    have := congrArg (fun p : Plane => p 1) heq
    exact (ne_of_lt hh) this
  apply (isArcBetween_segment hbottom).concatenate (isArcBetween_segment hright)
  intro p hp hq
  have hp1 := (Schoenflies.mem_segment_horiz.mp hp).1
  have hp0 := (Schoenflies.mem_segment_vert.mp hq).1
  ext i
  fin_cases i
  · exact hp0
  · exact hp1

private lemma right_mem_frontier {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Schoenflies.Plane.mk 1 y ∈ frontier unitSquare := by
  rw [unitSquare_eq_closedSquare]
  apply Schoenflies.Plane.mem_frontier_closedSquare_of_fst
  · norm_num [squareCenter]
  · change |y - (1 / 2 : ℝ)| ≤ 1 / 2
    rw [abs_le]
    constructor <;> linarith

private lemma bottomRightBoundaryArc_subset_frontier {h : ℝ}
    (hh0 : 0 < h) (hh1 : h ≤ 1) :
    bottomRightBoundaryArc h ⊆ frontier unitSquare := by
  rintro p (hp | hp)
  · exact bottom_segment_subset_frontier (by norm_num) (by norm_num) (by norm_num) hp
  · rw [Schoenflies.mem_segment_vert, segment_eq_Icc hh0.le] at hp
    have heq : p = Schoenflies.Plane.mk 1 (p 1) := by
      ext i
      fin_cases i
      · exact hp.1
      · rfl
    rw [heq]
    exact right_mem_frontier hp.2.1 (hp.2.2.trans hh1)

/-- These four actual contacts alternate around the square boundary.
The two pieces therefore cannot have disjoint Jordan interiors. -/
theorem bottom_left_contacts_impossible {P Q : Set Plane} {h w : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hh0 : 0 < h) (hh1 : h ≤ 1) (hw0 : 0 < w) (hw1 : w ≤ 1)
    (hBL : Schoenflies.Plane.mk 0 0 ∈ P)
    (hRh : Schoenflies.Plane.mk 1 h ∈ P)
    (hwB : Schoenflies.Plane.mk w 0 ∈ Q)
    (hTL : Schoenflies.Plane.mk 0 1 ∈ Q) : False := by
  have hwA : Schoenflies.Plane.mk w 0 ∈ bottomRightBoundaryArc h \
      {Schoenflies.Plane.mk 0 0, Schoenflies.Plane.mk 1 h} := by
    constructor
    · left
      rw [Schoenflies.mem_segment_horiz, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
      exact ⟨rfl, hw0.le, hw1⟩
    · intro hmem
      rcases mem_insert_iff.mp hmem with heq | heq
      · exact (ne_of_gt hw0) (congrArg (fun p : Plane => p 0) heq)
      · have := congrArg (fun p : Plane => p 1) (mem_singleton_iff.mp heq)
        exact (ne_of_lt hh0) this
  have hTLnot : Schoenflies.Plane.mk 0 1 ∉ bottomRightBoundaryArc h := by
    rintro (hmem | hmem)
    · have := (Schoenflies.mem_segment_horiz.mp hmem).1
      norm_num at this
    · have := (Schoenflies.mem_segment_vert.mp hmem).1
      norm_num at this
  exact boundary_arc_contacts_impossible hP hQ isJordanRegion_unitSquare hPS hQS hdis
    (bottomRightBoundaryArc_isArc hh0) (bottomRightBoundaryArc_subset_frontier hh0 hh1)
    hBL hRh hwB hTL hwA (top_mem_frontier (by norm_num) (by norm_num)) hTLnot

end Puzzling139335.RectangularHull
