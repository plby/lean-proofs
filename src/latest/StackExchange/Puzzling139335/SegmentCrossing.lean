import StackExchange.Puzzling139335.SegmentCrossing.Algebra
import StackExchange.Puzzling139335.SegmentCrossing.Jordan
import StackExchange.Puzzling139335.SegmentCrossing.Overlap

/-!
# Transverse actual boundary segments force interior overlap

The segments in this file are required to lie in the actual frontiers of
the Jordan regions. A segment contained only in a convex hull does not meet
that hypothesis. No polygonality, rectifiability, or convexity is assumed.
-/

open Set

namespace Puzzling139335.SegmentCrossing

theorem detForm_eq_at_endpoints (A B : Plane) :
    detForm (B - A) A = detForm (B - A) B := by
  have h : detForm (B - A) (B - A) = 0 := by simp
  rw [map_sub] at h
  exact (sub_eq_zero.mp h).symm

/-- A transverse crossing in the relative interiors of two actual straight
Jordan-boundary segments forces the two open regions to overlap. -/
theorem interiors_inter_nonempty_of_transverse_boundary_segments
    {P Q : Set Plane} {A B C D x : Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hAB : segment ℝ A B ⊆ frontier P) (hCD : segment ℝ C D ⊆ frontier Q)
    (hdet : det (B - A) (D - C) ≠ 0)
    (hxAB : x ∈ openSegment ℝ A B) (hxCD : x ∈ openSegment ℝ C D) :
    (interior P ∩ interior Q).Nonempty := by
  have hneAB : A ≠ B := by
    intro h
    simp [h] at hdet
  have hneCD : C ≠ D := by
    intro h
    simp [h] at hdet
  have hdet' : det (D - C) (B - A) ≠ 0 := by
    rw [det_swap]
    exact neg_ne_zero.mpr hdet
  have hPc := jordan_segment_hasInteriorHalfBall_or_neg hP hneAB hAB hxAB
    (detForm (B - A)) (detForm_surjective_of_det_ne_zero hdet)
    (detForm_eq_at_endpoints A B)
  have hQc := jordan_segment_hasInteriorHalfBall_or_neg hQ hneCD hCD hxCD
    (detForm (D - C)) (detForm_surjective_of_det_ne_zero hdet')
    (detForm_eq_at_endpoints C D)
  rcases hPc with hPc | hPc <;> rcases hQc with hQc | hQc
  · apply hPc.inter_nonempty hQc
    obtain ⟨w, hw₁, hw₂⟩ := exists_detForm_eq_pair hdet 1 1
    exact ⟨w, by rw [hw₁]; norm_num, by rw [hw₂]; norm_num⟩
  · apply hPc.inter_nonempty hQc
    obtain ⟨w, hw₁, hw₂⟩ := exists_detForm_eq_pair hdet 1 (-1)
    refine ⟨w, by rw [hw₁]; norm_num, ?_⟩
    change 0 < -(detForm (D - C) w)
    rw [hw₂]
    norm_num
  · apply hPc.inter_nonempty hQc
    obtain ⟨w, hw₁, hw₂⟩ := exists_detForm_eq_pair hdet (-1) 1
    refine ⟨w, ?_, by rw [hw₂]; norm_num⟩
    change 0 < -(detForm (B - A) w)
    rw [hw₁]
    norm_num
  · apply hPc.inter_nonempty hQc
    obtain ⟨w, hw₁, hw₂⟩ := exists_detForm_eq_pair hdet (-1) (-1)
    refine ⟨w, ?_, ?_⟩
    · change 0 < -(detForm (B - A) w)
      rw [hw₁]
      norm_num
    · change 0 < -(detForm (D - C) w)
      rw [hw₂]
      norm_num

theorem not_disjoint_interiors_of_transverse_boundary_segments
    {P Q : Set Plane} {A B C D x : Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hAB : segment ℝ A B ⊆ frontier P) (hCD : segment ℝ C D ⊆ frontier Q)
    (hdet : det (B - A) (D - C) ≠ 0)
    (hxAB : x ∈ openSegment ℝ A B) (hxCD : x ∈ openSegment ℝ C D) :
    ¬ Disjoint (interior P) (interior Q) :=
  (interiors_inter_nonempty_of_transverse_boundary_segments hP hQ hAB hCD hdet
    hxAB hxCD).not_disjoint

/-- With disjoint Jordan interiors, transverse actual boundary segments cannot
meet in both relative interiors. -/
theorem openSegments_disjoint_of_disjoint_interiors
    {P Q : Set Plane} {A B C D : Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hdis : Disjoint (interior P) (interior Q))
    (hAB : segment ℝ A B ⊆ frontier P) (hCD : segment ℝ C D ⊆ frontier Q)
    (hdet : det (B - A) (D - C) ≠ 0) :
    Disjoint (openSegment ℝ A B) (openSegment ℝ C D) := by
  apply Set.disjoint_left.mpr
  intro x hxAB hxCD
  exact not_disjoint_interiors_of_transverse_boundary_segments hP hQ hAB hCD hdet
    hxAB hxCD hdis

/-- Direct bridge from a strict scalar-parameter intersection to the geometric
contradiction. -/
theorem not_disjoint_interiors_of_point_eq
    {P Q : Set Plane} {A B C D : Plane} {t u : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hAB : segment ℝ A B ⊆ frontier P) (hCD : segment ℝ C D ⊆ frontier Q)
    (hdet : det (B - A) (D - C) ≠ 0)
    (ht : t ∈ Ioo (0 : ℝ) 1) (hu : u ∈ Ioo (0 : ℝ) 1)
    (hpoint : point A B t = point C D u) :
    ¬ Disjoint (interior P) (interior Q) := by
  obtain ⟨x, hxAB, hxCD⟩ := openSegment_inter_nonempty_of_point_eq ht hu hpoint
  exact not_disjoint_interiors_of_transverse_boundary_segments hP hQ hAB hCD hdet
    hxAB hxCD

/-- Direct bridge from strict Cramer parameters to the geometric contradiction. -/
theorem not_disjoint_interiors_of_cramer
    {P Q : Set Plane} {A B C D : Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hAB : segment ℝ A B ⊆ frontier P) (hCD : segment ℝ C D ⊆ frontier Q)
    (hdet : det (B - A) (D - C) ≠ 0)
    (ht : det (C - A) (D - C) / det (B - A) (D - C) ∈ Ioo (0 : ℝ) 1)
    (hu : det (C - A) (B - A) / det (B - A) (D - C) ∈ Ioo (0 : ℝ) 1) :
    ¬ Disjoint (interior P) (interior Q) :=
  not_disjoint_interiors_of_point_eq hP hQ hAB hCD hdet ht hu (point_eq_of_cramer hdet)

end Puzzling139335.SegmentCrossing

namespace Puzzling139335

theorem SquareDissection.openSegments_disjoint_of_transverse_frontiers
    (d : SquareDissection) {i j : Fin 4} (hij : i ≠ j) {A B C D : Plane}
    (hAB : segment ℝ A B ⊆ frontier (d.piece i))
    (hCD : segment ℝ C D ⊆ frontier (d.piece j))
    (hdet : SegmentCrossing.det (B - A) (D - C) ≠ 0) :
    Disjoint (openSegment ℝ A B) (openSegment ℝ C D) :=
  SegmentCrossing.openSegments_disjoint_of_disjoint_interiors
    (d.jordan i) (d.jordan j) (d.disjoint_interiors hij) hAB hCD hdet

end Puzzling139335
