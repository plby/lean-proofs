import ErdosProblems.Erdos957.Case2SecondaryNoThree

noncomputable section

namespace Erdos957Case2StrictTurnEliminator

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957Case2RoleUniqueness
open Erdos957Case2SecondaryNoThree

abbrev Point := Erdos957GeometryCore.Point

/- The two unit-circle intersections of the anchor source `u` and its
degree-five Case-2 target `w`. -/
lemma eq_v_or_b_of_unit_to_u_w {z : Point}
    (hu : dist Erdos957Cases24.Case2.u z = 1)
    (hw : dist Erdos957Cases24.Case2.w z = 1) :
    z = Erdos957Cases24.Case2.v ∨ z = Erdos957Cases24.Case2.b := by
  have huSq := congrArg (fun r : ℝ ↦ r ^ 2) hu
  have hwSq := congrArg (fun r : ℝ ↦ r ^ 2) hw
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at huSq hwSq
  simp only [Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.w,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
    one_pow] at huSq hwSq
  have hy : z 1 = -(Erdos957Cases24.sqrtThree / 2) := by
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  have hxSq : (z 0) ^ 2 = 1 / 4 := by
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (by
      calc
        (z 0) ^ 2 = 1 / 4 := hxSq
        _ = (1 / 2 : ℝ) ^ 2 := by norm_num) with hx | hx
  · right
    apply Erdos957Cases24.point_ext
    · simpa [Erdos957Cases24.Case2.b] using hx
    · simpa [Erdos957Cases24.Case2.b] using hy
  · left
    apply Erdos957Cases24.point_ext
    · simpa [Erdos957Cases24.Case2.v] using hx
    · simpa [Erdos957Cases24.Case2.v] using hy

/- The segment from `u` to `wNext` has length two, hence its common unit
neighbour is the canonical point `b`. -/
lemma eq_b_of_unit_to_u_wNext {z : Point}
    (hu : dist Erdos957Cases24.Case2.u z = 1)
    (hw : dist Erdos957Cases24.Case2.wNext z = 1) :
    z = Erdos957Cases24.Case2.b := by
  have huSq := congrArg (fun r : ℝ ↦ r ^ 2) hu
  have hwSq := congrArg (fun r : ℝ ↦ r ^ 2) hw
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at huSq hwSq
  simp only [Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.wNext,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
    one_pow] at huSq hwSq
  have hline : z 0 - Erdos957Cases24.sqrtThree * z 1 = 2 := by
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  have hx : z 0 = 1 / 2 := by
    nlinarith [Erdos957Cases24.sqrtThree_sq,
      sq_nonneg (Erdos957Cases24.sqrtThree * z 0 + z 1)]
  have hy : z 1 = -(Erdos957Cases24.sqrtThree / 2) := by
    rw [hx] at hline
    nlinarith [Erdos957Cases24.sqrtThree_sq,
      Erdos957Cases24.sqrtThree_ne_zero]
  exact Erdos957Cases24.point_ext
    (by simpa [Erdos957Cases24.Case2.b] using hx)
    (by simpa [Erdos957Cases24.Case2.b] using hy)

/- The two unit-circle intersections of `u` and `b`. -/
lemma eq_v_or_uNext_of_unit_to_u_b {z : Point}
    (hu : dist Erdos957Cases24.Case2.u z = 1)
    (hb : dist Erdos957Cases24.Case2.b z = 1) :
    z = Erdos957Cases24.Case2.v ∨ z = Erdos957Cases24.Case2.uNext := by
  have huSq := congrArg (fun r : ℝ ↦ r ^ 2) hu
  have hbSq := congrArg (fun r : ℝ ↦ r ^ 2) hb
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at huSq hbSq
  simp only [Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.b,
    Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one,
    one_pow] at huSq hbSq
  have hline : z 0 - Erdos957Cases24.sqrtThree * z 1 = 1 := by
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  have hwSq : dist Erdos957Cases24.Case2.wNext z ^ 2 = 3 := by
    rw [Erdos957Cases24.dist_sq_eq_coordinates]
    simp only [Erdos957Cases24.Case2.wNext,
      Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one]
    nlinarith [Erdos957Cases24.sqrtThree_sq]
  have hw : dist Erdos957Cases24.Case2.wNext z =
      Erdos957Cases24.sqrtThree := by
    nlinarith [hwSq, dist_nonneg
      (x := Erdos957Cases24.Case2.wNext) (y := z),
      Erdos957Cases24.sqrtThree_pos, Erdos957Cases24.sqrtThree_sq]
  exact eq_case2_v_or_uNext_of_dist_u_one_dist_wNext_sqrtThree hu hw

variable {A : Finset Point} {P : CyclicHullData A}

/- Reusable strict-turn/degree-count eliminator for the central surviving
mixed branch.  A Case-4 middle sharing the anchor source and a degree-five
Case-2 target is forced to canonical `b`; its hull source is then the
forbidden straight continuation `uNext`. -/
lemma no_case4_split_middle_on_anchor_edge
    (hA : IsOneSeparated A)
    {source z : {p // p ∈ P.H}} {q m : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) q)
    (hq : D.edgeFrame.toCanonical q = Erdos957Cases24.Case2.w ∨
      D.edgeFrame.toCanonical q = Erdos957Cases24.Case2.wNext)
    (hmSource : dist (source.1 : Point) (m : Point) = 1)
    (hmTarget : dist (m : Point) (q : Point) = 1)
    (hmDegree : (unitDistanceGraph A).degree m = 5)
    (hzSource : dist (source.1 : Point) (z.1 : Point) = 1)
    (hzMiddle : dist (z.1 : Point) (m : Point) = 1) : False := by
  let cm := D.edgeFrame.toCanonical (m : Point)
  let cz := D.edgeFrame.toCanonical (z.1 : Point)
  have hsource : D.edgeFrame.toCanonical source.1 =
      Erdos957Cases24.Case2.u := by
    rw [← D.source_actual, D.edgeFrame.toCanonical_actual]
  have hUm : dist Erdos957Cases24.Case2.u cm = 1 := by
    rw [← hsource, D.edgeFrame.dist_eq]
    exact hmSource
  have hqm : dist (D.edgeFrame.toCanonical q) cm = 1 := by
    rw [D.edgeFrame.dist_eq]
    simpa [dist_comm] using hmTarget
  have hmCases : cm = Erdos957Cases24.Case2.v ∨
      cm = Erdos957Cases24.Case2.b := by
    rcases hq with hq | hq
    · exact eq_v_or_b_of_unit_to_u_w hUm (by simpa [hq] using hqm)
    · exact Or.inr (eq_b_of_unit_to_u_wNext hUm (by simpa [hq] using hqm))
  have hmNeV : cm ≠ Erdos957Cases24.Case2.v := by
    intro hmV
    have hmmiddle : m = D.middle := by
      apply Subtype.ext
      apply D.edgeFrame.toCanonical.injective
      change cm = D.edgeFrame.toCanonical D.middle
      rw [hmV, ← D.middle_actual, D.edgeFrame.toCanonical_actual]
    have hdegreeSix : (unitDistanceGraph A).degree m = 6 := by
      rw [hmmiddle]
      exact D.middle_degree_six
    omega
  have hmB : cm = Erdos957Cases24.Case2.b := hmCases.resolve_left hmNeV
  have hUz : dist Erdos957Cases24.Case2.u cz = 1 := by
    rw [← hsource, D.edgeFrame.dist_eq]
    exact hzSource
  have hBz : dist Erdos957Cases24.Case2.b cz = 1 := by
    rw [← hmB, D.edgeFrame.dist_eq]
    simpa [dist_comm] using hzMiddle
  rcases eq_v_or_uNext_of_unit_to_u_b hUz hBz with hzV | hzNext
  · apply D.middle_not_hull
    have hzmiddle : z.1 = D.middle := by
      apply Subtype.ext
      apply D.edgeFrame.toCanonical.injective
      change cz = D.edgeFrame.toCanonical D.middle
      rw [hzV, ← D.middle_actual, D.edgeFrame.toCanonical_actual]
    exact hzmiddle ▸ z.property
  · apply Erdos957Case24Bridge.case2_uNext_not_mem_of_strict_support
      D.strict_support
    exact Finset.mem_image.mpr ⟨z.1, z.1.property, hzNext⟩

end Erdos957Case2StrictTurnEliminator

#print axioms Erdos957Case2StrictTurnEliminator.no_case4_split_middle_on_anchor_edge
