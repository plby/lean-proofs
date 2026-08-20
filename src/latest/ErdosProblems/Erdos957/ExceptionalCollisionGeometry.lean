import ErdosProblems.Erdos957.Case2RoleUniqueness

/-!
# Analytic kernels for the exceptional Erdős 957 arrivals

This file contains only coordinate consequences of the checked rigid
Case-2 picture.  In particular, it proves that the two vertically deep
secondary recipients `w` and `wNext` cannot be a unit distance from a hull
point in the shallow outgoing cone.  Hence any such direct competitor to a
Case-2 secondary arrival must meet the remaining `e` branch.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957ExceptionalCollisionGeometry

open Erdos957GeometryCore
open Erdos957Case2RoleUniqueness

abbrev Point := Erdos957GeometryCore.Point

private lemma coord_sq_of_dist_eq_one
    (z c : Point) (h : dist z c = 1) :
    (z 0 - c 0) ^ 2 + (z 1 - c 1) ^ 2 = 1 := by
  have hs := Erdos957Cases24.dist_sq_eq_coordinates z c
  rw [h] at hs
  nlinarith

/-- Two vertices joined to one common unit target cannot be more than two
units apart in a single horizontal coordinate of any retained rigid chart.
This is the metric kernel used for far away-prefix competitors in Case 4. -/
lemma no_common_unit_target_of_rigid_fst_gap_gt_two
    {A : Finset Point}
    (E : Erdos957Case24Bridge.Framed.RigidChart)
    {middle competitor target : Vertex A}
    (hm : (unitDistanceGraph A).Adj middle target)
    (hc : (unitDistanceGraph A).Adj competitor target)
    (hgap : 2 < |(E.toCanonical middle) 0 -
      (E.toCanonical competitor) 0|) : False := by
  have hdistLe : dist (middle : Point) (competitor : Point) ≤ 2 := by
    calc
      dist (middle : Point) (competitor : Point) ≤
          dist (middle : Point) (target : Point) +
            dist (target : Point) (competitor : Point) := dist_triangle _ _ _
      _ = 2 := by
        rw [show dist (middle : Point) (target : Point) = 1 by
              simpa [unitDistanceGraph] using hm,
            show dist (target : Point) (competitor : Point) = 1 by
              simpa [unitDistanceGraph, dist_comm] using hc]
        norm_num
  have hdistCoord : dist (E.toCanonical middle)
      (E.toCanonical competitor) ≤ 2 := by
    rw [E.dist_eq]
    exact hdistLe
  have hs := Erdos957Cases24.dist_sq_eq_coordinates
    (E.toCanonical middle) (E.toCanonical competitor)
  have habsnonneg : 0 ≤ |(E.toCanonical middle) 0 -
      (E.toCanonical competitor) 0| := abs_nonneg _
  have hsnd : 0 ≤ ((E.toCanonical middle) 1 -
      (E.toCanonical competitor) 1) ^ 2 := sq_nonneg _
  have hdistnonneg : 0 ≤ dist (E.toCanonical middle)
      (E.toCanonical competitor) := dist_nonneg
  have hgapSq : 4 < ((E.toCanonical middle) 0 -
      (E.toCanonical competitor) 0) ^ 2 := by
    nlinarith [sq_abs ((E.toCanonical middle) 0 -
      (E.toCanonical competitor) 0)]
  nlinarith

/-- The canonical `w=(0,-√3)` unit circle is disjoint from the shallow
cone `-y≤x/5`. -/
lemma not_unit_case2_w_of_shallow_cone
    (z : Point) (hcone : -z 1 ≤ z 0 / 5) :
    dist z Erdos957Cases24.Case2.w ≠ 1 := by
  intro hunit
  have hs := coord_sq_of_dist_eq_one z Erdos957Cases24.Case2.w hunit
  simp only [Erdos957Cases24.Case2.w,
    Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one, sub_zero] at hs
  have hx : -5 * z 1 ≤ z 0 := by linarith
  have hsqrtone : (1 : ℝ) < Erdos957Cases24.sqrtThree := by
    nlinarith [Erdos957Cases24.sqrtThree_pos,
      Erdos957Cases24.sqrtThree_sq]
  have hyneg : z 1 < 0 := by
    by_contra hy
    have hy' : 0 ≤ z 1 := le_of_not_gt hy
    nlinarith [sq_nonneg (z 0),
      sq_nonneg (z 1 + Erdos957Cases24.sqrtThree)]
  have hxnonneg : 0 ≤ z 0 := by linarith
  have hsq : 25 * (z 1) ^ 2 ≤ (z 0) ^ 2 := by
    have hprod : 0 ≤ (z 0 + 5 * z 1) * (z 0 - 5 * z 1) := by
      exact mul_nonneg (by linarith) (by linarith)
    nlinarith
  nlinarith [hsq, sq_nonneg (26 * z 1 + Erdos957Cases24.sqrtThree),
    Erdos957Cases24.sqrtThree_sq]

/-- The canonical `wNext=(1,-√3)` unit circle is also disjoint from the
same shallow cone. -/
lemma not_unit_case2_wNext_of_shallow_cone
    (z : Point) (hcone : -z 1 ≤ z 0 / 5) :
    dist z Erdos957Cases24.Case2.wNext ≠ 1 := by
  intro hunit
  have hs := coord_sq_of_dist_eq_one z Erdos957Cases24.Case2.wNext hunit
  simp only [Erdos957Cases24.Case2.wNext,
    Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one] at hs
  have hxle : z 0 ≤ 2 := by
    nlinarith [sq_nonneg (z 1 + Erdos957Cases24.sqrtThree)]
  have hylower : -(2 / 5 : ℝ) ≤ z 1 := by linarith
  have hsqrt : (7 / 5 : ℝ) < Erdos957Cases24.sqrtThree := by
    nlinarith [Erdos957Cases24.sqrtThree_pos,
      Erdos957Cases24.sqrtThree_sq]
  have hone : 1 < z 1 + Erdos957Cases24.sqrtThree := by linarith
  nlinarith [sq_nonneg (z 0 - 1)]

/-- A point strictly to the right of `x=5/2` cannot be a unit distance
from `e=(3/2,-√3/2)`. -/
lemma not_unit_case2_e_of_fst_gt_five_halves
    (z : Point) (hx : (5 / 2 : ℝ) < z 0) :
    dist z Erdos957Cases24.Case2.e ≠ 1 := by
  intro hunit
  have hs := coord_sq_of_dist_eq_one z Erdos957Cases24.Case2.e hunit
  simp only [Erdos957Cases24.Case2.e,
    Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one] at hs
  nlinarith [sq_nonneg (z 1 + Erdos957Cases24.sqrtThree / 2)]

/-- Every Case-2 secondary recipient has nonnegative horizontal coordinate,
so a point strictly left of `x=-1` cannot be unit adjacent to it. -/
lemma not_unit_case2_secondary_of_fst_lt_neg_one
    (z target : Point) (hx : z 0 < -1)
    (htarget : target = Erdos957Cases24.Case2.w ∨
      target = Erdos957Cases24.Case2.wNext ∨
      target = Erdos957Cases24.Case2.e) :
    dist z target ≠ 1 := by
  intro hunit
  have hs := coord_sq_of_dist_eq_one z target hunit
  rcases htarget with rfl | rfl | rfl <;>
    simp only [Erdos957Cases24.Case2.w,
      Erdos957Cases24.Case2.wNext, Erdos957Cases24.Case2.e,
      Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one, sub_zero] at hs <;>
    nlinarith [sq_nonneg (z 1 + Erdos957Cases24.sqrtThree),
      sq_nonneg (z 1 + Erdos957Cases24.sqrtThree / 2)]

/-- The incident partner itself, at canonical `uPrev=(-1,0)`, is not unit
adjacent to any Case-2 secondary recipient. -/
lemma case2_uPrev_not_unit_secondary
    (target : Point)
    (htarget : target = Erdos957Cases24.Case2.w ∨
      target = Erdos957Cases24.Case2.wNext ∨
      target = Erdos957Cases24.Case2.e) :
    dist Erdos957Cases24.Case2.uPrev target ≠ 1 := by
  rcases htarget with rfl | rfl | rfl <;>
    intro h <;>
    have hs := coord_sq_of_dist_eq_one _ _ h <;>
    simp only [Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.Case2.w, Erdos957Cases24.Case2.wNext,
      Erdos957Cases24.Case2.e, Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one] at hs <;>
    nlinarith [Erdos957Cases24.sqrtThree_sq]

/-- A unit-adjacent shallow-cone competitor to an actual Case-2 secondary
recipient forces the sole surviving canonical formula `e`. -/
theorem Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj
    {A : Finset Point} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {v t : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (hcone : -(D.edgeFrame.toCanonical t) 1 ≤
      (D.edgeFrame.toCanonical t) 0 / 5)
    (hadj : (unitDistanceGraph A).Adj t v) :
    D.edgeFrame.toCanonical v = Erdos957Cases24.Case2.e := by
  have hunit : dist (D.edgeFrame.toCanonical t)
      (D.edgeFrame.toCanonical v) = 1 := by
    rw [D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using hadj
  rcases D.target_edge_coordinate_cases with hw | hwNext | he
  · exfalso
    rw [hw] at hunit
    exact not_unit_case2_w_of_shallow_cone _ hcone hunit
  · exfalso
    rw [hwNext] at hunit
    exact not_unit_case2_wNext_of_shallow_cone _ hcone hunit
  · exact he

/-- Combining the shallow-cone screen with the three-step horizontal exit
excludes every Case-2 secondary formula. -/
theorem Case2SecondaryFormula.not_adj_of_shallow_cone_and_fst_gt_five_halves
    {A : Finset Point} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {v t : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (hcone : -(D.edgeFrame.toCanonical t) 1 ≤
      (D.edgeFrame.toCanonical t) 0 / 5)
    (hx : (5 / 2 : ℝ) < (D.edgeFrame.toCanonical t) 0) :
    ¬ (unitDistanceGraph A).Adj t v := by
  intro hadj
  have he :=
    Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj D hcone hadj
  have hunit : dist (D.edgeFrame.toCanonical t)
      (D.edgeFrame.toCanonical v) = 1 := by
    rw [D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using hadj
  rw [he] at hunit
  exact not_unit_case2_e_of_fst_gt_five_halves _ hx hunit

/-- Actual-frame form of the left-of-partner exclusion. -/
theorem Case2SecondaryFormula.not_adj_of_fst_lt_neg_one
    {A : Finset Point} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {v t : Vertex A}
    (D : Case2SecondaryFormula (P := P) (source := source) v)
    (hx : (D.edgeFrame.toCanonical t) 0 < -1) :
    ¬ (unitDistanceGraph A).Adj t v := by
  intro hadj
  have hunit : dist (D.edgeFrame.toCanonical t)
      (D.edgeFrame.toCanonical v) = 1 := by
    rw [D.edgeFrame.dist_eq]
    simpa [unitDistanceGraph] using hadj
  apply not_unit_case2_secondary_of_fst_lt_neg_one
    (D.edgeFrame.toCanonical t) (D.edgeFrame.toCanonical v) hx
  rcases D.target_edge_coordinate_cases with hw | hwNext | he
  · exact Or.inl hw
  · exact Or.inr (Or.inl hwNext)
  · exact Or.inr (Or.inr he)
  · exact hunit

/-- The rigid chart in which a generalized Case-4 split formula retains
its actual middle and secondary recipient. -/
def Case4SplitRightFormula.rigidFrame
    {A : Finset Point} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {v : Vertex A} :
    Case4SplitRightFormula (P := P) (source := source) v →
      Erdos957Case24Bridge.Framed.RigidChart
  | .orderedLow _ _ frame _ _ _ _ _ _ => frame
  | .orderedHigh _ _ frame _ _ _ _ _ _ _ => frame
  | .paired _ frame _ _ _ _ _ _ _ _ => frame

@[simp] lemma Case4SplitRightFormula.rigidFrame_middleVertex
    {A : Finset Point} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {v : Vertex A}
    (D : Case4SplitRightFormula (P := P) (source := source) v) :
    (Case4SplitRightFormula.rigidFrame D).toCanonical D.middleVertex =
      Erdos957Cases24.Case2.v := by
  cases D <;> assumption

/-- Any direct competitor to a split-right target has rigid-frame
horizontal coordinate at most `3/2`: otherwise it is more than two units
horizontally from the retained middle `v=(-1/2,-√3/2)`. -/
theorem Case4SplitRightFormula.not_direct_competitor_of_fst_gt_three_halves
    {A : Finset Point} {P : CyclicHullData A}
    {source : {p // p ∈ P.H}} {v competitor : Vertex A}
    (D : Case4SplitRightFormula (P := P) (source := source) v)
    (hx : (3 / 2 : ℝ) <
      ((Case4SplitRightFormula.rigidFrame D).toCanonical competitor) 0) :
    ¬ (unitDistanceGraph A).Adj competitor v := by
  intro hcomp
  apply no_common_unit_target_of_rigid_fst_gap_gt_two
    (Case4SplitRightFormula.rigidFrame D)
    D.middle_target_adj hcomp
  rw [Case4SplitRightFormula.rigidFrame_middleVertex D]
  simp only [Erdos957Cases24.Case2.v,
    Erdos957Cases24.point_apply_zero]
  rw [abs_of_neg (by linarith)]
  linarith

end Erdos957ExceptionalCollisionGeometry

#print axioms Erdos957ExceptionalCollisionGeometry.not_unit_case2_w_of_shallow_cone
#print axioms Erdos957ExceptionalCollisionGeometry.no_common_unit_target_of_rigid_fst_gap_gt_two
#print axioms Erdos957ExceptionalCollisionGeometry.not_unit_case2_wNext_of_shallow_cone
#print axioms Erdos957ExceptionalCollisionGeometry.not_unit_case2_e_of_fst_gt_five_halves
#print axioms Erdos957ExceptionalCollisionGeometry.not_unit_case2_secondary_of_fst_lt_neg_one
#print axioms Erdos957ExceptionalCollisionGeometry.case2_uPrev_not_unit_secondary
#print axioms Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.target_eq_e_of_shallow_cone_of_adj
#print axioms Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.not_adj_of_shallow_cone_and_fst_gt_five_halves
#print axioms Erdos957ExceptionalCollisionGeometry.Case2SecondaryFormula.not_adj_of_fst_lt_neg_one
#print axioms Erdos957ExceptionalCollisionGeometry.Case4SplitRightFormula.not_direct_competitor_of_fst_gt_three_halves
