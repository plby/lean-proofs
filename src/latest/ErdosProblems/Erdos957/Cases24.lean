/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos957.Basic

/-!
# Coordinate geometry for Cases 2 and 4 in the Erdős 957 charging argument

This module contains only elementary Euclidean facts.  It fixes the
normal form used in Dumitrescu's Cases 2 and 4, verifies all advertised unit
edges, and proves that the successive "common neighbors" in the construction
are the only intersections of the relevant unit circles.  It does not assume
any global charging or incidence estimate.
-/

open Metric
open scoped EuclideanGeometry RealInnerProductSpace

namespace Erdos957Cases24

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable def sqrtThree : ℝ := Real.sqrt 3

lemma sqrtThree_pos : 0 < sqrtThree := by
  exact Real.sqrt_pos.2 (by norm_num)

lemma sqrtThree_sq : sqrtThree ^ 2 = 3 := by
  exact Real.sq_sqrt (by norm_num)

lemma sqrtThree_ne_zero : sqrtThree ≠ 0 := ne_of_gt sqrtThree_pos

lemma sqrtThree_le_two : sqrtThree ≤ 2 := by
  nlinarith [sqrtThree_sq, sqrtThree_pos.le]

noncomputable def point (x y : ℝ) : Point := !₂[x, y]

private lemma inner_eq_coordinates (u v : Point) :
    ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  ring

private lemma norm_sq_eq_coordinates (u : Point) :
    ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_coordinates]
  ring

lemma dist_sq_eq_coordinates (p q : Point) :
    dist p q ^ 2 = (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by
  rw [dist_eq_norm, norm_sq_eq_coordinates]
  simp

@[simp] lemma point_apply_zero (x y : ℝ) : point x y 0 = x := by
  simp [point]

@[simp] lemma point_apply_one (x y : ℝ) : point x y 1 = y := by
  simp [point]

lemma point_ext {p : Point} {x y : ℝ} (hx : p 0 = x) (hy : p 1 = y) :
    p = point x y := by
  ext i
  fin_cases i
  · simpa using hx
  · simpa using hy

@[simp] lemma point_inj {x₁ y₁ x₂ y₂ : ℝ} :
    point x₁ y₁ = point x₂ y₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun p : Point ↦ p 0) h,
      by simpa using congrArg (fun p : Point ↦ p 1) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

lemma dist_eq_one_of_sq_eq_one {p q : Point} (h : dist p q ^ 2 = 1) :
    dist p q = 1 := by
  nlinarith [dist_nonneg (x := p) (y := q)]

lemma dist_point_eq_one_of_coordinate_identity (x₁ y₁ x₂ y₂ : ℝ)
    (h : (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 = 1) :
    dist (point x₁ y₁) (point x₂ y₂) = 1 := by
  apply dist_eq_one_of_sq_eq_one
  rw [dist_sq_eq_coordinates]
  simpa using h

/-- The transfer rectangle in coordinates centered at the source hull vertex. -/
def InTransferRectangle (p : Point) : Prop :=
  -(7 / 4 : ℝ) ≤ p 0 ∧ p 0 ≤ 7 / 4 ∧ -(2 : ℝ) ≤ p 1 ∧ p 1 ≤ 0

/-- Strict membership in the half-plane below the normalized support line. -/
def BelowSupport (p : Point) : Prop := p 1 < 0

/-- The normalized minimum-distance adjacency relation. -/
def UnitAdjacent (p q : Point) : Prop := dist p q = 1

/-- A deliberately elementary version of graph distance at most two. -/
def WithinTwoUnitEdges (p q : Point) : Prop :=
  UnitAdjacent p q ∨ ∃ z, UnitAdjacent p z ∧ UnitAdjacent z q

/-- Signed twice-area, used only to make the Case 2 side-of-line claims
coordinate-explicit. -/
def orient (p q r : Point) : ℝ :=
  (q 0 - p 0) * (r 1 - p 1) - (q 1 - p 1) * (r 0 - p 0)

/-- Unit neighbors inside an arbitrary finite configuration. -/
noncomputable def unitNeighbors (A : Finset Point) (p : Point) : Finset Point :=
  A.filter fun q ↦ dist p q = 1

@[simp] lemma mem_unitNeighbors {A : Finset Point} {p q : Point} :
    q ∈ unitNeighbors A p ↔ q ∈ A ∧ dist p q = 1 := by
  simp [unitNeighbors]

/-- Pairwise minimum separation one. -/
def IsOneSeparated (A : Finset Point) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 ≤ dist x y

/-- Pure algebra behind one orientation of regular-hexagon completion.  Here
`(X,Y)` is on the unit circle and is at least unit distance from the east,
west, southeast, southwest, and northwest hexagon vertices.  The only
remaining position is northeast. -/
lemma northeast_coordinates_of_unit_and_five_separations {X Y : ℝ}
    (hunit : X ^ 2 + Y ^ 2 = 1)
    (heast : X ≤ 1 / 2)
    (hwest : -(1 / 2 : ℝ) ≤ X)
    (hsoutheast : X - sqrtThree * Y ≤ 1)
    (hsouthwest : -X - sqrtThree * Y ≤ 1)
    (hnorthwest : -X + sqrtThree * Y ≤ 1) :
    X = 1 / 2 ∧ Y = sqrtThree / 2 := by
  have hsySq : (sqrtThree * Y) ^ 2 = 3 * Y ^ 2 := by
    rw [mul_pow, sqrtThree_sq]
  have hsyPos : 0 < sqrtThree * Y := by
    by_contra hnot
    have hsyNonpos : sqrtThree * Y ≤ 0 := le_of_not_gt hnot
    rcases le_total 0 X with hx | hx
    · have hupper : -sqrtThree * Y ≤ 1 - X := by linarith
      have hright : 0 ≤ 1 - X := by linarith
      have hleft : 0 ≤ -sqrtThree * Y := by linarith
      have hprod : 0 ≤ ((1 - X) - (-sqrtThree * Y)) *
          ((1 - X) + (-sqrtThree * Y)) :=
        mul_nonneg (sub_nonneg.mpr hupper) (add_nonneg hright hleft)
      nlinarith [hsySq]
    · have hupper : -sqrtThree * Y ≤ 1 + X := by linarith
      have hright : 0 ≤ 1 + X := by linarith
      have hleft : 0 ≤ -sqrtThree * Y := by linarith
      have hprod : 0 ≤ ((1 + X) - (-sqrtThree * Y)) *
          ((1 + X) + (-sqrtThree * Y)) :=
        mul_nonneg (sub_nonneg.mpr hupper) (add_nonneg hright hleft)
      nlinarith [hsySq]
  have hupper : sqrtThree * Y ≤ 1 + X := by linarith
  have hright : 0 ≤ 1 + X := by linarith
  have hprod : 0 ≤ ((1 + X) - sqrtThree * Y) *
      ((1 + X) + sqrtThree * Y) := by
    exact mul_nonneg (sub_nonneg.mpr hupper) (add_nonneg hright hsyPos.le)
  have hx : X = 1 / 2 := by
    nlinarith [hsySq]
  have hsy : sqrtThree * Y = 3 / 2 := by
    rw [hx] at hnorthwest
    nlinarith [hsySq]
  constructor
  · exact hx
  · apply (mul_left_cancel₀ sqrtThree_ne_zero)
    rw [hsy]
    nlinarith [sqrtThree_sq]

namespace Case2

/-!
The right-hand Case 2 source is `u`.  The left source and common middle
neighbor form the downward unit equilateral triangle `uPrev,u,v`.  The points
`b,w,wNext,e` are exactly the right-hand lattice chain in the paper.
-/

noncomputable def uPrev : Point := point (-1) 0
noncomputable def u : Point := point 0 0
noncomputable def v : Point := point (-(1 / 2)) (-(sqrtThree / 2))
noncomputable def b : Point := point (1 / 2) (-(sqrtThree / 2))
noncomputable def w : Point := point 0 (-sqrtThree)
noncomputable def wNext : Point := point 1 (-sqrtThree)
noncomputable def e : Point := point (3 / 2) (-(sqrtThree / 2))
/-- The horizontal lattice continuation whose presence would flatten the hull
at the right source. -/
noncomputable def uNext : Point := point 1 0
/-- The two possible further lower neighbors of `e`. -/
noncomputable def eSouthEast : Point := point 2 (-sqrtThree)
noncomputable def eEast : Point := point (5 / 2) (-(sqrtThree / 2))
/-- The continuation of the slanted line through `wNext,e`. -/
noncomputable def eNorthEast : Point := point 2 0

private lemma unit_by_norm_num (x₁ y₁ x₂ y₂ : ℝ)
    (h : (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 = 1) :
    dist (point x₁ y₁) (point x₂ y₂) = 1 :=
  dist_point_eq_one_of_coordinate_identity x₁ y₁ x₂ y₂ h

lemma dist_uPrev_u : dist uPrev u = 1 := by
  apply unit_by_norm_num
  norm_num

lemma dist_uPrev_v : dist uPrev v = 1 := by
  apply unit_by_norm_num
  nlinarith [sqrtThree_sq]

lemma dist_u_v : dist u v = 1 := by
  apply unit_by_norm_num
  nlinarith [sqrtThree_sq]

lemma dist_u_b : dist u b = 1 := by
  apply unit_by_norm_num
  nlinarith [sqrtThree_sq]

lemma dist_v_b : dist v b = 1 := by
  apply unit_by_norm_num
  norm_num

lemma dist_v_w : dist v w = 1 := by
  apply unit_by_norm_num
  nlinarith [sqrtThree_sq]

lemma dist_b_w : dist b w = 1 := by
  apply unit_by_norm_num
  nlinarith [sqrtThree_sq]

lemma dist_b_wNext : dist b wNext = 1 := by
  apply unit_by_norm_num
  nlinarith [sqrtThree_sq]

lemma dist_w_wNext : dist w wNext = 1 := by
  apply unit_by_norm_num
  norm_num

lemma dist_b_e : dist b e = 1 := by
  apply unit_by_norm_num
  norm_num

lemma dist_wNext_e : dist wNext e = 1 := by
  apply unit_by_norm_num
  nlinarith [sqrtThree_sq]

lemma dist_b_uNext : dist b uNext = 1 := by
  apply unit_by_norm_num
  nlinarith [sqrtThree_sq]

lemma dist_u_uNext : dist u uNext = 1 := by
  apply unit_by_norm_num
  norm_num

lemma dist_e_eSouthEast : dist e eSouthEast = 1 := by
  apply unit_by_norm_num
  nlinarith [sqrtThree_sq]

lemma dist_e_eEast : dist e eEast = 1 := by
  apply unit_by_norm_num
  norm_num

lemma dist_e_eNorthEast : dist e eNorthEast = 1 := by
  apply unit_by_norm_num
  nlinarith [sqrtThree_sq]

lemma dist_e_uNext : dist e uNext = 1 := by
  apply unit_by_norm_num
  nlinarith [sqrtThree_sq]

/-- The three normalized hull-line points are exactly collinear, with `u` the
midpoint of its predecessor and continuation. -/
lemma u_eq_midpoint_uPrev_uNext :
    u = (1 / 2 : ℝ) • (uPrev + uNext) := by
  ext i
  fin_cases i <;> simp [u, uPrev, uNext, point]

/-- `eNorthEast` is the exact straight continuation from `wNext` through
`e`; its occurrence is the collinearity excluded in the paper. -/
lemma e_eq_midpoint_wNext_eNorthEast :
    e = (1 / 2 : ℝ) • (wNext + eNorthEast) := by
  ext i
  fin_cases i
  · change (3 / 2 : ℝ) = (1 / 2 : ℝ) * (1 + 2)
    norm_num
  · change -(sqrtThree / 2) = (1 / 2 : ℝ) * (-sqrtThree + 0)
    ring

lemma orient_wNext_e_b_pos : 0 < orient wNext e b := by
  simp only [orient, wNext, e, b, point_apply_zero, point_apply_one]
  nlinarith [sqrtThree_pos]

lemma orient_wNext_e_eSouthEast_neg : orient wNext e eSouthEast < 0 := by
  simp only [orient, wNext, e, eSouthEast, point_apply_zero, point_apply_one]
  nlinarith [sqrtThree_pos]

lemma orient_wNext_e_eEast_neg : orient wNext e eEast < 0 := by
  simp only [orient, wNext, e, eEast, point_apply_zero, point_apply_one]
  nlinarith [sqrtThree_pos]

lemma orient_wNext_e_uNext_pos : 0 < orient wNext e uNext := by
  simp only [orient, wNext, e, uNext, point_apply_zero, point_apply_one]
  nlinarith [sqrtThree_pos]

lemma orient_wNext_e_eNorthEast_eq_zero : orient wNext e eNorthEast = 0 := by
  simp only [orient, wNext, e, eNorthEast, point_apply_zero, point_apply_one]
  ring

/-- If a unit neighbor of `b` stays unit-separated from the five displayed
hexagon positions, it is the missing northeast position `uNext`. -/
lemma eq_uNext_of_unit_to_b_and_five_separations {x : Point}
    (hxb : dist x b = 1)
    (hxu : 1 ≤ dist x u) (hxv : 1 ≤ dist x v)
    (hxw : 1 ≤ dist x w) (hxwNext : 1 ≤ dist x wNext)
    (hxe : 1 ≤ dist x e) :
    x = uNext := by
  have hunit := congrArg (fun t : ℝ ↦ t ^ 2) hxb
  rw [dist_sq_eq_coordinates] at hunit
  simp only [b, point_apply_zero, point_apply_one, one_pow] at hunit
  have square_lower {q : Point} (h : 1 ≤ dist x q) : 1 ≤ dist x q ^ 2 := by
    nlinarith [dist_nonneg (x := x) (y := q)]
  have hu := square_lower hxu
  have hv := square_lower hxv
  have hw := square_lower hxw
  have hwn := square_lower hxwNext
  have he := square_lower hxe
  rw [dist_sq_eq_coordinates] at hu hv hw hwn he
  simp only [u, v, w, wNext, e, point_apply_zero, point_apply_one] at hu hv hw hwn he
  let X : ℝ := x 0 - 1 / 2
  let Y : ℝ := x 1 + sqrtThree / 2
  have hunitXY : X ^ 2 + Y ^ 2 = 1 := by
    dsimp [X, Y]
    nlinarith
  have heast : X ≤ 1 / 2 := by
    dsimp [X, Y]
    nlinarith
  have hwest : -(1 / 2 : ℝ) ≤ X := by
    dsimp [X, Y]
    nlinarith
  have hsoutheast : X - sqrtThree * Y ≤ 1 := by
    dsimp [X, Y]
    nlinarith [sqrtThree_sq]
  have hsouthwest : -X - sqrtThree * Y ≤ 1 := by
    dsimp [X, Y]
    nlinarith [sqrtThree_sq]
  have hnorthwest : -X + sqrtThree * Y ≤ 1 := by
    dsimp [X, Y]
    nlinarith [sqrtThree_sq]
  obtain ⟨hX, hY⟩ := northeast_coordinates_of_unit_and_five_separations
    hunitXY heast hwest hsoutheast hsouthwest hnorthwest
  apply point_ext
  · dsimp [X] at hX
    nlinarith
  · dsimp [Y] at hY
    nlinarith

/-- The five consecutive, already occupied neighbor positions around `b`. -/
noncomputable def displayedFiveAtB : Finset Point := {u, v, w, wNext, e}

lemma card_displayedFiveAtB : displayedFiveAtB.card = 5 := by
  have h₁ : u ∉ ({v, w, wNext, e} : Finset Point) := by
    simp [u, v, w, wNext, e, point_inj, sqrtThree_ne_zero]
  have h₂ : v ∉ ({w, wNext, e} : Finset Point) := by
    simp [v, w, wNext, e, point_inj]
    norm_num
  have h₃ : w ∉ ({wNext, e} : Finset Point) := by
    simp [w, wNext, e, point_inj]
    norm_num
  have h₄ : wNext ∉ ({e} : Finset Point) := by
    simp [wNext, e, point_inj]
    norm_num
  simp only [displayedFiveAtB, Finset.card_insert_of_notMem h₁,
    Finset.card_insert_of_notMem h₂, Finset.card_insert_of_notMem h₃,
    Finset.card_insert_of_notMem h₄, Finset.card_singleton]

lemma displayedFiveAtB_unit (q : Point) (hq : q ∈ displayedFiveAtB) :
    dist b q = 1 := by
  simp only [displayedFiveAtB, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · simpa [dist_comm] using dist_u_b
  · simpa [dist_comm] using dist_v_b
  · exact dist_b_w
  · exact dist_b_wNext
  · exact dist_b_e

/-- This derives the actual missing lattice point from degree six, provided
the five consecutive displayed positions are already present.  It is a local
regular-hexagon rigidity lemma proved here without assuming a global charging
claim. -/
lemma uNext_mem_of_card_unitNeighbors_b_eq_six {A : Finset Point}
    (hsep : IsOneSeparated A) (hdisplay : displayedFiveAtB ⊆ A)
    (hdegree : (unitNeighbors A b).card = 6) :
    uNext ∈ A := by
  by_contra hnot
  have hsubset : unitNeighbors A b ⊆ displayedFiveAtB := by
    intro x hx
    by_contra hxdisplay
    have hxA : x ∈ A := (mem_unitNeighbors.mp hx).1
    have hxb : dist x b = 1 := by
      simpa [dist_comm] using (mem_unitNeighbors.mp hx).2
    have huMem : u ∈ displayedFiveAtB := by simp [displayedFiveAtB]
    have hvMem : v ∈ displayedFiveAtB := by simp [displayedFiveAtB]
    have hwMem : w ∈ displayedFiveAtB := by simp [displayedFiveAtB]
    have hwnMem : wNext ∈ displayedFiveAtB := by simp [displayedFiveAtB]
    have heMem : e ∈ displayedFiveAtB := by simp [displayedFiveAtB]
    have hxu : 1 ≤ dist x u := hsep x hxA u (hdisplay huMem) (by
      intro h
      subst x
      exact hxdisplay huMem)
    have hxv : 1 ≤ dist x v := hsep x hxA v (hdisplay hvMem) (by
      intro h
      subst x
      exact hxdisplay hvMem)
    have hxw : 1 ≤ dist x w := hsep x hxA w (hdisplay hwMem) (by
      intro h
      subst x
      exact hxdisplay hwMem)
    have hxwn : 1 ≤ dist x wNext := hsep x hxA wNext (hdisplay hwnMem) (by
      intro h
      subst x
      exact hxdisplay hwnMem)
    have hxe : 1 ≤ dist x e := hsep x hxA e (hdisplay heMem) (by
      intro h
      subst x
      exact hxdisplay heMem)
    have hxnext := eq_uNext_of_unit_to_b_and_five_separations
      hxb hxu hxv hxw hxwn hxe
    exact hnot (hxnext ▸ hxA)
  have hcard := Finset.card_le_card hsubset
  rw [hdegree, card_displayedFiveAtB] at hcard
  omega

lemma b_in_rectangle : InTransferRectangle b := by
  simp only [InTransferRectangle, b, point_apply_zero, point_apply_one]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · nlinarith [sqrtThree_le_two]
  · nlinarith [sqrtThree_pos]

lemma w_in_rectangle : InTransferRectangle w := by
  simp only [InTransferRectangle, w, point_apply_zero, point_apply_one]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · nlinarith [sqrtThree_le_two]
  · nlinarith [sqrtThree_pos]

lemma wNext_in_rectangle : InTransferRectangle wNext := by
  simp only [InTransferRectangle, wNext, point_apply_zero, point_apply_one]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · nlinarith [sqrtThree_le_two]
  · nlinarith [sqrtThree_pos]

lemma e_in_rectangle : InTransferRectangle e := by
  simp only [InTransferRectangle, e, point_apply_zero, point_apply_one]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · nlinarith [sqrtThree_le_two]
  · nlinarith [sqrtThree_pos]

lemma v_in_rectangle : InTransferRectangle v := by
  simp only [InTransferRectangle, v, point_apply_zero, point_apply_one]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · nlinarith [sqrtThree_le_two]
  · nlinarith [sqrtThree_pos]

lemma b_below_support : BelowSupport b := by
  simp only [BelowSupport, b, point_apply_one]
  nlinarith [sqrtThree_pos]

lemma v_below_support : BelowSupport v := by
  simp only [BelowSupport, v, point_apply_one]
  nlinarith [sqrtThree_pos]

lemma w_below_support : BelowSupport w := by
  simp only [BelowSupport, w, point_apply_one]
  nlinarith [sqrtThree_pos]

lemma wNext_below_support : BelowSupport wNext := by
  simp only [BelowSupport, wNext, point_apply_one]
  nlinarith [sqrtThree_pos]

lemma e_below_support : BelowSupport e := by
  simp only [BelowSupport, e, point_apply_one]
  nlinarith [sqrtThree_pos]

lemma u_within_two_b : WithinTwoUnitEdges u b := by
  exact Or.inl dist_u_b

lemma u_within_two_v : WithinTwoUnitEdges u v := by
  exact Or.inl dist_u_v

lemma u_within_two_w : WithinTwoUnitEdges u w := by
  exact Or.inr ⟨v, dist_u_v, dist_v_w⟩

lemma u_within_two_wNext : WithinTwoUnitEdges u wNext := by
  exact Or.inr ⟨b, dist_u_b, dist_b_wNext⟩

lemma u_within_two_e : WithinTwoUnitEdges u e := by
  exact Or.inr ⟨b, dist_u_b, dist_b_e⟩

/-- The two unit circles centered at `b` and `w` meet only at `v` and
`wNext`.  This is the exact coordinate form of the first Case 2 lattice
continuation. -/
lemma eq_v_or_wNext_of_unit_to_b_w {x : Point}
    (hxb : dist x b = 1) (hxw : dist x w = 1) :
    x = v ∨ x = wNext := by
  have hb := congrArg (fun t : ℝ ↦ t ^ 2) hxb
  have hw := congrArg (fun t : ℝ ↦ t ^ 2) hxw
  rw [dist_sq_eq_coordinates] at hb hw
  simp only [b, w, point_apply_zero, point_apply_one, one_pow] at hb hw
  have hline : x 0 + sqrtThree * x 1 = -2 := by
    nlinarith [sqrtThree_sq]
  have hsy : sqrtThree * x 1 = -2 - x 0 := by linarith
  have hsySq := congrArg (fun t : ℝ ↦ t ^ 2) hsy
  rw [mul_pow, sqrtThree_sq] at hsySq
  have hfactor : (2 * x 0 + 1) * (x 0 - 1) = 0 := by
    nlinarith [hb, hsySq]
  rcases mul_eq_zero.mp hfactor with hx | hx
  · left
    have hx0 : x 0 = -(1 / 2 : ℝ) := by linarith
    have hx1 : x 1 = -(sqrtThree / 2) := by
      apply (mul_left_cancel₀ sqrtThree_ne_zero)
      rw [hsy, hx0]
      nlinarith [sqrtThree_sq]
    exact point_ext hx0 hx1
  · right
    have hx0 : x 0 = 1 := by linarith
    have hx1 : x 1 = -sqrtThree := by
      apply (mul_left_cancel₀ sqrtThree_ne_zero)
      rw [hsy, hx0]
      nlinarith [sqrtThree_sq]
    exact point_ext hx0 hx1

/-- The next two unit circles meet only at the previous lattice point `w`
and the advertised Case 2 endpoint `e`. -/
lemma eq_w_or_e_of_unit_to_b_wNext {x : Point}
    (hxb : dist x b = 1) (hxw : dist x wNext = 1) :
    x = w ∨ x = e := by
  have hb := congrArg (fun t : ℝ ↦ t ^ 2) hxb
  have hw := congrArg (fun t : ℝ ↦ t ^ 2) hxw
  rw [dist_sq_eq_coordinates] at hb hw
  simp only [b, wNext, point_apply_zero, point_apply_one, one_pow] at hb hw
  have hline : x 0 - sqrtThree * x 1 = 3 := by
    nlinarith [sqrtThree_sq]
  have hsy : sqrtThree * x 1 = x 0 - 3 := by linarith
  have hsySq := congrArg (fun t : ℝ ↦ t ^ 2) hsy
  rw [mul_pow, sqrtThree_sq] at hsySq
  have hfactor : x 0 * (2 * x 0 - 3) = 0 := by
    nlinarith [hb, hsySq]
  rcases mul_eq_zero.mp hfactor with hx | hx
  · left
    have hx0 : x 0 = 0 := hx
    have hx1 : x 1 = -sqrtThree := by
      apply (mul_left_cancel₀ sqrtThree_ne_zero)
      rw [hsy, hx0]
      nlinarith [sqrtThree_sq]
    exact point_ext hx0 hx1
  · right
    have hx0 : x 0 = (3 / 2 : ℝ) := by linarith
    have hx1 : x 1 = -(sqrtThree / 2) := by
      apply (mul_left_cancel₀ sqrtThree_ne_zero)
      rw [hsy, hx0]
      nlinarith [sqrtThree_sq]
    exact point_ext hx0 hx1

/-- The secondary Case 2 recipient selected by the three degree branches. -/
noncomputable def secondaryRecipient (degreeW degreeWNext : ℕ) : Point :=
  if degreeW ≤ 5 then w else if degreeWNext ≤ 5 then wNext else e

/-- The support of the right-hand Case 2 transfer. -/
noncomputable def recipientSet (degreeW degreeWNext : ℕ) : Finset Point :=
  {b, secondaryRecipient degreeW degreeWNext}

lemma secondaryRecipient_in_rectangle (degreeW degreeWNext : ℕ) :
    InTransferRectangle (secondaryRecipient degreeW degreeWNext) := by
  simp only [secondaryRecipient]
  split_ifs
  · exact w_in_rectangle
  · exact wNext_in_rectangle
  · exact e_in_rectangle

lemma secondaryRecipient_below_support (degreeW degreeWNext : ℕ) :
    BelowSupport (secondaryRecipient degreeW degreeWNext) := by
  simp only [secondaryRecipient]
  split_ifs
  · exact w_below_support
  · exact wNext_below_support
  · exact e_below_support

lemma u_within_two_secondaryRecipient (degreeW degreeWNext : ℕ) :
    WithinTwoUnitEdges u (secondaryRecipient degreeW degreeWNext) := by
  simp only [secondaryRecipient]
  split_ifs
  · exact u_within_two_w
  · exact u_within_two_wNext
  · exact u_within_two_e

lemma mem_recipientSet_geometry {degreeW degreeWNext : ℕ} {x : Point}
    (hx : x ∈ recipientSet degreeW degreeWNext) :
    InTransferRectangle x ∧ BelowSupport x ∧ WithinTwoUnitEdges u x := by
  simp only [recipientSet, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b_in_rectangle, b_below_support, u_within_two_b⟩
  · exact ⟨secondaryRecipient_in_rectangle _ _, secondaryRecipient_below_support _ _,
      u_within_two_secondaryRecipient _ _⟩

end Case2

namespace Case4

/-!
Case 4 uses the same middle vertex and lowest neighbor as Case 2.  The two
common unit neighbors of that pair are `a` and `b` below.
-/

noncomputable def v : Point := Case2.v
noncomputable def w : Point := Case2.w
noncomputable def a : Point := point (-1) (-sqrtThree)
noncomputable def b : Point := Case2.b
/-- The regular-hexagon completion at `a` which would be a sixth neighbor of
the five-valent middle point `v`. -/
noncomputable def vMissing : Point := point (-(3 / 2)) (-(sqrtThree / 2))

lemma dist_v_a : dist v a = 1 := by
  change dist (point (-(1 / 2)) (-(sqrtThree / 2)))
    (point (-1) (-sqrtThree)) = 1
  apply dist_point_eq_one_of_coordinate_identity
  nlinarith [sqrtThree_sq]

lemma dist_w_a : dist w a = 1 := by
  change dist (point 0 (-sqrtThree)) (point (-1) (-sqrtThree)) = 1
  apply dist_point_eq_one_of_coordinate_identity
  norm_num

lemma dist_v_b : dist v b = 1 := Case2.dist_v_b

lemma dist_w_b : dist w b = 1 := by
  simpa [v, w, b, dist_comm] using Case2.dist_b_w

lemma dist_a_vMissing : dist a vMissing = 1 := by
  change dist (point (-1) (-sqrtThree))
    (point (-(3 / 2)) (-(sqrtThree / 2))) = 1
  apply dist_point_eq_one_of_coordinate_identity
  nlinarith [sqrtThree_sq]

lemma dist_v_vMissing : dist v vMissing = 1 := by
  change dist (point (-(1 / 2)) (-(sqrtThree / 2)))
    (point (-(3 / 2)) (-(sqrtThree / 2))) = 1
  apply dist_point_eq_one_of_coordinate_identity
  norm_num

/-- The five displayed neighbors of the five-valent Case 4 middle point. -/
noncomputable def displayedFiveAtV : Finset Point :=
  {Case2.uPrev, Case2.u, b, w, a}

/-- Adding the completion forced by a regular hexagon at `a` gives six
different unit neighbors of `v`. -/
noncomputable def completedSixAtV : Finset Point :=
  insert vMissing displayedFiveAtV

lemma card_displayedFiveAtV : displayedFiveAtV.card = 5 := by
  have h₁ : Case2.uPrev ∉ ({Case2.u, b, w, a} : Finset Point) := by
    simp [Case2.uPrev, Case2.u, b, Case2.b, w, Case2.w, a, point_inj,
      sqrtThree_ne_zero]
  have h₂ : Case2.u ∉ ({b, w, a} : Finset Point) := by
    simp [Case2.u, b, Case2.b, w, Case2.w, a, point_inj, sqrtThree_ne_zero]
  have h₃ : b ∉ ({w, a} : Finset Point) := by
    simp [b, Case2.b, w, Case2.w, a, point_inj]
    norm_num
  have h₄ : w ∉ ({a} : Finset Point) := by
    simp [w, Case2.w, a, point_inj]
  simp only [displayedFiveAtV, Finset.card_insert_of_notMem h₁,
    Finset.card_insert_of_notMem h₂, Finset.card_insert_of_notMem h₃,
    Finset.card_insert_of_notMem h₄, Finset.card_singleton]

lemma card_completedSixAtV : completedSixAtV.card = 6 := by
  have hmissing : vMissing ∉ displayedFiveAtV := by
    simp [displayedFiveAtV, vMissing, Case2.uPrev, Case2.u, b, Case2.b,
      w, Case2.w, a, point_inj, sqrtThree_ne_zero]
    norm_num
  rw [completedSixAtV, Finset.card_insert_of_notMem hmissing,
    card_displayedFiveAtV]

lemma completedSixAtV_unit (q : Point) (hq : q ∈ completedSixAtV) :
    dist v q = 1 := by
  simp only [completedSixAtV, displayedFiveAtV, Finset.mem_insert,
    Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact dist_v_vMissing
  · simpa [v, dist_comm] using Case2.dist_uPrev_v
  · simpa [v, dist_comm] using Case2.dist_u_v
  · exact dist_v_b
  · exact Case2.dist_v_w
  · exact dist_v_a

/-- If all six displayed lattice points occur in a configuration, then `v`
has at least six unit neighbors.  This is the exact degree contradiction used
after the Case 4 completion at `a` has been forced. -/
lemma six_le_card_unitNeighbors_v {A : Finset Point}
    (hsub : completedSixAtV ⊆ A) :
    6 ≤ (unitNeighbors A v).card := by
  rw [← card_completedSixAtV]
  apply Finset.card_le_card
  intro q hq
  exact mem_unitNeighbors.mpr ⟨hsub hq, completedSixAtV_unit q hq⟩

lemma vMissing_not_mem_of_card_unitNeighbors_eq_five {A : Finset Point}
    (hfive : displayedFiveAtV ⊆ A)
    (hdegree : (unitNeighbors A v).card = 5) :
    vMissing ∉ A := by
  intro hmissing
  have hsub : completedSixAtV ⊆ A := by
    intro q hq
    rw [completedSixAtV, Finset.mem_insert] at hq
    exact hq.elim (fun h ↦ h ▸ hmissing) (fun h ↦ hfive h)
  have := six_le_card_unitNeighbors_v hsub
  omega

lemma a_in_rectangle : InTransferRectangle a := by
  simp only [InTransferRectangle, a, point_apply_zero, point_apply_one]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · nlinarith [sqrtThree_le_two]
  · nlinarith [sqrtThree_pos]

lemma b_in_rectangle : InTransferRectangle b := by
  simpa [b] using Case2.b_in_rectangle

lemma v_in_rectangle : InTransferRectangle v := by
  simpa [v] using Case2.v_in_rectangle

lemma w_in_rectangle : InTransferRectangle w := by
  simpa [w] using Case2.w_in_rectangle

lemma a_below_support : BelowSupport a := by
  simp only [BelowSupport, a, point_apply_one]
  nlinarith [sqrtThree_pos]

lemma b_below_support : BelowSupport b := by
  simpa [b] using Case2.b_below_support

lemma v_below_support : BelowSupport v := by
  simpa [v] using Case2.v_below_support

lemma w_below_support : BelowSupport w := by
  simpa [w] using Case2.w_below_support

lemma u_within_two_v : WithinTwoUnitEdges Case2.u v := by
  simpa [v] using Case2.u_within_two_v

lemma u_within_two_w : WithinTwoUnitEdges Case2.u w := by
  simpa [w] using Case2.u_within_two_w

lemma u_within_two_b : WithinTwoUnitEdges Case2.u b := by
  simpa [b] using Case2.u_within_two_b

lemma u_within_two_a : WithinTwoUnitEdges Case2.u a := by
  exact Or.inr ⟨v, Case2.dist_u_v, dist_v_a⟩

/-- The two common unit neighbors of the Case 4 pair `v,w` are exactly
`a,b`. -/
lemma eq_a_or_b_of_unit_to_v_w {x : Point}
    (hxv : dist x v = 1) (hxw : dist x w = 1) :
    x = a ∨ x = b := by
  have hv := congrArg (fun t : ℝ ↦ t ^ 2) hxv
  have hw := congrArg (fun t : ℝ ↦ t ^ 2) hxw
  rw [dist_sq_eq_coordinates] at hv hw
  simp only [v, w, Case2.v, Case2.w, point_apply_zero, point_apply_one, one_pow] at hv hw
  have hline : x 0 - sqrtThree * x 1 = 2 := by
    nlinarith [sqrtThree_sq]
  have hsy : sqrtThree * x 1 = x 0 - 2 := by linarith
  have hsySq := congrArg (fun t : ℝ ↦ t ^ 2) hsy
  rw [mul_pow, sqrtThree_sq] at hsySq
  have hfactor : (x 0 + 1) * (2 * x 0 - 1) = 0 := by
    nlinarith [hv, hsySq]
  rcases mul_eq_zero.mp hfactor with hx | hx
  · left
    have hx0 : x 0 = -1 := by linarith
    have hx1 : x 1 = -sqrtThree := by
      apply (mul_left_cancel₀ sqrtThree_ne_zero)
      rw [hsy, hx0]
      nlinarith [sqrtThree_sq]
    exact point_ext hx0 hx1
  · right
    have hx0 : x 0 = (1 / 2 : ℝ) := by linarith
    have hx1 : x 1 = -(sqrtThree / 2) := by
      apply (mul_left_cancel₀ sqrtThree_ne_zero)
      rw [hsy, hx0]
      nlinarith [sqrtThree_sq]
    exact point_ext hx0 hx1

/-- The support of the Case 4 transfer.  The natural-number inputs are the
degrees of the middle point and its selected lowest neighbor. -/
noncomputable def recipientSet (degreeV degreeW : ℕ) : Finset Point :=
  if degreeV ≤ 4 then {v}
  else if degreeW ≤ 5 then {v, w}
  else {v, a, b}

lemma mem_recipientSet_geometry {degreeV degreeW : ℕ} {x : Point}
    (hx : x ∈ recipientSet degreeV degreeW) :
    InTransferRectangle x ∧ BelowSupport x ∧ WithinTwoUnitEdges Case2.u x := by
  change x ∈ (if degreeV ≤ 4 then {v}
    else if degreeW ≤ 5 then {v, w} else {v, a, b}) at hx
  split_ifs at hx
  · simp only [Finset.mem_singleton] at hx
    subst x
    exact ⟨v_in_rectangle, v_below_support, u_within_two_v⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨v_in_rectangle, v_below_support, u_within_two_v⟩
    · exact ⟨w_in_rectangle, w_below_support, u_within_two_w⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨v_in_rectangle, v_below_support, u_within_two_v⟩
    · exact ⟨a_in_rectangle, a_below_support, u_within_two_a⟩
    · exact ⟨b_in_rectangle, b_below_support, u_within_two_b⟩

end Case4

end Erdos957Cases24

