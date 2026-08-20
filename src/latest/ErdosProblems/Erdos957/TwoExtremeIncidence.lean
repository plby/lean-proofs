import ErdosProblems.Erdos957.TwoExtremeFrame
import ErdosProblems.Erdos957.EdgeFrame

/-!
# Canonical incidence from the two-extreme frame

This module identifies the common unit neighbor in the terminal chart of an
incoming unit hull edge.  Hull support chooses the lower of the two possible
equilateral points.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957TwoExtremeIncidence

open Erdos957GeometryCore

abbrev Point := Erdos957GeometryCore.Point

/-- In the terminal rigid chart of an incoming unit hull edge, a common unit
neighbor of its endpoints is literally the canonical Case-2 point `v`.
The supporting-edge inequality selects the negative-square-root branch. -/
theorem terminalUnitEdgeRigidChart_toCanonical_middle_eq_case2_v
    {A : Finset Point} (P : CyclicHullData A)
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (hunit : dist ((P.next⁻¹ source).1.1 : Point) source.1.1 = 1)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hprevMiddle : (unitDistanceGraph A).Adj (P.next⁻¹ source).1 middle) :
    (Erdos957EdgeFrame.terminalUnitEdgeRigidChart
      (P.next⁻¹ source).1.1 source.1.1 hunit).toCanonical middle =
        Erdos957Cases24.Case2.v := by
  let p : Point := (P.next⁻¹ source).1.1
  let o : Point := source.1.1
  let F := Erdos957EdgeFrame.terminalUnitEdgeRigidChart p o hunit
  have hnextPrev : P.next (P.next⁻¹ source) = source := by simp
  have hsupport := P.edge_support (P.next⁻¹ source) middle
  rw [hnextPrev] at hsupport
  have hFo : F.toCanonical o = Erdos957Cases24.Case2.u := by
    have ho : F.actual Erdos957Cases24.Case2.u = o := by
      simpa [F] using
      (Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_u p o hunit)
    rw [← ho, F.toCanonical_actual]
  have hFp : F.toCanonical p = Erdos957Cases24.Case2.uPrev := by
    have hp : F.actual Erdos957Cases24.Case2.uPrev = p := by
      simpa [F] using
      (Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_uPrev p o hunit)
    rw [← hp, F.toCanonical_actual]
  have hdistO : dist (F.toCanonical middle) Erdos957Cases24.Case2.u = 1 := by
    rw [← hFo, F.dist_eq]
    change dist (source.1.1 : Point) middle = 1 at hsourceMiddle
    simpa [o, dist_comm] using hsourceMiddle
  have hdistP : dist (F.toCanonical middle) Erdos957Cases24.Case2.uPrev = 1 := by
    rw [← hFp, F.dist_eq]
    change dist ((P.next⁻¹ source).1.1 : Point) middle = 1 at hprevMiddle
    simpa [p, dist_comm] using hprevMiddle
  have hy : (F.toCanonical middle) 1 ≤ 0 := by
    change (Erdos957EdgeFrame.edgePointCoord o (o - p) middle) 1 ≤ 0
    rw [Erdos957EdgeFrame.edgePointCoord_apply_one]
    simp only [Erdos957EdgeFrame.edgePairCoord, WithLp.ofLp_sub, Pi.sub_apply]
    simp only [cross, WithLp.ofLp_sub, Pi.sub_apply] at hsupport
    dsimp [p, o] at hsupport ⊢
    nlinarith
  have hdistOSq := congrArg (fun x : ℝ ↦ x ^ 2) hdistO
  have hdistPSq := congrArg (fun x : ℝ ↦ x ^ 2) hdistP
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hdistOSq hdistPSq
  norm_num at hdistOSq hdistPSq
  apply Erdos957Cases24.point_ext
  · simp only [Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one]
      at hdistOSq hdistPSq
    simp only [Erdos957Cases24.Case2.v,
      Erdos957Cases24.point_apply_zero]
    nlinarith
  · simp only [Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one]
      at hdistOSq hdistPSq
    simp only [Erdos957Cases24.Case2.v,
      Erdos957Cases24.point_apply_one]
    have hsqrtPos : 0 < Erdos957Cases24.sqrtThree :=
      Erdos957Cases24.sqrtThree_pos
    have hsqrtSq : Erdos957Cases24.sqrtThree ^ 2 = 3 :=
      Erdos957Cases24.sqrtThree_sq
    nlinarith

/-! ## Strict support of the terminal unit-edge chart -/

/-- A rigid motion preserves the elementary obstruction that an extreme
point cannot lie in the relative interior of a segment joining two
configuration points.  This is the only convexity input needed to upgrade
closed supporting-edge containment to strict containment below a unit hull
edge. -/
private lemma actual_right_not_mem_of_middle_extreme
    {A : Finset Point} (F : Erdos957Case24Bridge.Framed.RigidChart)
    {left middle right : Erdos957Cases24.Point}
    (hleft : F.actual left ∈ A)
    (hmiddleExtreme : F.actual middle ∈
      (convexHull ℝ (A : Set Point)).extremePoints ℝ)
    (hsum : dist left middle + dist middle right = dist left right)
    (hleftNe : left ≠ middle) (hrightNe : right ≠ middle) :
    F.actual right ∉ A := by
  intro hright
  have hsegment : F.actual middle ∈
      segment ℝ (F.actual left) (F.actual right) := by
    rw [mem_segment_iff_wbtw, ← dist_add_dist_eq_iff]
    simpa only [F.dist_actual] using hsum
  have hleftHull : F.actual left ∈ convexHull ℝ (A : Set Point) :=
    subset_convexHull ℝ (A : Set Point) hleft
  have hrightHull : F.actual right ∈ convexHull ℝ (A : Set Point) :=
    subset_convexHull ℝ (A : Set Point) hright
  have hend := (mem_extremePoints_iff_forall_segment.mp hmiddleExtreme).2
    (F.actual left) hleftHull (F.actual right) hrightHull hsegment
  rcases hend with h | h
  · exact hleftNe (F.actual_injective h)
  · exact hrightNe (F.actual_injective h)

/-- The terminal chart of a consecutive unit hull edge sends every other
configuration point strictly below the canonical support line.  Closed
edge support first gives height at most zero.  At height zero,
one-separation puts the point beyond one endpoint of the unit segment,
contradicting extremality of that endpoint. -/
theorem terminalUnitEdgeRigidChart_strictlyBelowOutside
    {A : Finset Point} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (source : {p // p ∈ P.H})
    (hunit : dist ((P.next⁻¹ source).1.1 : Point)
      (source.1.1 : Point) = 1) :
    let F := Erdos957EdgeFrame.terminalUnitEdgeRigidChart
      (P.next⁻¹ source).1.1 source.1.1 hunit
    Erdos957Case24Bridge.StrictlyBelowOutside (F.image A)
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u} := by
  let p : Point := (P.next⁻¹ source).1.1
  let o : Point := source.1.1
  let F := Erdos957EdgeFrame.terminalUnitEdgeRigidChart p o hunit
  have hpA : F.actual Erdos957Cases24.Case2.uPrev ∈ A := by
    rw [Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_uPrev]
    exact (P.next⁻¹ source).1.property
  have hoA : F.actual Erdos957Cases24.Case2.u ∈ A := by
    rw [Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_u]
    exact source.1.property
  have hpExtreme : F.actual Erdos957Cases24.Case2.uPrev ∈
      (convexHull ℝ (A : Set Point)).extremePoints ℝ := by
    rw [Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_uPrev]
    exact (P.hull_exact (P.next⁻¹ source).1).mp (P.next⁻¹ source).property
  have hoExtreme : F.actual Erdos957Cases24.Case2.u ∈
      (convexHull ℝ (A : Set Point)).extremePoints ℝ := by
    rw [Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_u]
    exact (P.hull_exact source.1).mp source.property
  have hsep := F.image_oneSeparated hA
  change Erdos957Case24Bridge.StrictlyBelowOutside (F.image A)
    {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u}
  intro z hzB hzBoundary
  have hzA : F.actual z ∈ A := F.mem_image_iff.mp hzB
  let q : Vertex A := ⟨F.actual z, hzA⟩
  have hyLe : z 1 ≤ 0 := by
    have hs := P.edge_support (P.next⁻¹ source) q
    have hnext : P.next (P.next⁻¹ source) = source := by simp
    rw [hnext] at hs
    have hs' : 0 ≤ cross (o - p) (F.actual z - o) := by
      change 0 ≤ cross (o - p) (F.actual z - p) at hs
      simp only [cross, PiLp.sub_apply] at hs ⊢
      nlinarith
    rw [← F.toCanonical_actual z,
      Erdos957EdgeFrame.terminalUnitEdgeRigidChart_toCanonical,
      Erdos957EdgeFrame.edgePointCoord_apply_one]
    simp only [Erdos957EdgeFrame.edgePairCoord, PiLp.sub_apply]
    simp only [cross, PiLp.sub_apply] at hs'
    nlinarith
  refine lt_of_le_of_ne hyLe ?_
  intro hyZero
  have hzNePrev : z ≠ Erdos957Cases24.Case2.uPrev := by
    intro h
    apply hzBoundary
    simp [h]
  have hzNeU : z ≠ Erdos957Cases24.Case2.u := by
    intro h
    apply hzBoundary
    simp [h]
  have hsepU : 1 ≤ dist z Erdos957Cases24.Case2.u :=
    hsep z hzB Erdos957Cases24.Case2.u
      (F.mem_image_iff.mpr hoA) hzNeU
  have hsepPrev : 1 ≤ dist z Erdos957Cases24.Case2.uPrev :=
    hsep z hzB Erdos957Cases24.Case2.uPrev
      (F.mem_image_iff.mpr hpA) hzNePrev
  have hsepUSq : 1 ≤ dist z Erdos957Cases24.Case2.u ^ 2 := by
    nlinarith [dist_nonneg (x := z) (y := Erdos957Cases24.Case2.u)]
  have hsepPrevSq : 1 ≤ dist z Erdos957Cases24.Case2.uPrev ^ 2 := by
    nlinarith [dist_nonneg (x := z) (y := Erdos957Cases24.Case2.uPrev)]
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hsepUSq hsepPrevSq
  simp only [Erdos957Cases24.Case2.u,
    Erdos957Cases24.Case2.uPrev, Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one] at hsepUSq hsepPrevSq
  have hxNeNegOne : z 0 ≠ -1 := by
    intro hx
    apply hzNePrev
    apply Erdos957Cases24.point_ext
    · simpa [Erdos957Cases24.Case2.uPrev] using hx
    · simpa [Erdos957Cases24.Case2.uPrev] using hyZero
  by_cases hxNonneg : 0 ≤ z 0
  · have hxOne : 1 ≤ z 0 := by
      nlinarith [sq_nonneg (z 0 - 1)]
    have huSq := Erdos957Cases24.dist_sq_eq_coordinates
      Erdos957Cases24.Case2.u z
    have hpSq := Erdos957Cases24.dist_sq_eq_coordinates
      Erdos957Cases24.Case2.uPrev z
    have huNonneg := dist_nonneg (x := Erdos957Cases24.Case2.u) (y := z)
    have hpNonneg := dist_nonneg (x := Erdos957Cases24.Case2.uPrev) (y := z)
    rw [hyZero] at huSq hpSq
    simp only [Erdos957Cases24.Case2.u,
      Erdos957Cases24.Case2.uPrev, Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one] at huSq hpSq
    have huSq' : dist Erdos957Cases24.Case2.u z ^ 2 = (z 0) ^ 2 := by
      calc
        _ = (0 - z 0) ^ 2 + (0 - 0) ^ 2 := huSq
        _ = _ := by ring
    have hpSq' : dist Erdos957Cases24.Case2.uPrev z ^ 2 =
        (z 0 + 1) ^ 2 := by
      calc
        _ = (-1 - z 0) ^ 2 + (0 - 0) ^ 2 := hpSq
        _ = _ := by ring
    have huDist : dist Erdos957Cases24.Case2.u z = z 0 := by
      apply (sq_eq_sq₀ huNonneg hxNonneg).mp
      exact huSq'
    have hpDist : dist Erdos957Cases24.Case2.uPrev z = z 0 + 1 := by
      apply (sq_eq_sq₀ hpNonneg (by linarith : 0 ≤ z 0 + 1)).mp
      exact hpSq'
    have hsum : dist Erdos957Cases24.Case2.uPrev
        Erdos957Cases24.Case2.u +
        dist Erdos957Cases24.Case2.u z =
        dist Erdos957Cases24.Case2.uPrev z := by
      rw [Erdos957Cases24.Case2.dist_uPrev_u, huDist, hpDist]
      ring
    exact actual_right_not_mem_of_middle_extreme F hpA hoExtreme hsum
      (by norm_num [Erdos957Cases24.Case2.uPrev,
        Erdos957Cases24.Case2.u, Erdos957Cases24.point_inj])
      hzNeU hzA
  · have hxNeg : z 0 < 0 := lt_of_not_ge hxNonneg
    have hxLeNegOne : z 0 ≤ -1 := by
      nlinarith [sq_nonneg (z 0 + 1)]
    have hxLtNegOne : z 0 < -1 := lt_of_le_of_ne hxLeNegOne hxNeNegOne
    have hxLeNegTwo : z 0 ≤ -2 := by
      nlinarith [sq_nonneg (z 0 + 2)]
    have hpSq := Erdos957Cases24.dist_sq_eq_coordinates z
      Erdos957Cases24.Case2.uPrev
    have huSq := Erdos957Cases24.dist_sq_eq_coordinates z
      Erdos957Cases24.Case2.u
    have hpNonneg := dist_nonneg (x := z)
      (y := Erdos957Cases24.Case2.uPrev)
    have huNonneg := dist_nonneg (x := z)
      (y := Erdos957Cases24.Case2.u)
    rw [hyZero] at hpSq huSq
    simp only [Erdos957Cases24.Case2.u,
      Erdos957Cases24.Case2.uPrev, Erdos957Cases24.point_apply_zero,
      Erdos957Cases24.point_apply_one] at hpSq huSq
    have hpSq' : dist z Erdos957Cases24.Case2.uPrev ^ 2 =
        (-(z 0 + 1)) ^ 2 := by
      calc
        _ = (z 0 - -1) ^ 2 + (0 - 0) ^ 2 := hpSq
        _ = _ := by ring
    have huSq' : dist z Erdos957Cases24.Case2.u ^ 2 = (-z 0) ^ 2 := by
      calc
        _ = (z 0 - 0) ^ 2 + (0 - 0) ^ 2 := huSq
        _ = _ := by ring
    have hpDist : dist z Erdos957Cases24.Case2.uPrev = -(z 0 + 1) := by
      apply (sq_eq_sq₀ hpNonneg (by linarith : 0 ≤ -(z 0 + 1))).mp
      exact hpSq'
    have huDist : dist z Erdos957Cases24.Case2.u = -(z 0) := by
      apply (sq_eq_sq₀ huNonneg (by linarith : 0 ≤ -z 0)).mp
      exact huSq'
    have hsum : dist Erdos957Cases24.Case2.u
        Erdos957Cases24.Case2.uPrev +
        dist Erdos957Cases24.Case2.uPrev z =
        dist Erdos957Cases24.Case2.u z := by
      rw [show dist Erdos957Cases24.Case2.u
          Erdos957Cases24.Case2.uPrev = 1 by
        simpa [dist_comm] using Erdos957Cases24.Case2.dist_uPrev_u,
        show dist Erdos957Cases24.Case2.uPrev z = -(z 0 + 1) by
          simpa [dist_comm] using hpDist,
        show dist Erdos957Cases24.Case2.u z = -z 0 by
          simpa [dist_comm] using huDist]
      ring
    exact actual_right_not_mem_of_middle_extreme F hoA hpExtreme hsum
      (by norm_num [Erdos957Cases24.Case2.u,
        Erdos957Cases24.Case2.uPrev, Erdos957Cases24.point_inj])
      hzNePrev hzA
/-! ## Degree-six regular-hexagon incidence -/

/-- The graph degree and the coordinate-file unit degree count the same
actual neighbors; only the membership proof carried by `Vertex` differs. -/
theorem graph_degree_eq_unitDegree {A : Finset Point} (v : Vertex A) :
    (unitDistanceGraph A).degree v =
      Erdos957Case24Bridge.unitDegree A (v : Point) := by
  classical
  rw [SimpleGraph.degree, Erdos957Case24Bridge.unitDegree]
  apply Finset.card_bij
    (s := (unitDistanceGraph A).neighborFinset v)
    (t := Erdos957Cases24.unitNeighbors A (v : Point))
    (fun w _ ↦ (w : Point))
  · intro w hw
    apply Erdos957Cases24.mem_unitNeighbors.mpr
    refine ⟨w.property, ?_⟩
    exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := v) w).mp hw
  · intro w _ z _ hwz
    exact Subtype.ext hwz
  · intro p hp
    let w : Vertex A := ⟨p, (Erdos957Cases24.mem_unitNeighbors.mp hp).1⟩
    refine ⟨w, ?_, rfl⟩
    exact (SimpleGraph.mem_neighborFinset
      (G := unitDistanceGraph A) (v := v) w).mpr
        (Erdos957Cases24.mem_unitNeighbors.mp hp).2

private lemma case2_v_add_u_sub_uPrev_eq_b :
    Erdos957Cases24.Case2.v + Erdos957Cases24.Case2.u -
      Erdos957Cases24.Case2.uPrev = Erdos957Cases24.Case2.b := by
  ext j
  fin_cases j <;>
    simp [Erdos957Cases24.Case2.v, Erdos957Cases24.Case2.u,
      Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.b]
  norm_num

private lemma case2_v_add_b_sub_u_eq_w :
    Erdos957Cases24.Case2.v + Erdos957Cases24.Case2.b -
      Erdos957Cases24.Case2.u = Erdos957Cases24.Case2.w := by
  ext j
  fin_cases j <;>
    simp [Erdos957Cases24.Case2.v, Erdos957Cases24.Case2.u,
      Erdos957Cases24.Case2.b, Erdos957Cases24.Case2.w]
  ring

private lemma case4_v_add_w_sub_b_eq_a :
    Erdos957Cases24.Case4.v + Erdos957Cases24.Case4.w -
      Erdos957Cases24.Case4.b = Erdos957Cases24.Case4.a := by
  ext j
  fin_cases j <;>
    simp [Erdos957Cases24.Case4.v, Erdos957Cases24.Case4.w,
      Erdos957Cases24.Case4.b, Erdos957Cases24.Case4.a,
      Erdos957Cases24.Case2.v, Erdos957Cases24.Case2.w,
      Erdos957Cases24.Case2.b]
  ring

/-- In canonical coordinates, degree six at the common equilateral middle
forces the entire five-point Case-4 display by three successive regular-
hexagon completions. -/
theorem case4_displayedFiveAtV_subset_of_degree_six
    {B : Finset Erdos957Cases24.Point}
    (hsep : Erdos957Cases24.IsOneSeparated B)
    (huPrev : Erdos957Cases24.Case2.uPrev ∈ B)
    (hu : Erdos957Cases24.Case2.u ∈ B)
    (hdegree : Erdos957Case24Bridge.unitDegree B
      Erdos957Cases24.Case4.v = 6) :
    Erdos957Cases24.Case4.displayedFiveAtV ⊆ B := by
  have hb : Erdos957Cases24.Case4.b ∈ B := by
    change Erdos957Cases24.Case2.b ∈ B
    rw [← case2_v_add_u_sub_uPrev_eq_b]
    exact Erdos957Case24Bridge.hexagon_completion_mem hsep hu huPrev
      (by simpa [Erdos957Cases24.Case4.v, dist_comm] using
        Erdos957Cases24.Case2.dist_u_v)
      (by simpa [Erdos957Cases24.Case4.v, dist_comm] using
        Erdos957Cases24.Case2.dist_uPrev_v)
      (by simpa [dist_comm] using Erdos957Cases24.Case2.dist_uPrev_u) hdegree
  have hw : Erdos957Cases24.Case4.w ∈ B := by
    change Erdos957Cases24.Case2.w ∈ B
    rw [← case2_v_add_b_sub_u_eq_w]
    exact Erdos957Case24Bridge.hexagon_completion_mem hsep hb hu
      (by simpa [Erdos957Cases24.Case4.v, Erdos957Cases24.Case4.b]
        using Erdos957Cases24.Case2.dist_v_b)
      (by simpa [Erdos957Cases24.Case4.v, dist_comm]
        using Erdos957Cases24.Case2.dist_u_v)
      (by simpa [Erdos957Cases24.Case4.b, dist_comm] using
        Erdos957Cases24.Case2.dist_u_b) hdegree
  have ha : Erdos957Cases24.Case4.a ∈ B := by
    rw [← case4_v_add_w_sub_b_eq_a]
    exact Erdos957Case24Bridge.hexagon_completion_mem hsep hw hb
      (by simpa [Erdos957Cases24.Case4.v, Erdos957Cases24.Case4.w]
        using Erdos957Cases24.Case2.dist_v_w)
      (by simpa using Erdos957Cases24.Case4.dist_v_b)
      Erdos957Cases24.Case4.dist_w_b hdegree
  intro q hq
  simp only [Erdos957Cases24.Case4.displayedFiveAtV,
    Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact huPrev
  · exact hu
  · exact hb
  · exact hw
  · exact ha

/-- Actual-coordinate version of the preceding incidence theorem.  If the
common middle has degree six in the genuine unit-distance graph, then every
canonical point in the Case-4 display represents an actual point of `A`. -/
theorem actual_case4_displayedFiveAtV_of_middle_degree_six
    {A : Finset Point} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (source : {p // p ∈ P.H})
    (middle : Vertex A)
    (hunit : dist ((P.next⁻¹ source).1.1 : Point) source.1.1 = 1)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hprevMiddle : (unitDistanceGraph A).Adj (P.next⁻¹ source).1 middle)
    (hdegree : (unitDistanceGraph A).degree middle = 6) :
    let F := Erdos957EdgeFrame.terminalUnitEdgeRigidChart
      (P.next⁻¹ source).1.1 source.1.1 hunit
    ∀ q ∈ Erdos957Cases24.Case4.displayedFiveAtV, F.actual q ∈ A := by
  let p : Point := (P.next⁻¹ source).1.1
  let o : Point := source.1.1
  let F := Erdos957EdgeFrame.terminalUnitEdgeRigidChart p o hunit
  let B := F.image A
  have hmiddleCoord : F.toCanonical middle = Erdos957Cases24.Case2.v := by
    exact terminalUnitEdgeRigidChart_toCanonical_middle_eq_case2_v
      P source middle hunit hsourceMiddle hprevMiddle
  have hsepA : Erdos957Cases24.IsOneSeparated A := hA
  have hsepB : Erdos957Cases24.IsOneSeparated B := F.image_oneSeparated hsepA
  have huPrev : Erdos957Cases24.Case2.uPrev ∈ B := by
    apply F.mem_image_iff.mpr
    have hp : F.actual Erdos957Cases24.Case2.uPrev = p := by
      simpa [F] using
        (Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_uPrev
          p o hunit)
    rw [hp]
    exact (P.next⁻¹ source).1.property
  have hu : Erdos957Cases24.Case2.u ∈ B := by
    apply F.mem_image_iff.mpr
    have ho : F.actual Erdos957Cases24.Case2.u = o := by
      simpa [F] using
        (Erdos957EdgeFrame.terminalUnitEdgeRigidChart_actual_case2_u p o hunit)
    rw [ho]
    exact source.1.property
  have hdegreeActual : Erdos957Case24Bridge.unitDegree A (middle : Point) = 6 := by
    rw [← graph_degree_eq_unitDegree]
    exact hdegree
  have hdegreeB : Erdos957Case24Bridge.unitDegree B
      Erdos957Cases24.Case4.v = 6 := by
    change Erdos957Case24Bridge.unitDegree B Erdos957Cases24.Case2.v = 6
    rw [← hmiddleCoord]
    exact (F.unitDegree_image A middle).trans hdegreeActual
  have hdisplay := case4_displayedFiveAtV_subset_of_degree_six
    hsepB huPrev hu hdegreeB
  change ∀ q ∈ Erdos957Cases24.Case4.displayedFiveAtV, F.actual q ∈ A
  intro q hq
  exact F.mem_image_iff.mp (hdisplay hq)

end Erdos957TwoExtremeIncidence
