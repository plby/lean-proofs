import ErdosProblems.Erdos957.TwoExtremeIncidence

/-!
# Aligned two-extreme charts for Erdős 957

This leaf module supplies the successor-side analogue of the incoming-edge
chart used by Cases 2 and 4.  It keeps the current source at the canonical
origin, sends its successor to `(-1,0)`, and preserves the supporting
half-plane below the horizontal axis.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957TwoExtremeAligned

open Erdos957GeometryCore
open Erdos957Case24Bridge.Framed

abbrev Point := Erdos957GeometryCore.Point

/-- Reflection in the vertical line `x = -1/2`.  It swaps the canonical
edge endpoints `(-1,0)` and `(0,0)` and fixes the vertical coordinate. -/
def swapEndpointCoord (z : Point) : Point :=
  Erdos957Cases24.point (-z 0 - 1) (z 1)

@[simp] theorem swapEndpointCoord_apply_zero (z : Point) :
    swapEndpointCoord z 0 = -z 0 - 1 := by
  simp [swapEndpointCoord]

@[simp] theorem swapEndpointCoord_apply_one (z : Point) :
    swapEndpointCoord z 1 = z 1 := by
  simp [swapEndpointCoord]

@[simp] theorem swapEndpointCoord_involutive (z : Point) :
    swapEndpointCoord (swapEndpointCoord z) = z := by
  ext j
  fin_cases j <;> simp [swapEndpointCoord]

/-- The endpoint-swapping reflection as an honest equivalence. -/
def swapEndpointEquiv : Point ≃ Point where
  toFun := swapEndpointCoord
  invFun := swapEndpointCoord
  left_inv := swapEndpointCoord_involutive
  right_inv := swapEndpointCoord_involutive

@[simp] theorem swapEndpointEquiv_apply (z : Point) :
    swapEndpointEquiv z = swapEndpointCoord z := rfl

@[simp] theorem swapEndpointEquiv_symm_apply (z : Point) :
    swapEndpointEquiv.symm z = swapEndpointCoord z := rfl

theorem dist_swapEndpointCoord (p q : Point) :
    dist (swapEndpointCoord p) (swapEndpointCoord q) = dist p q := by
  have hsq := Erdos957Cases24.dist_sq_eq_coordinates p q
  have hsq' := Erdos957Cases24.dist_sq_eq_coordinates
    (swapEndpointCoord p) (swapEndpointCoord q)
  simp only [swapEndpointCoord_apply_zero, swapEndpointCoord_apply_one] at hsq'
  have heq : dist (swapEndpointCoord p) (swapEndpointCoord q) ^ 2 =
      dist p q ^ 2 := by
    rw [hsq', hsq]
    ring
  nlinarith [dist_nonneg (x := swapEndpointCoord p)
    (y := swapEndpointCoord q), dist_nonneg (x := p) (y := q)]

/-- At a source `i`, normalize the successor edge but reflect the horizontal
coordinate.  Thus `i` is canonical `u=(0,0)`, `next i` is canonical
`uPrev=(-1,0)`, and the supporting side remains `y≤0`. -/
def reflectedSuccessorUnitEdgeRigidChart {A : Finset Point}
    (P : CyclicHullData A) (source : {p // p ∈ P.H})
    (hunit : dist (source.1.1 : Point) (P.next source).1.1 = 1) :
    RigidChart :=
  let T := Erdos957EdgeFrame.terminalUnitEdgeRigidChart
    source.1.1 (P.next source).1.1 hunit
  { toCanonical := T.toCanonical.trans swapEndpointEquiv
    dist_eq := by
      intro p q
      change dist (swapEndpointCoord (T.toCanonical p))
        (swapEndpointCoord (T.toCanonical q)) = dist p q
      rw [dist_swapEndpointCoord, T.dist_eq] }

/-- Explicit coordinate formula: horizontal reflection of the ordinary
successor-edge chart, with the same supporting-height coordinate. -/
theorem reflectedSuccessorUnitEdgeRigidChart_toCanonical
    {A : Finset Point} (P : CyclicHullData A)
    (source : {p // p ∈ P.H})
    (hunit : dist (source.1.1 : Point) (P.next source).1.1 = 1)
    (q : Point) :
    let z := Erdos957EdgeFrame.edgePointCoord source.1.1
      ((P.next source).1.1 - source.1.1) q
    (reflectedSuccessorUnitEdgeRigidChart P source hunit).toCanonical q =
      Erdos957Cases24.point (-z 0) (z 1) := by
  have he := Erdos957EdgeFrame.coordinate_sq_sum_eq_one_of_dist_eq_one hunit
  dsimp [reflectedSuccessorUnitEdgeRigidChart]
  apply Erdos957Cases24.point_ext
  · simp only [Equiv.trans_apply, swapEndpointEquiv_apply,
      swapEndpointCoord_apply_zero,
      Erdos957EdgeFrame.terminalUnitEdgeRigidChart_toCanonical,
      Erdos957EdgeFrame.edgePointCoord_apply_zero,
      Erdos957EdgeFrame.edgePairCoord, PiLp.sub_apply,
      Erdos957Cases24.point_apply_zero]
    nlinarith
  · simp only [Equiv.trans_apply, swapEndpointEquiv_apply,
      swapEndpointCoord_apply_one,
      Erdos957EdgeFrame.terminalUnitEdgeRigidChart_toCanonical,
      Erdos957EdgeFrame.edgePointCoord_apply_one,
      Erdos957EdgeFrame.edgePairCoord, PiLp.sub_apply,
      Erdos957Cases24.point_apply_one]
    ring

@[simp] theorem reflectedSuccessorUnitEdgeRigidChart_actual_case2_u
    {A : Finset Point} (P : CyclicHullData A)
    (source : {p // p ∈ P.H})
    (hunit : dist (source.1.1 : Point) (P.next source).1.1 = 1) :
    (reflectedSuccessorUnitEdgeRigidChart P source hunit).actual
      Erdos957Cases24.Case2.u = source.1.1 := by
  let F := reflectedSuccessorUnitEdgeRigidChart P source hunit
  apply F.toCanonical.injective
  rw [F.toCanonical_actual]
  have hformula := reflectedSuccessorUnitEdgeRigidChart_toCanonical
    P source hunit source.1.1
  simp only [Erdos957EdgeFrame.edgePointCoord,
    Erdos957EdgeFrame.edgePairCoord_self, Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one, neg_zero] at hformula
  change Erdos957Cases24.point 0 0 = F.toCanonical source.1.1
  simpa [F] using hformula.symm

@[simp] theorem reflectedSuccessorUnitEdgeRigidChart_actual_case2_uPrev
    {A : Finset Point} (P : CyclicHullData A)
    (source : {p // p ∈ P.H})
    (hunit : dist (source.1.1 : Point) (P.next source).1.1 = 1) :
    (reflectedSuccessorUnitEdgeRigidChart P source hunit).actual
      Erdos957Cases24.Case2.uPrev = (P.next source).1.1 := by
  let F := reflectedSuccessorUnitEdgeRigidChart P source hunit
  apply F.toCanonical.injective
  rw [F.toCanonical_actual]
  have hterminal := Erdos957EdgeFrame.edgePairCoord_terminal hunit
  have hformula := reflectedSuccessorUnitEdgeRigidChart_toCanonical
    P source hunit (P.next source).1.1
  simp only [Erdos957EdgeFrame.edgePointCoord_apply_zero,
    Erdos957EdgeFrame.edgePointCoord_apply_one] at hformula
  rw [hterminal] at hformula
  simpa [F, Erdos957Cases24.Case2.uPrev] using hformula.symm

/-- A common unit neighbor of the current source and its successor is the
same canonical lower equilateral point `Case2.v` in the reflected chart. -/
theorem reflectedSuccessorUnitEdgeRigidChart_toCanonical_middle_eq_case2_v
    {A : Finset Point} (P : CyclicHullData A)
    (source : {p // p ∈ P.H}) (middle : Vertex A)
    (hunit : dist (source.1.1 : Point) (P.next source).1.1 = 1)
    (hsourceMiddle : (unitDistanceGraph A).Adj source.1 middle)
    (hnextMiddle : (unitDistanceGraph A).Adj (P.next source).1 middle) :
    (reflectedSuccessorUnitEdgeRigidChart P source hunit).toCanonical middle =
      Erdos957Cases24.Case2.v := by
  let F := reflectedSuccessorUnitEdgeRigidChart P source hunit
  have hFo : F.toCanonical source.1.1 = Erdos957Cases24.Case2.u := by
    rw [← reflectedSuccessorUnitEdgeRigidChart_actual_case2_u P source hunit,
      F.toCanonical_actual]
  have hFn : F.toCanonical (P.next source).1.1 =
      Erdos957Cases24.Case2.uPrev := by
    rw [← reflectedSuccessorUnitEdgeRigidChart_actual_case2_uPrev P source hunit,
      F.toCanonical_actual]
  have hdistO : dist (F.toCanonical middle) Erdos957Cases24.Case2.u = 1 := by
    rw [← hFo, F.dist_eq]
    change dist (source.1.1 : Point) middle = 1 at hsourceMiddle
    simpa [dist_comm] using hsourceMiddle
  have hdistN : dist (F.toCanonical middle)
      Erdos957Cases24.Case2.uPrev = 1 := by
    rw [← hFn, F.dist_eq]
    change dist ((P.next source).1.1 : Point) middle = 1 at hnextMiddle
    simpa [dist_comm] using hnextMiddle
  have hy : (F.toCanonical middle) 1 ≤ 0 := by
    have hs := P.edge_support source middle
    have hformula := reflectedSuccessorUnitEdgeRigidChart_toCanonical
      P source hunit (middle : Point)
    rw [hformula]
    simp only [Erdos957Cases24.point_apply_one,
      Erdos957EdgeFrame.edgePointCoord_apply_one,
      Erdos957EdgeFrame.edgePairCoord, PiLp.sub_apply]
    simp only [cross, PiLp.sub_apply] at hs
    linarith
  have hdistOSq := congrArg (fun x : ℝ ↦ x ^ 2) hdistO
  have hdistNSq := congrArg (fun x : ℝ ↦ x ^ 2) hdistN
  rw [Erdos957Cases24.dist_sq_eq_coordinates] at hdistOSq hdistNSq
  norm_num at hdistOSq hdistNSq
  apply Erdos957Cases24.point_ext
  · simp only [Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one]
      at hdistOSq hdistNSq
    simp only [Erdos957Cases24.Case2.v,
      Erdos957Cases24.point_apply_zero]
    nlinarith
  · simp only [Erdos957Cases24.Case2.u, Erdos957Cases24.Case2.uPrev,
      Erdos957Cases24.point_apply_zero, Erdos957Cases24.point_apply_one]
      at hdistOSq hdistNSq
    simp only [Erdos957Cases24.Case2.v,
      Erdos957Cases24.point_apply_one]
    nlinarith [Erdos957Cases24.sqrtThree_pos,
      Erdos957Cases24.sqrtThree_sq]

/-- The reflected successor chart has strict support away from its two
canonical edge endpoints.  This is transported from the already checked
terminal-edge theorem at `next source` through `swapEndpointCoord`. -/
theorem reflectedSuccessorUnitEdgeRigidChart_strictlyBelowOutside
    {A : Finset Point} (hA : IsOneSeparated A)
    (P : CyclicHullData A) (source : {p // p ∈ P.H})
    (hunit : dist (source.1.1 : Point) (P.next source).1.1 = 1) :
    let F := reflectedSuccessorUnitEdgeRigidChart P source hunit
    Erdos957Case24Bridge.StrictlyBelowOutside (F.image A)
      {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u} := by
  let nextSource := P.next source
  have hprev : P.next⁻¹ nextSource = source := by simp [nextSource]
  have hterminalUnit :
      dist ((P.next⁻¹ nextSource).1.1 : Point) nextSource.1.1 = 1 := by
    simpa [hprev, nextSource] using hunit
  let T := Erdos957EdgeFrame.terminalUnitEdgeRigidChart
    source.1.1 nextSource.1.1 hunit
  let F := reflectedSuccessorUnitEdgeRigidChart P source hunit
  have hstrict :=
    Erdos957TwoExtremeIncidence.terminalUnitEdgeRigidChart_strictlyBelowOutside
      hA P nextSource hterminalUnit
  change Erdos957Case24Bridge.StrictlyBelowOutside (F.image A)
    {Erdos957Cases24.Case2.uPrev, Erdos957Cases24.Case2.u}
  intro z hzF hzEndpoints
  have hactual : F.actual z = T.actual (swapEndpointCoord z) := by
    apply F.toCanonical.injective
    rw [F.toCanonical_actual]
    change z = swapEndpointCoord (T.toCanonical (T.actual (swapEndpointCoord z)))
    rw [T.toCanonical_actual, swapEndpointCoord_involutive]
  have hswapMem : swapEndpointCoord z ∈ T.image A := by
    rw [T.mem_image_iff, ← hactual]
    exact F.mem_image_iff.mp hzF
  have hswapMem' : swapEndpointCoord z ∈
      (Erdos957EdgeFrame.terminalUnitEdgeRigidChart
        (P.next⁻¹ nextSource).1.1 nextSource.1.1 hterminalUnit).image A := by
    simpa [T, hprev, nextSource] using hswapMem
  have hswapEndpoints : swapEndpointCoord z ∉
      ({Erdos957Cases24.Case2.uPrev,
        Erdos957Cases24.Case2.u} : Finset Point) := by
    intro hmem
    apply hzEndpoints
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem ⊢
    rcases hmem with h | h
    · right
      rw [← swapEndpointCoord_involutive z, h]
      apply Erdos957Cases24.point_ext <;>
        simp [swapEndpointCoord, Erdos957Cases24.Case2.uPrev,
          Erdos957Cases24.Case2.u]
    · left
      rw [← swapEndpointCoord_involutive z, h]
      apply Erdos957Cases24.point_ext <;>
        simp [swapEndpointCoord, Erdos957Cases24.Case2.uPrev,
          Erdos957Cases24.Case2.u]
  have hT : (swapEndpointCoord z) 1 < 0 := by
    exact hstrict (swapEndpointCoord z) hswapMem' hswapEndpoints
  simpa using hT

end Erdos957TwoExtremeAligned
