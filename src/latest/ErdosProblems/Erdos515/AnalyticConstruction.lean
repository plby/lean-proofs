/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.BoundaryAccess
import ErdosProblems.Erdos515.Construction
import ErdosProblems.Erdos515.Growth
import ErdosProblems.Erdos515.NestedDomains

/-!
# The concrete nested-domain recursion for Erdős Problem 515

This file performs the choice and bookkeeping which turn the analytic short-positive-path lemma
into one sequence of matching finite polygonal blocks.  The state at stage `k` is a point where
the control function is positive.  Consequently the recursive choice is total on its state type:
there is no fallback point and no artificial segment.

The genuinely analytic input is isolated in `LRWShortPathPrinciple`.  Its output is stated on the
actual component of the strict sublevel used by Lewis--Rossi--Weitsman and on the actual normalized
positive part of the control function.  `LRWBoundaryControl` records the boundary-distance estimate
proved separately by the Phragmén--Lindelöf argument.  The last theorem combines these two proved
inputs with the finite-block summability engine from `Construction`.
-/

open Filter Metric Set
open scoped ENNReal NNReal Topology

namespace Erdos515

/-- A point at which the LRW control function is positive. -/
structure PositiveControlPoint (u : ℂ → ℝ) where
  point : ℂ
  positive : 0 < u point

/-- A transcendental entire function has a point where `log⁺ |f|` is positive. -/
theorem exists_positiveControlPoint_logPosNorm {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (htrans : ¬ IsPolynomialFunction f) :
    Nonempty (PositiveControlPoint (logPosNorm f)) := by
  obtain ⟨r, hr, z, _hzr, hz⟩ :=
    (eventually_exists_norm_eq_posLog_ge hf htrans 1).exists
  refine ⟨⟨z, ?_⟩⟩
  rw [logPosNorm_eq_log_max]
  have hlog : 0 < Real.log r := Real.log_pos hr
  exact hlog.trans_le (by
    simpa [Real.posLog_eq_log_max_one (norm_nonneg (f z))] using hz)

/-- The positive logarithmic modulus of a transcendental entire function is unbounded above. -/
theorem logPosNorm_unbounded {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (htrans : ¬ IsPolynomialFunction f) :
    ∀ A : ℝ, ∃ z : ℂ, A ≤ logPosNorm f z := by
  intro A
  have hev := eventually_exists_norm_eq_posLog_ge hf htrans 1
  have her : ∀ᶠ r : ℝ in atTop, Real.exp A < r := eventually_gt_atTop (Real.exp A)
  obtain ⟨r, ⟨_hr1, z, _hzr, hz⟩, hr⟩ := (hev.and her).exists
  refine ⟨z, ?_⟩
  have hrpos : 0 < r := (Real.exp_pos A).trans hr
  have hAlog : A < Real.log r := by
    rw [← Real.exp_lt_exp, Real.exp_log hrpos]
    exact hr
  rw [logPosNorm_eq_log_max]
  exact hAlog.le.trans (by
    simpa [Real.posLog_eq_log_max_one (norm_nonneg (f z))] using hz)

/-- The level defining the domain at a positive state. -/
noncomputable def lrwLevel (delta : ℝ) (u : ℂ → ℝ) (a : PositiveControlPoint u) : ℝ :=
  u a.point / (1 - delta)

/-- The component, through the fixed initial point, of the stage sublevel. -/
noncomputable def lrwDomain (delta : ℝ) (u : ℂ → ℝ) (base : ℂ)
    (a : PositiveControlPoint u) : Set ℂ :=
  sublevelComponent u (lrwLevel delta u a) base

/-- The normalized positive part used in the LRW short-path lemma.

Positivity of this function is precisely the lower bound `delta * u(a) < u(z)` needed for the
inverse-modulus estimate. -/
noncomputable def lrwNormalizedControl (delta : ℝ) (u : ℂ → ℝ)
    (a : PositiveControlPoint u) (z : ℂ) : ℝ :=
  (u a.point)⁻¹ * max ((1 - delta) * (u z - delta * u a.point)) 0

/-- A fixed growth factor strictly between `1` and `(1-delta)⁻¹`. -/
noncomputable def lrwGrowthFactor (delta : ℝ) : ℝ :=
  (1 + (1 - delta)⁻¹) / 2

/-- A positive state which belongs to its own fixed-base LRW sublevel component. -/
structure LRWAdmissiblePoint (delta : ℝ) (u : ℂ → ℝ) (base : ℂ) where
  controlPoint : PositiveControlPoint u
  mem_domain : controlPoint.point ∈ lrwDomain delta u base controlPoint

lemma one_lt_lrwGrowthFactor {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    1 < lrwGrowthFactor delta := by
  have hinv : 1 < (1 - delta)⁻¹ := by
    rw [one_lt_inv₀ (sub_pos.mpr hdelta1)]
    linarith
  unfold lrwGrowthFactor
  linarith

lemma lrwGrowthFactor_lt_inv_one_sub {delta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    lrwGrowthFactor delta < (1 - delta)⁻¹ := by
  have hinv : 1 < (1 - delta)⁻¹ := by
    rw [one_lt_inv₀ (sub_pos.mpr hdelta1)]
    linarith
  unfold lrwGrowthFactor
  linarith

lemma positive_of_lrwNormalizedControl_pos {delta : ℝ} {u : ℂ → ℝ}
    {a : PositiveControlPoint u} {z : ℂ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hz : 0 < lrwNormalizedControl delta u a z) :
    delta * u a.point < u z := by
  unfold lrwNormalizedControl at hz
  have hmul := mul_pos_iff.mp hz
  have hmax : 0 < max ((1 - delta) * (u z - delta * u a.point)) 0 := by
    rcases hmul with hmul | hmul
    · exact hmul.2
    · exact False.elim ((not_lt_of_ge (inv_nonneg.mpr a.positive.le)) hmul.1)
  have hprod : 0 < (1 - delta) * (u z - delta * u a.point) := by
    by_contra hnot
    have hle : (1 - delta) * (u z - delta * u a.point) ≤ 0 := le_of_not_gt hnot
    rw [max_eq_right hle] at hmax
    exact (lt_irrefl 0) hmax
  rcases mul_pos_iff.mp hprod with hprod | hprod
  · linarith
  · exact False.elim ((not_lt_of_ge (sub_pos.mpr hdelta1).le) hprod.1)

/-- At an interior point of a proper open planar domain, distance to the frontier equals distance
to the complement. -/
lemma infDist_frontier_eq_infDist_compl {D : Set ℂ} (hDopen : IsOpen D)
    {x : ℂ} (hx : x ∈ D) (hDproper : D ≠ univ) :
    infDist x (frontier D) = infDist x Dᶜ := by
  have hfrontNonempty : (frontier D).Nonempty :=
    nonempty_frontier_iff.mpr ⟨⟨x, hx⟩, hDproper⟩
  have hfrontCompl : frontier D ⊆ Dᶜ := by
    intro z hz hzD
    have hzBoth : z ∈ D ∩ frontier D := ⟨hzD, hz⟩
    rw [hDopen.inter_frontier_eq] at hzBoth
    exact hzBoth
  apply le_antisymm
  · obtain ⟨z, hzfront, hzdist⟩ :=
      exists_mem_frontier_infDist_compl_eq_dist hx hDproper
    exact (infDist_le_dist_of_mem hzfront).trans_eq hzdist.symm
  · exact infDist_le_infDist_of_subset hfrontCompl hfrontNonempty

/-- For nested proper open domains containing the same point, the distance from that point to the
frontier is monotone. -/
lemma infDist_frontier_mono {D E : Set ℂ} (hDopen : IsOpen D) (hEopen : IsOpen E)
    {x : ℂ} (hxD : x ∈ D) (hxE : x ∈ E) (hDproper : D ≠ univ)
    (hEproper : E ≠ univ) (hDE : D ⊆ E) :
    infDist x (frontier D) ≤ infDist x (frontier E) := by
  rw [infDist_frontier_eq_infDist_compl hDopen hxD hDproper,
    infDist_frontier_eq_infDist_compl hEopen hxE hEproper]
  exact infDist_le_infDist_of_subset (compl_subset_compl.mpr hDE) (nonempty_compl.mpr hEproper)

/-- The endpoint of a finite positive polygonal arc belongs to its open domain. -/
lemma FinitePositivePolygonalArc.finish_mem {D : Set ℂ} {v : ℂ → ℝ} {a c : ℂ}
    (P : FinitePositivePolygonalArc D v a c) : c ∈ D := by
  let i := P.steps - 1
  have hi : i < P.steps := by
    have hsteps := P.steps_pos
    dsimp [i]
    omega
  have h := P.segment_mem i hi 1 (by simp)
  have hilast : i + 1 = P.steps := by
    have hsteps := P.steps_pos
    dsimp [i]
    omega
  have hpoint : P.vertex ⟨i + 1, Nat.succ_lt_succ hi⟩ = c := by
    calc
      P.vertex ⟨i + 1, Nat.succ_lt_succ hi⟩ =
          P.vertex ⟨P.steps, Nat.lt_succ_self P.steps⟩ := by
        congr 1
        exact Fin.ext hilast
      _ = c := P.finish
  simpa only [AffineMap.lineMap_apply, one_smul, vsub_vadd, hpoint] using h

namespace PolygonalArcToBoundary

/-- A nonempty finite prefix of a positive polygonal arc to the boundary. -/
noncomputable def finitePrefix {D : Set ℂ} {v : ℂ → ℝ} {a b : ℂ}
    (Q : PolygonalArcToBoundary D v a b) (N : ℕ) (hN : 0 < N) :
    FinitePositivePolygonalArc D v a (Q.vertex N) where
  steps := N
  steps_pos := hN
  vertex i := Q.vertex i
  start := Q.start
  finish := rfl
  segment_mem i hi t ht := Q.segment_mem i t ht
  segment_positive i hi t ht := Q.segment_positive i t ht

/-- Taking a finite prefix cannot increase the total polygonal length. -/
lemma finitePrefix_length_le {D : Set ℂ} {v : ℂ → ℝ} {a b : ℂ}
    (Q : PolygonalArcToBoundary D v a b) (N : ℕ) (hN : 0 < N) :
    (Q.finitePrefix N hN).length ≤ Q.length := by
  rw [FinitePositivePolygonalArc.length, PolygonalArcToBoundary.length]
  change (∑ i : Fin N, edist (Q.vertex i) (Q.vertex (i + 1))) ≤ _
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦ edist (Q.vertex i) (Q.vertex (i + 1))) N]
  exact ENNReal.sum_le_tsum (Finset.range N)

end PolygonalArcToBoundary

/-- One successful finite short-path step from an admissible positive state. -/
structure LRWStepOutput (u : ℂ → ℝ) (base : ℂ) (delta constant : ℝ)
    (a : LRWAdmissiblePoint delta u base) where
  next : PositiveControlPoint u
  growth : lrwGrowthFactor delta * u a.controlPoint.point ≤ u next.point
  arc : FinitePositivePolygonalArc (lrwDomain delta u base a.controlPoint)
    (lrwNormalizedControl delta u a.controlPoint) a.controlPoint.point next.point
  length_le : arc.length ≤ ENNReal.ofReal
    (constant * infDist a.controlPoint.point
      (frontier (lrwDomain delta u base a.controlPoint)))

namespace LRWStepOutput

/-- A finite LRW step obtained by truncating a finite-length positive arc when it approaches the
exact boundary level.  This separates the radial Hall--Prawitz construction, which naturally
produces a countable polygonal arc to the frontier, from the finite-block recursion. -/
theorem exists_of_arcToBoundary {u : ℂ → ℝ} {base : ℂ} {delta constant : ℝ}
    (hu : Continuous u) (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (a : LRWAdmissiblePoint delta u base) {b : ℂ}
    (Q : PolygonalArcToBoundary (lrwDomain delta u base a.controlPoint)
      (lrwNormalizedControl delta u a.controlPoint) a.controlPoint.point b)
    (hQlength : Q.length ≤ ENNReal.ofReal
      (constant * infDist a.controlPoint.point
        (frontier (lrwDomain delta u base a.controlPoint)))) :
    Nonempty (LRWStepOutput u base delta constant a) := by
  have hbLevel : u b = lrwLevel delta u a.controlPoint :=
    eq_level_of_mem_frontier_sublevelComponent hu Q.endpoint_mem_frontier
  have htarget : lrwGrowthFactor delta * u a.controlPoint.point < u b := by
    rw [hbLevel]
    unfold lrwLevel
    have hgrowth := lrwGrowthFactor_lt_inv_one_sub hdelta0 hdelta1
    have hmul := mul_lt_mul_of_pos_right hgrowth a.controlPoint.positive
    simpa only [div_eq_mul_inv, mul_comm] using hmul
  have htend : Tendsto (fun n ↦ u (Q.vertex n)) atTop (nhds (u b)) :=
    hu.continuousAt.tendsto.comp Q.tendsto_endpoint
  have hevTarget : ∀ᶠ n in atTop,
      lrwGrowthFactor delta * u a.controlPoint.point < u (Q.vertex n) :=
    (tendsto_order.1 htend).1 _ htarget
  obtain ⟨N, hNgrowth, hNone⟩ := (hevTarget.and (eventually_ge_atTop 1)).exists
  have hNpos : 0 < N := hNone
  have hnextPos : 0 < u (Q.vertex N) := by
    have hfactor : 0 < lrwGrowthFactor delta :=
      zero_lt_one.trans (one_lt_lrwGrowthFactor hdelta0 hdelta1)
    exact (mul_pos hfactor a.controlPoint.positive).trans hNgrowth
  refine ⟨{
    next := ⟨Q.vertex N, hnextPos⟩
    growth := hNgrowth.le
    arc := Q.finitePrefix N hNpos
    length_le := ?_ }⟩
  exact (Q.finitePrefix_length_le N hNpos).trans hQlength

/-- Endpoint growth and sublevel nesting make the endpoint admissible for the next stage. -/
noncomputable def nextAdmissible {u : ℂ → ℝ} {base : ℂ} {delta constant : ℝ}
    {a : LRWAdmissiblePoint delta u base} (O : LRWStepOutput u base delta constant a)
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    LRWAdmissiblePoint delta u base where
  controlPoint := O.next
  mem_domain := by
    have hnextOld : O.next.point ∈ lrwDomain delta u base a.controlPoint := O.arc.finish_mem
    apply sublevelComponent_mono base _ hnextOld
    unfold lrwLevel
    apply div_le_div_of_nonneg_right _ (sub_pos.mpr hdelta1).le
    exact ((le_mul_iff_one_le_left a.controlPoint.positive).2
      (one_lt_lrwGrowthFactor hdelta0 hdelta1).le).trans O.growth

end LRWStepOutput

/-- The exact high-level analytic result required by the recursive construction.

The Hall--Prawitz--Koebe argument supplies `delta` and `constant` once and for all.  The `step`
field then applies that same pair of constants at every positive state. -/
structure LRWShortPathPrinciple (u : ℂ → ℝ) (base : ℂ) where
  delta : ℝ
  constant : ℝ
  delta_pos : 0 < delta
  delta_lt_one : delta < 1
  constant_nonneg : 0 ≤ constant
  step : ∀ a : LRWAdmissiblePoint delta u base,
    Nonempty (LRWStepOutput u base delta constant a)

namespace LRWShortPathPrinciple

variable {u : ℂ → ℝ} {base : ℂ}

/-- The fixed base point is admissible for the first stage. -/
noncomputable def initialAdmissible (a : PositiveControlPoint u)
    (S : LRWShortPathPrinciple u a.point) :
    LRWAdmissiblePoint S.delta u a.point where
  controlPoint := a
  mem_domain := by
    apply mem_sublevelComponent_self
    unfold lrwLevel
    rw [div_eq_mul_inv]
    have hden : 0 < 1 - S.delta := sub_pos.mpr S.delta_lt_one
    have hinv : 1 < (1 - S.delta)⁻¹ := by
      rw [one_lt_inv₀ hden]
      linarith [S.delta_pos]
    exact lt_mul_of_one_lt_right a.positive hinv

/-- The chosen successful step at a state. -/
noncomputable def chosenStep (S : LRWShortPathPrinciple u base)
    (a : LRWAdmissiblePoint S.delta u base) : LRWStepOutput u base S.delta S.constant a :=
  Classical.choice (S.step a)

/-- The recursively chosen sequence of positive states. -/
noncomputable def state (S : LRWShortPathPrinciple u base)
    (initial : LRWAdmissiblePoint S.delta u base) : ℕ → LRWAdmissiblePoint S.delta u base
  | 0 => initial
  | k + 1 => (S.chosenStep (state S initial k)).nextAdmissible S.delta_pos S.delta_lt_one

@[simp] lemma state_zero (S : LRWShortPathPrinciple u base)
    (initial : LRWAdmissiblePoint S.delta u base) : S.state initial 0 = initial := rfl

@[simp] lemma state_succ (S : LRWShortPathPrinciple u base)
    (initial : LRWAdmissiblePoint S.delta u base) (k : ℕ) :
    (S.state initial (k + 1)).controlPoint =
      (S.chosenStep (S.state initial k)).next := rfl

/-- The actual stage domains of the recursively selected construction. -/
noncomputable def domain (S : LRWShortPathPrinciple u base)
    (initial : LRWAdmissiblePoint S.delta u base) (k : ℕ) : Set ℂ :=
  lrwDomain S.delta u base (S.state initial k).controlPoint

/-- The actual normalized controls of the recursively selected construction. -/
noncomputable def normalizedControl (S : LRWShortPathPrinciple u base)
    (initial : LRWAdmissiblePoint S.delta u base) (k : ℕ) : ℂ → ℝ :=
  lrwNormalizedControl S.delta u (S.state initial k).controlPoint

/-- The matching finite positive arcs obtained by dependent recursion. -/
noncomputable def matchingArcs (S : LRWShortPathPrinciple u base)
    (initial : LRWAdmissiblePoint S.delta u base) :
    MatchingFinitePositiveArcs (S.domain initial) (S.normalizedControl initial) where
  endpoint k := (S.state initial k).controlPoint.point
  arc k := (S.chosenStep (S.state initial k)).arc

@[simp] lemma matchingArcs_endpoint (S : LRWShortPathPrinciple u base)
    (initial : LRWAdmissiblePoint S.delta u base) (k : ℕ) :
    (S.matchingArcs initial).endpoint k = (S.state initial k).controlPoint.point := rfl

@[simp] lemma matchingArcs_arc (S : LRWShortPathPrinciple u base)
    (initial : LRWAdmissiblePoint S.delta u base) (k : ℕ) :
    (S.matchingArcs initial).arc k = (S.chosenStep (S.state initial k)).arc := rfl

lemma endpointGrowth (S : LRWShortPathPrinciple u base)
    (initial : LRWAdmissiblePoint S.delta u base) (k : ℕ) :
    lrwGrowthFactor S.delta * u ((S.matchingArcs initial).endpoint k) ≤
      u ((S.matchingArcs initial).endpoint (k + 1)) := by
  exact (S.chosenStep (S.state initial k)).growth

lemma arc_length_le (S : LRWShortPathPrinciple u base)
    (initial : LRWAdmissiblePoint S.delta u base) (k : ℕ) :
    ((S.matchingArcs initial).arc k).length ≤ ENNReal.ofReal
      (S.constant * infDist ((S.matchingArcs initial).endpoint k)
        (frontier (S.domain initial k))) := by
  exact (S.chosenStep (S.state initial k)).length_le

lemma segment_logPos_lower {f : ℂ → ℂ} (S : LRWShortPathPrinciple (logPosNorm f) base)
    (initial : LRWAdmissiblePoint S.delta (logPosNorm f) base) (k : ℕ) {z : ℂ}
    (hz : 0 < S.normalizedControl initial k z) :
    S.delta * logPosNorm f ((S.matchingArcs initial).endpoint k) ≤ logPosNorm f z := by
  exact (positive_of_lrwNormalizedControl_pos S.delta_pos S.delta_lt_one hz).le

end LRWShortPathPrinciple

/-- The boundary-distance output of the Phragmén--Lindelöf part of the LRW proof.

The scale is measured from the fixed base point; the distance from a later endpoint is handled by
the polygonal endpoint-distance estimate and the triangle inequality. -/
structure LRWBoundaryControl {u : ℂ → ℝ} {base : ℂ}
    (S : LRWShortPathPrinciple u base)
    (initial : LRWAdmissiblePoint S.delta u base) where
  scale : ℕ → ℝ
  initial_eq_base : initial.controlPoint.point = base
  scale_gt_one : ∀ k, 1 < scale k
  scale_mono : Monotone scale
  height_div_log_scale :
    Tendsto (fun k ↦ u ((S.matchingArcs initial).endpoint k) / Real.log (scale k)) atTop atTop
  base_infDist_le : ∀ k,
    infDist base (frontier (S.domain initial k)) ≤ scale k

namespace LRWBoundaryControl

variable {u : ℂ → ℝ} {base : ℂ} {S : LRWShortPathPrinciple u base}
  {initial : LRWAdmissiblePoint S.delta u base}

/-- The distance of the current endpoint from the stage boundary is controlled by the distance
traversed in earlier blocks plus the base-point boundary scale. -/
lemma endpoint_infDist_le (B : LRWBoundaryControl S initial) (k : ℕ) :
    infDist ((S.matchingArcs initial).endpoint k) (frontier (S.domain initial k)) ≤
      (∑ i ∈ Finset.range k, ((S.matchingArcs initial).arc i).length.toReal) + B.scale k := by
  calc
    infDist ((S.matchingArcs initial).endpoint k) (frontier (S.domain initial k)) ≤
        infDist base (frontier (S.domain initial k)) +
          dist ((S.matchingArcs initial).endpoint k) base :=
      Metric.infDist_le_infDist_add_dist
    _ ≤ B.scale k +
        ∑ i ∈ Finset.range k, ((S.matchingArcs initial).arc i).length.toReal := by
      apply add_le_add (B.base_infDist_le k)
      have hdist := (S.matchingArcs initial).dist_endpoint_zero_le_sum_length k
      have hbase :
          dist ((S.matchingArcs initial).endpoint k) base =
            dist ((S.matchingArcs initial).endpoint k) initial.controlPoint.point :=
        (congrArg (fun x : ℂ ↦ dist ((S.matchingArcs initial).endpoint k) x)
          B.initial_eq_base).symm
      rw [hbase]
      simpa only [LRWShortPathPrinciple.matchingArcs_endpoint,
        LRWShortPathPrinciple.state_zero] using hdist
    _ = (∑ i ∈ Finset.range k,
          ((S.matchingArcs initial).arc i).length.toReal) + B.scale k := add_comm _ _

/-- The short-path bound has exactly the recurrence form used by the finite-block LRW engine. -/
lemma shortPathRecurrence (B : LRWBoundaryControl S initial) (k : ℕ) :
    ((S.matchingArcs initial).arc k).length ≤ ENNReal.ofReal
      (S.constant *
        ((∑ i ∈ Finset.range k, ((S.matchingArcs initial).arc i).length.toReal) +
          B.scale k)) := by
  refine (S.arc_length_le initial k).trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (B.endpoint_infDist_le k) S.constant_nonneg

/-- Package the chosen analytic steps and the boundary estimate in the exact positive-arc
interface consumed by `Construction`. -/
noncomputable def toPositiveArcConstruction {f : ℂ → ℂ}
    (S : LRWShortPathPrinciple (logPosNorm f) base)
    (initial : LRWAdmissiblePoint S.delta (logPosNorm f) base)
    (B : LRWBoundaryControl S initial) (hf : Continuous f) :
    LRWPositiveArcConstruction (S.domain initial) (S.normalizedControl initial) f where
  chain := S.matchingArcs initial
  height k := logPosNorm f ((S.matchingArcs initial).endpoint k)
  boundaryScale := B.scale
  growthFactor := lrwGrowthFactor S.delta
  positivityFactor := S.delta
  shortPathConstant := S.constant
  f_continuous := hf
  growthFactor_gt_one := one_lt_lrwGrowthFactor S.delta_pos S.delta_lt_one
  positivityFactor_pos := S.delta_pos
  shortPathConstant_nonneg := S.constant_nonneg
  initialHeight_pos := initial.controlPoint.positive
  endpointGrowth := S.endpointGrowth initial
  boundaryScale_gt_one := B.scale_gt_one
  boundaryScale_mono := B.scale_mono
  height_div_log_boundaryScale := B.height_div_log_scale
  shortPathRecurrence := B.shortPathRecurrence
  positiveControl := by
    intro k z hz
    exact S.segment_logPos_lower initial k hz

/-- End-to-end constructor once the two analytic inputs have been proved: a single locally
rectifiable polygonal ray works for every positive exponent. -/
theorem exists_path {f : ℂ → ℂ}
    (S : LRWShortPathPrinciple (logPosNorm f) base)
    (initial : LRWAdmissiblePoint S.delta (logPosNorm f) base)
    (B : LRWBoundaryControl S initial) (hf : Continuous f) :
    ∃ C : LocallyRectifiablePath,
      C.vertex = (S.matchingArcs initial).toFiniteArcBlocks.vertex ∧
      ∀ lambda : ℝ, 0 < lambda → lineIntegral C f lambda ≠ ∞ := by
  exact (B.toPositiveArcConstruction S initial hf).toLogPosBlockConstruction.exists_path

/-- The growth of a transcendental entire function and the boundary-access theorem construct the
boundary-scale certificate required by the recursive LRW path. -/
theorem exists_boundaryControl_logPosNorm {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (htrans : ¬ IsPolynomialFunction f) {base : ℂ}
    (S : LRWShortPathPrinciple (logPosNorm f) base)
    (initial : LRWAdmissiblePoint S.delta (logPosNorm f) base)
    (hinitial : initial.controlPoint.point = base) :
    Nonempty (LRWBoundaryControl S initial) := by
  let height : ℕ → ℝ := fun k ↦
    logPosNorm f ((S.matchingArcs initial).endpoint k)
  let scale : ℕ → ℝ := fun k ↦
    max 2 (infDist base (frontier (S.domain initial k)))
  have hheight : Tendsto height atTop atTop := by
    apply endpoint_tendsto_atTop
    · exact one_lt_lrwGrowthFactor S.delta_pos S.delta_lt_one
    · dsimp [height]
      simpa only [LRWShortPathPrinciple.matchingArcs_endpoint,
        LRWShortPathPrinciple.state_zero] using initial.controlPoint.positive
    · intro k
      exact S.endpointGrowth initial k
  have hheightMono : Monotone height := by
    apply monotone_nat_of_le_succ
    intro k
    have hkpos : 0 < height k := (S.state initial k).controlPoint.positive
    exact ((le_mul_iff_one_le_left hkpos).2
      (one_lt_lrwGrowthFactor S.delta_pos S.delta_lt_one).le).trans
      (S.endpointGrowth initial k)
  let level : ℕ → ℝ := fun k ↦ lrwLevel S.delta (logPosNorm f) (S.state initial k).controlPoint
  have hlevel : Tendsto level atTop atTop := by
    have hmul := hheight.const_mul_atTop (inv_pos.mpr (sub_pos.mpr S.delta_lt_one))
    simpa only [level, height, lrwLevel, div_eq_mul_inv, mul_comm,
      LRWShortPathPrinciple.matchingArcs_endpoint] using hmul
  have hlevelMono : Monotone level := by
    intro i j hij
    dsimp only [level, lrwLevel]
    exact div_le_div_of_nonneg_right (hheightMono hij) (sub_pos.mpr S.delta_lt_one).le
  have hdomainMono : Monotone (S.domain initial) := by
    intro i j hij
    exact sublevelComponent_mono base (hlevelMono hij)
  have hproper : ∀ k, S.domain initial k ≠ univ := by
    intro k
    obtain ⟨z, hz⟩ := logPosNorm_unbounded hf htrans (level k)
    exact sublevelComponent_ne_univ_of_le_value hz
  have hopen : ∀ k, IsOpen (S.domain initial k) := by
    intro k
    exact isOpen_sublevelComponent (continuous_logPosNorm hf.continuous) _ _
  have hbaseMem : ∀ k, base ∈ S.domain initial k := by
    intro k
    apply mem_sublevelComponent_self
    apply sublevelComponent_nonempty_iff.mp
    exact ⟨(S.state initial k).controlPoint.point, (S.state initial k).mem_domain⟩
  have hscaleGt : ∀ k, 1 < scale k := by
    intro k
    exact lt_max_of_lt_left (by norm_num)
  have hscaleMono : Monotone scale := by
    intro i j hij
    apply max_le_max le_rfl
    exact infDist_frontier_mono (hopen i) (hopen j) (hbaseMem i) (hbaseMem j)
      (hproper i) (hproper j) (hdomainMono hij)
  obtain ⟨w, hwSphere, hwMax⟩ :=
    (isCompact_sphere (0 : ℂ) 1).exists_isMaxOn
      (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1))
      (continuous_logPosNorm hf.continuous).continuousOn
  let M : ℝ := logPosNorm f w
  have hsphere : ∀ z : ℂ, ‖z‖ = 1 → logPosNorm f z ≤ M := by
    intro z hz
    apply hwMax
    simpa [mem_sphere_iff_norm] using hz
  let Bconst : ℝ := 2 + ‖base‖
  let Cconst : ℝ := (1 - S.delta)⁻¹
  have hBconst : 0 ≤ Bconst := by dsimp [Bconst]; positivity
  have hbound : ∀ n : ℝ, 0 < n → ∀ᶠ k in atTop,
      scale k ≤ Bconst + Real.exp ((Cconst * height k - M) / n) := by
    intro n hn
    have hevGrowth := eventually_exists_norm_eq_posLog_ge hf htrans (n + 1)
    have hevRadius : ∀ᶠ r : ℝ in atTop, Real.exp (max M 0) < r :=
      eventually_gt_atTop (Real.exp (max M 0))
    obtain ⟨r, ⟨hrone, z, hzr, hzgrowth⟩, hrlarge⟩ :=
      (hevGrowth.and hevRadius).exists
    have hrpos : 0 < r := zero_lt_one.trans hrone
    have hloglarge : max M 0 < Real.log r := by
      rw [← Real.exp_lt_exp, Real.exp_log hrpos]
      exact hrlarge
    have hMlog : M < Real.log r := (le_max_left M 0).trans_lt hloglarge
    have hzgrowth' : (n + 1) * Real.log r ≤ logPosNorm f z := by
      rw [logPosNorm_eq_log_max]
      simpa [Real.posLog_eq_log_max_one (norm_nonneg (f z))] using hzgrowth
    have hzexcess : 0 < radialExcess (logPosNorm f) M n z := by
      unfold radialExcess
      rw [hzr]
      linarith
    have hUnion : ⋃ k, S.domain initial k = univ := by
      simpa only [LRWShortPathPrinciple.domain, lrwDomain, level] using
        (iUnion_sublevelComponent_eq_univ (continuous_logPosNorm hf.continuous) hlevel base)
    have hzUnion : z ∈ ⋃ k, S.domain initial k := by rw [hUnion]; trivial
    obtain ⟨K, hzK⟩ := mem_iUnion.mp hzUnion
    filter_upwards [eventually_ge_atTop K] with k hk
    have hzk : z ∈ S.domain initial k := hdomainMono hk hzK
    have hznorm : 1 < ‖z‖ := by simpa only [hzr] using hrone
    have hd := distance_to_frontier_le_exp (subharmonic_logPosNorm hf)
      (hopen k) hn
      (fun y hy ↦ sublevelComponent_subset (logPosNorm f) (level k) base hy)
      hsphere hzk hznorm hzexcess base
    change max 2 (infDist base (frontier (S.domain initial k))) ≤
      Bconst + Real.exp ((Cconst * height k - M) / n)
    have hexpEq : Real.exp ((level k - M) / n) =
        Real.exp ((Cconst * height k - M) / n) := by
      have hlevelEq : level k = Cconst * height k := by
        dsimp [level, Cconst, height, lrwLevel]
        simp only [LRWShortPathPrinciple.matchingArcs_endpoint, div_eq_mul_inv, mul_comm]
      rw [hlevelEq]
    rw [hexpEq] at hd
    apply max_le
    · dsimp [Bconst]
      exact (le_add_of_nonneg_right (norm_nonneg base)).trans
        (le_add_of_nonneg_right (Real.exp_pos _).le)
    · exact hd.trans (by
        dsimp [Bconst]
        linarith)
  refine ⟨{
    scale := scale
    initial_eq_base := hinitial
    scale_gt_one := hscaleGt
    scale_mono := hscaleMono
    height_div_log_scale := ?_
    base_infDist_le := fun k ↦ le_max_right 2 _ }⟩
  exact height_div_log_boundaryScale_tendsto_of_divisor_bounds hheight hscaleGt hBconst hbound

end LRWBoundaryControl

end Erdos515
