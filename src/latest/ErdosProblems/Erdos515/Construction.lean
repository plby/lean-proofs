/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.LRWCore
import ErdosProblems.Erdos515.ShortPath
import ErdosProblems.Erdos515.Subharmonic

/-!
# The finite-block construction bridge for Erdős Problem 515

This file packages the output of the analytic short-path step in exactly the form needed by the
abstract LRW summability engine.  The analytic theorem is allowed to choose a different finite
polygonal block at every stage, but the blocks themselves do not depend on `lambda`.

The substantive bookkeeping proved here is as follows.

* geometric endpoint growth makes the block heights tend to infinity;
* positivity on every flattened segment therefore makes the polygonal ray escape uniformly;
* the short-path recurrence is solved by `length_recurrence`;
* a subexponential boundary-distance estimate turns that solution into the `lengthBound` field of
  `LRWArcInequalities`;
* the resulting single flattened path has finite inverse-modulus integral for every positive
  exponent.
-/

open Filter Set
open scoped ENNReal NNReal Topology

namespace Erdos515

/-- The original LRW growth hypothesis in sequential form implies the subexponential radius
estimate used in the path-length recurrence. -/
lemma boundaryScale_subexponential_of_ratio_tendsto
    {height boundaryScale : ℕ → ℝ}
    (hscale : ∀ k, 1 < boundaryScale k)
    (hratio : Tendsto (fun k ↦ height k / Real.log (boundaryScale k)) atTop atTop) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ k ≥ N,
      boundaryScale k ≤ Real.exp (epsilon * height k) := by
  intro epsilon hepsilon
  have hevent : ∀ᶠ k in atTop,
      1 / epsilon ≤ height k / Real.log (boundaryScale k) :=
    hratio.eventually (eventually_ge_atTop (1 / epsilon))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨N, fun k hk ↦ ?_⟩
  have hlog : 0 < Real.log (boundaryScale k) := Real.log_pos (hscale k)
  have hdiv := (le_div_iff₀ hlog).mp (hN k hk)
  have hmul := mul_le_mul_of_nonneg_left hdiv hepsilon.le
  have hlogle : Real.log (boundaryScale k) ≤ epsilon * height k := by
    calc
      Real.log (boundaryScale k) = epsilon * ((1 / epsilon) *
          Real.log (boundaryScale k)) := by field_simp [hepsilon.ne']
      _ ≤ epsilon * height k := hmul
  calc
    boundaryScale k = Real.exp (Real.log (boundaryScale k)) :=
      (Real.exp_log (zero_lt_one.trans (hscale k))).symm
    _ ≤ Real.exp (epsilon * height k) := Real.exp_le_exp.mpr hlogle

/-- A positive lower bound for `log⁺ |f|` is an exponential lower bound for `|f|`.
The positivity assumption is what rules out the truncated `log⁺ = 0` branch. -/
lemma exp_le_norm_of_le_logPosNorm {f : ℂ → ℂ} {A : ℝ} (hA : 0 < A)
    {z : ℂ} (hz : A ≤ logPosNorm f z) :
    Real.exp A ≤ ‖f z‖ := by
  have hnorm : 1 < ‖f z‖ := by
    by_contra h
    have hle : ‖f z‖ ≤ 1 := le_of_not_gt h
    rw [logPosNorm_eq_log_max, max_eq_left hle] at hz
    exact (not_le_of_gt hA) (by simpa using hz)
  rw [logPosNorm_eq_log_max, max_eq_right hnorm.le] at hz
  calc
    Real.exp A ≤ Real.exp (Real.log ‖f z‖) := Real.exp_le_exp.mpr hz
    _ = ‖f z‖ := Real.exp_log (zero_lt_one.trans hnorm)

/-- The total inverse-modulus cost of one finite polygonal block. -/
noncomputable def finiteBlockCost (f : ℂ → ℂ) (lambda : ℝ) {steps : ℕ}
    (vertex : Fin (steps + 1) → ℂ) : ℝ≥0∞ :=
  ∑ i : Fin steps,
    segmentIntegral f lambda (vertex i.castSucc) (vertex i.succ)

/-- The ordinary Euclidean length of one finite polygonal block. -/
noncomputable def finiteBlockLength {steps : ℕ}
    (vertex : Fin (steps + 1) → ℂ) : ℝ :=
  ∑ i : Fin steps, ‖vertex i.succ - vertex i.castSucc‖

lemma finiteBlockLength_nonneg {steps : ℕ} (vertex : Fin (steps + 1) → ℂ) :
    0 ≤ finiteBlockLength vertex := by
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- A positive blockwise lower bound for `log⁺ |f|` gives exactly the LRW block-cost bound. -/
lemma finiteBlockCost_le_of_logPosNorm_ge
    {f : ℂ → ℂ} {lambda A : ℝ} (hlambda : 0 < lambda) (hA : 0 < A)
    {steps : ℕ} (vertex : Fin (steps + 1) → ℂ)
    (hcontrol : ∀ i : Fin steps, ∀ t ∈ Icc (0 : ℝ) 1,
      A ≤ logPosNorm f (segmentPoint (vertex i.castSucc) (vertex i.succ) t)) :
    finiteBlockCost f lambda vertex ≤ ENNReal.ofReal
      (finiteBlockLength vertex * Real.exp (-lambda * A)) := by
  calc
    finiteBlockCost f lambda vertex ≤
        ∑ i : Fin steps, ENNReal.ofReal ‖vertex i.succ - vertex i.castSucc‖ *
          ENNReal.ofReal (Real.exp (-lambda * A)) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply segmentIntegral_le_of_norm_ge_exp hlambda.le
      intro t ht
      exact exp_le_norm_of_le_logPosNorm hA (hcontrol i t ht)
    _ = ENNReal.ofReal (finiteBlockLength vertex * Real.exp (-lambda * A)) := by
      rw [← Finset.sum_mul]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)]
      rw [ENNReal.ofReal_mul (finiteBlockLength_nonneg vertex)]
      simp only [finiteBlockLength]

/-- A fully quantitative finite-block output of the nested-domain/short-path construction.

`segmentBlock n` records which finite block contains flattened segment `n`.  Requiring this index
to tend to infinity is the exact no-infinite-block condition needed for escape.  The `regroup`
field says that all flattened segments are accounted for by their finite block costs; it is the
statement supplied by the finite-block concatenation theorem in `Path`.
-/
structure LRWFiniteBlockConstruction (f : ℂ → ℂ)
    (blockCost : ℝ → ℕ → ℝ≥0∞) where
  vertex : ℕ → ℂ
  segmentBlock : ℕ → ℕ
  control : ℂ → ℝ
  height : ℕ → ℝ
  arcLength : ℕ → ℝ
  boundaryScale : ℕ → ℝ
  growthFactor : ℝ
  positivityFactor : ℝ
  shortPathConstant : ℝ
  growthFactor_gt_one : 1 < growthFactor
  positivityFactor_pos : 0 < positivityFactor
  shortPathConstant_nonneg : 0 ≤ shortPathConstant
  initialHeight_pos : 0 < height 0
  control_continuous : Continuous control
  endpointGrowth : ∀ k, growthFactor * height k ≤ height (k + 1)
  boundaryScale_nonneg : ∀ k, 0 ≤ boundaryScale k
  boundaryScale_mono : Monotone boundaryScale
  boundaryScale_subexponential : ∀ epsilon : ℝ, 0 < epsilon →
    ∃ N : ℕ, ∀ k ≥ N, boundaryScale k ≤ Real.exp (epsilon * height k)
  shortPathRecurrence : ∀ k,
    arcLength k ≤ shortPathConstant *
      ((∑ i ∈ Finset.range k, arcLength i) + boundaryScale k)
  segmentBlock_tendsto : Tendsto segmentBlock atTop atTop
  segmentControlLower : ∀ n t, t ∈ Icc (0 : ℝ) 1 →
    positivityFactor * height (segmentBlock n) ≤
      control (segmentPoint (vertex n) (vertex (n + 1)) t)
  costBound : ∀ lambda : ℝ, 0 < lambda → ∀ k,
    blockCost lambda k ≤ ENNReal.ofReal
      (arcLength k * Real.exp (-lambda * positivityFactor * height k))
  regroup : ∀ lambda : ℝ, 0 < lambda →
    (∑' n : ℕ, segmentIntegral f lambda (vertex n) (vertex (n + 1))) ≤
      ∑' k : ℕ, blockCost lambda k

namespace LRWFiniteBlockConstruction

/-- The endpoint heights in any finite-block construction tend to infinity. -/
lemma height_tendsto_atTop {f : ℂ → ℂ} {blockCost : ℝ → ℕ → ℝ≥0∞}
    (h : LRWFiniteBlockConstruction f blockCost) :
    Tendsto h.height atTop atTop :=
  endpoint_tendsto_atTop h.growthFactor_gt_one h.initialHeight_pos h.endpointGrowth

/-- The height lower bound along the flattened segments tends to infinity. -/
lemma segmentHeight_tendsto_atTop {f : ℂ → ℂ}
    {blockCost : ℝ → ℕ → ℝ≥0∞}
    (h : LRWFiniteBlockConstruction f blockCost) :
    Tendsto (fun n ↦ h.positivityFactor * h.height (h.segmentBlock n)) atTop atTop := by
  exact (h.height_tendsto_atTop.comp h.segmentBlock_tendsto).const_mul_atTop
    h.positivityFactor_pos

/-- Positivity on every finite block transfers to uniform escape on whole flattened segments.

The essential compactness step is explicit: the continuous control function is bounded above on
every closed Euclidean ball.  Since its lower bound on late blocks tends to infinity, no point of
a late segment can remain in that ball. -/
lemma escape {f : ℂ → ℂ} {blockCost : ℝ → ℕ → ℝ≥0∞}
    (h : LRWFiniteBlockConstruction f blockCost) :
    ∀ R : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) 1,
      R ≤ ‖segmentPoint (h.vertex n) (h.vertex (n + 1)) t‖ := by
  intro R
  obtain ⟨M, hM⟩ := bddAbove_def.mp
    ((isCompact_closedBall (0 : ℂ) R).bddAbove_image h.control_continuous.continuousOn)
  have hevent : ∀ᶠ n in atTop,
      M + 1 ≤ h.positivityFactor * h.height (h.segmentBlock n) :=
    h.segmentHeight_tendsto_atTop.eventually (eventually_ge_atTop (M + 1))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨N, fun n hn t ht ↦ ?_⟩
  by_contra hnorm
  have hlt : ‖segmentPoint (h.vertex n) (h.vertex (n + 1)) t‖ < R :=
    lt_of_not_ge hnorm
  have hzball : segmentPoint (h.vertex n) (h.vertex (n + 1)) t ∈
      Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall]
    simpa only [dist_zero_right] using hlt.le
  have hupper : h.control (segmentPoint (h.vertex n) (h.vertex (n + 1)) t) ≤ M :=
    hM _ ⟨_, hzball, rfl⟩
  have hlower : M + 1 ≤
      h.control (segmentPoint (h.vertex n) (h.vertex (n + 1)) t) :=
    (hN n hn).trans (h.segmentControlLower n t ht)
  linarith

/-- Closed form of the path-length recurrence produced by the short-path theorem. -/
lemma arcLength_le_closedForm {f : ℂ → ℂ}
    {blockCost : ℝ → ℕ → ℝ≥0∞}
    (h : LRWFiniteBlockConstruction f blockCost) (k : ℕ) :
    h.arcLength k ≤ h.shortPathConstant * (1 + h.shortPathConstant) ^ k *
      h.boundaryScale k :=
  length_recurrence h.shortPathConstant_nonneg h.boundaryScale_mono
    h.shortPathRecurrence k

/-- The solved recurrence has the eventual LRW exponential form. -/
lemma arcLength_eventually_le_exp {f : ℂ → ℂ}
    {blockCost : ℝ → ℕ → ℝ≥0∞}
    (h : LRWFiniteBlockConstruction f blockCost) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (N : ℕ) (A C : ℝ), ∀ k ≥ N,
      h.arcLength k ≤ Real.exp (A + C * (k : ℝ) + epsilon * h.height k) := by
  obtain ⟨N, hscale⟩ := h.boundaryScale_subexponential epsilon hepsilon
  refine ⟨N, h.shortPathConstant, Real.log (1 + h.shortPathConstant), fun k hk ↦ ?_⟩
  have hcpos : 0 < 1 + h.shortPathConstant := by
    linarith [h.shortPathConstant_nonneg]
  have hcle : h.shortPathConstant ≤ Real.exp h.shortPathConstant := by
    exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  calc
    h.arcLength k ≤ h.shortPathConstant * (1 + h.shortPathConstant) ^ k *
        h.boundaryScale k := h.arcLength_le_closedForm k
    _ ≤ Real.exp h.shortPathConstant * (1 + h.shortPathConstant) ^ k *
        Real.exp (epsilon * h.height k) := by
      exact mul_le_mul
        (mul_le_mul hcle le_rfl (pow_nonneg hcpos.le k) (Real.exp_nonneg _))
        (hscale k hk) (h.boundaryScale_nonneg k)
        (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hcpos.le k))
    _ = Real.exp
        (h.shortPathConstant + Real.log (1 + h.shortPathConstant) * (k : ℝ) +
          epsilon * h.height k) := by
      rw [← Real.exp_log hcpos, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [Real.log_exp]
      ring

/-- The recursive finite-block package discharges every field of the abstract LRW engine. -/
def toArcInequalities {f : ℂ → ℂ} {blockCost : ℝ → ℕ → ℝ≥0∞}
    (h : LRWFiniteBlockConstruction f blockCost) :
    LRWArcInequalities blockCost where
  height := h.height
  arcLength := h.arcLength
  growthFactor := h.growthFactor
  positivityFactor := h.positivityFactor
  growthFactor_gt_one := h.growthFactor_gt_one
  positivityFactor_pos := h.positivityFactor_pos
  initialHeight_pos := h.initialHeight_pos
  endpointGrowth := h.endpointGrowth
  lengthBound := h.arcLength_eventually_le_exp
  costBound := h.costBound

/-- The complete construction bridge: the finite blocks determine one escaping polygonal ray,
and the same ray has finite inverse-modulus integral for every positive exponent. -/
theorem exists_path {f : ℂ → ℂ} {blockCost : ℝ → ℕ → ℝ≥0∞}
    (h : LRWFiniteBlockConstruction f blockCost) :
    ∃ C : LocallyRectifiablePath,
      C.vertex = h.vertex ∧
      ∀ lambda : ℝ, 0 < lambda → lineIntegral C f lambda ≠ ∞ := by
  apply exists_path_of_lrw_arc_inequalities f h.vertex h.escape blockCost
    h.toArcInequalities
  intro lambda hlambda
  simpa [lineIntegral, lrwPath] using h.regroup lambda hlambda

end LRWFiniteBlockConstruction

/-! ## Concrete finite blocks for the entire-function application -/

/-- A sequence of finite positive polygonal arcs whose endpoints match by construction.

The `k`th arc starts at `endpoint k` and finishes at `endpoint (k + 1)`.  The domains and
positive control functions may vary with the block; this is the form delivered by the nested
sublevel-domain construction. -/
structure MatchingFinitePositiveArcs (D : ℕ → Set ℂ) (v : ℕ → ℂ → ℝ) where
  endpoint : ℕ → ℂ
  arc : (k : ℕ) →
    FinitePositivePolygonalArc (D k) (v k) (endpoint k) (endpoint (k + 1))

namespace MatchingFinitePositiveArcs

/-- Forget the domains and positivity certificates and retain the exact finite blocks. -/
def toFiniteArcBlocks {D : ℕ → Set ℂ} {v : ℕ → ℂ → ℝ}
    (P : MatchingFinitePositiveArcs D v) : FiniteArcBlocks where
  segCount k := (P.arc k).steps
  segCount_pos k := (P.arc k).steps_pos
  point k := (P.arc k).vertex
  endpoint_eq_next k := (P.arc k).finish.trans (P.arc (k + 1)).start.symm

@[simp] lemma toFiniteArcBlocks_segCount {D : ℕ → Set ℂ} {v : ℕ → ℂ → ℝ}
    (P : MatchingFinitePositiveArcs D v) (k : ℕ) :
    P.toFiniteArcBlocks.segCount k = (P.arc k).steps := rfl

@[simp] lemma toFiniteArcBlocks_point {D : ℕ → Set ℂ} {v : ℕ → ℂ → ℝ}
    (P : MatchingFinitePositiveArcs D v) (k : ℕ) :
    P.toFiniteArcBlocks.point k = (P.arc k).vertex := rfl

/-- Exact conversion between the real length used by the recurrence and the extended-real
length supplied by the short-path theorem. -/
lemma ofReal_finiteBlockLength_toFiniteArcBlocks {D : ℕ → Set ℂ}
    {v : ℕ → ℂ → ℝ} (P : MatchingFinitePositiveArcs D v) (k : ℕ) :
    ENNReal.ofReal (finiteBlockLength (P.toFiniteArcBlocks.point k)) = (P.arc k).length := by
  rw [finiteBlockLength, FinitePositivePolygonalArc.length]
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [toFiniteArcBlocks_point, edist_dist, dist_eq_norm]
  rw [norm_sub_rev]
  rfl

/-- The same exact length conversion in the real-valued form expected by `length_recurrence`. -/
lemma finiteBlockLength_toFiniteArcBlocks {D : ℕ → Set ℂ}
    {v : ℕ → ℂ → ℝ} (P : MatchingFinitePositiveArcs D v) (k : ℕ) :
    finiteBlockLength (P.toFiniteArcBlocks.point k) = (P.arc k).length.toReal := by
  rw [← P.ofReal_finiteBlockLength_toFiniteArcBlocks k, ENNReal.toReal_ofReal]
  exact finiteBlockLength_nonneg _

/-- Translate an extended-real short-path bound into the real inequality consumed by the LRW
length recurrence. -/
lemma finiteBlockLength_le_iff_arc_length_le {D : ℕ → Set ℂ}
    {v : ℕ → ℂ → ℝ} (P : MatchingFinitePositiveArcs D v) (k : ℕ)
    {bound : ℝ} (hbound : 0 ≤ bound) :
    finiteBlockLength (P.toFiniteArcBlocks.point k) ≤ bound ↔
      (P.arc k).length ≤ ENNReal.ofReal bound := by
  rw [← P.ofReal_finiteBlockLength_toFiniteArcBlocks k]
  exact (ENNReal.ofReal_le_ofReal_iff hbound).symm

/-- A recurrence stated with the `ENNReal` arc lengths returned by `short_positive_polygonal_path`
is exactly the real recurrence expected by `LRWLogPosBlockConstruction`. -/
lemma finiteBlockLength_recurrence {D : ℕ → Set ℂ} {v : ℕ → ℂ → ℝ}
    (P : MatchingFinitePositiveArcs D v) {constant : ℝ} {boundaryScale : ℕ → ℝ}
    (hconstant : 0 ≤ constant) (hboundaryScale : ∀ k, 0 ≤ boundaryScale k)
    (hrecurrence : ∀ k,
      (P.arc k).length ≤ ENNReal.ofReal
        (constant * ((∑ i ∈ Finset.range k, (P.arc i).length.toReal) + boundaryScale k))) :
    ∀ k, finiteBlockLength (P.toFiniteArcBlocks.point k) ≤ constant *
      ((∑ i ∈ Finset.range k, finiteBlockLength (P.toFiniteArcBlocks.point i)) +
        boundaryScale k) := by
  intro k
  have hsum : 0 ≤
      ∑ i ∈ Finset.range k, finiteBlockLength (P.toFiniteArcBlocks.point i) :=
    Finset.sum_nonneg fun _ _ ↦ finiteBlockLength_nonneg _
  have hrhs : 0 ≤
      constant *
        ((∑ i ∈ Finset.range k, finiteBlockLength (P.toFiniteArcBlocks.point i)) +
          boundaryScale k) :=
    mul_nonneg hconstant (add_nonneg hsum (hboundaryScale k))
  refine (P.finiteBlockLength_le_iff_arc_length_le k hrhs).2 ?_
  simpa only [P.finiteBlockLength_toFiniteArcBlocks] using hrecurrence k

/-- The distance between the endpoints of one finite block is bounded by its exact chord-sum
length. -/
lemma dist_arc_endpoints_le_length {D : ℕ → Set ℂ} {v : ℕ → ℂ → ℝ}
    (P : MatchingFinitePositiveArcs D v) (k : ℕ) :
    dist (P.endpoint k) (P.endpoint (k + 1)) ≤ (P.arc k).length.toReal := by
  let Q := P.arc k
  let w : ℕ → ℂ := fun i ↦
    Q.vertex ⟨min i Q.steps, Nat.lt_succ_of_le (Nat.min_le_right i Q.steps)⟩
  have hpolygon := dist_le_range_sum_dist w Q.steps
  have hwzero : w 0 = P.endpoint k := by
    simpa [w, Q] using Q.start
  have hwlast : w Q.steps = P.endpoint (k + 1) := by
    simpa [w, Q] using Q.finish
  have hsum :
      (∑ i ∈ Finset.range Q.steps, dist (w i) (w (i + 1))) =
        finiteBlockLength Q.vertex := by
    rw [finiteBlockLength, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < Q.steps := Finset.mem_range.mp hi
    simp only [w, Nat.min_eq_left (Nat.le_of_lt hi'),
      Nat.min_eq_left (Nat.succ_le_iff.mpr hi'), Complex.dist_eq]
    rw [dif_pos hi']
    rw [norm_sub_rev]
    rfl
  rw [hwzero, hwlast, hsum] at hpolygon
  have hlength : finiteBlockLength Q.vertex = (P.arc k).length.toReal := by
    change finiteBlockLength (P.toFiniteArcBlocks.point k) = (P.arc k).length.toReal
    exact P.finiteBlockLength_toFiniteArcBlocks k
  rw [hlength] at hpolygon
  exact hpolygon

/-- Matching consecutive endpoints telescope: the displacement after `k` blocks is bounded by
the sum of the exact finite-arc lengths of the preceding blocks. -/
lemma dist_endpoint_zero_le_sum_length {D : ℕ → Set ℂ}
    {v : ℕ → ℂ → ℝ} (P : MatchingFinitePositiveArcs D v) (k : ℕ) :
    dist (P.endpoint k) (P.endpoint 0) ≤
      ∑ i ∈ Finset.range k, (P.arc i).length.toReal := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc
        dist (P.endpoint (k + 1)) (P.endpoint 0) ≤
            dist (P.endpoint (k + 1)) (P.endpoint k) +
              dist (P.endpoint k) (P.endpoint 0) := dist_triangle _ _ _
        _ ≤ (P.arc k).length.toReal +
              ∑ i ∈ Finset.range k, (P.arc i).length.toReal :=
          add_le_add (by simpa only [dist_comm] using P.dist_arc_endpoints_le_length k) ih
        _ = ∑ i ∈ Finset.range k, (P.arc i).length.toReal +
              (P.arc k).length.toReal := add_comm _ _

end MatchingFinitePositiveArcs

/-- Concrete analytic and recursive data on a sequence of matching finite polygonal blocks.

Unlike `LRWFiniteBlockConstruction`, this interface does not ask the caller to formulate a global
segment enumeration or a regrouping theorem.  Those are supplied by `FiniteArcBlocks`.  Its
control function is the actual `log⁺ |f|`, so the inverse-modulus block estimate is proved below
rather than assumed.
-/
structure LRWLogPosBlockConstruction (B : FiniteArcBlocks) (f : ℂ → ℂ) where
  height : ℕ → ℝ
  boundaryScale : ℕ → ℝ
  growthFactor : ℝ
  positivityFactor : ℝ
  shortPathConstant : ℝ
  f_continuous : Continuous f
  growthFactor_gt_one : 1 < growthFactor
  positivityFactor_pos : 0 < positivityFactor
  shortPathConstant_nonneg : 0 ≤ shortPathConstant
  initialHeight_pos : 0 < height 0
  endpointGrowth : ∀ k, growthFactor * height k ≤ height (k + 1)
  boundaryScale_gt_one : ∀ k, 1 < boundaryScale k
  boundaryScale_mono : Monotone boundaryScale
  height_div_log_boundaryScale :
    Tendsto (fun k ↦ height k / Real.log (boundaryScale k)) atTop atTop
  shortPathRecurrence : ∀ k,
    finiteBlockLength (B.point k) ≤ shortPathConstant *
      ((∑ i ∈ Finset.range k, finiteBlockLength (B.point i)) + boundaryScale k)
  segmentLogPosLower : ∀ k (j : Fin (B.segCount k)) t, t ∈ Icc (0 : ℝ) 1 →
    positivityFactor * height k ≤
      logPosNorm f (segmentPoint (B.blockVertex k j) (B.blockVertexSucc k j) t)

/-- The most convenient input interface for the analytic construction.

It keeps the finite positive arcs themselves, states their short-path recurrence in the
`ENNReal` form produced by `short_positive_polygonal_path`, and records how positivity of the
block control function implies the required quantitative lower bound for `log⁺ |f|`.
`toLogPosBlockConstruction` below performs all endpoint, length, and segment-index conversions. -/
structure LRWPositiveArcConstruction (D : ℕ → Set ℂ) (v : ℕ → ℂ → ℝ)
    (f : ℂ → ℂ) where
  chain : MatchingFinitePositiveArcs D v
  height : ℕ → ℝ
  boundaryScale : ℕ → ℝ
  growthFactor : ℝ
  positivityFactor : ℝ
  shortPathConstant : ℝ
  f_continuous : Continuous f
  growthFactor_gt_one : 1 < growthFactor
  positivityFactor_pos : 0 < positivityFactor
  shortPathConstant_nonneg : 0 ≤ shortPathConstant
  initialHeight_pos : 0 < height 0
  endpointGrowth : ∀ k, growthFactor * height k ≤ height (k + 1)
  boundaryScale_gt_one : ∀ k, 1 < boundaryScale k
  boundaryScale_mono : Monotone boundaryScale
  height_div_log_boundaryScale :
    Tendsto (fun k ↦ height k / Real.log (boundaryScale k)) atTop atTop
  shortPathRecurrence : ∀ k,
    (chain.arc k).length ≤ ENNReal.ofReal
      (shortPathConstant *
        ((∑ i ∈ Finset.range k, (chain.arc i).length.toReal) + boundaryScale k))
  positiveControl : ∀ k z, 0 < v k z →
    positivityFactor * height k ≤ logPosNorm f z

namespace LRWPositiveArcConstruction

/-- The matching positive arcs, converted to the finite-block interface used by the path
flattening theorem. -/
def blocks {D : ℕ → Set ℂ} {v : ℕ → ℂ → ℝ} {f : ℂ → ℂ}
    (h : LRWPositiveArcConstruction D v f) : FiniteArcBlocks :=
  h.chain.toFiniteArcBlocks

/-- Convert the analytic positive-arc package into the quantitative finite-block construction.
In particular, this theorem is the recurrence adapter: it removes `ENNReal.ofReal` from the
short-path length inequality without losing an inequality or changing a constant. -/
noncomputable def toLogPosBlockConstruction {D : ℕ → Set ℂ}
    {v : ℕ → ℂ → ℝ} {f : ℂ → ℂ}
    (h : LRWPositiveArcConstruction D v f) :
    LRWLogPosBlockConstruction h.blocks f where
  height := h.height
  boundaryScale := h.boundaryScale
  growthFactor := h.growthFactor
  positivityFactor := h.positivityFactor
  shortPathConstant := h.shortPathConstant
  f_continuous := h.f_continuous
  growthFactor_gt_one := h.growthFactor_gt_one
  positivityFactor_pos := h.positivityFactor_pos
  shortPathConstant_nonneg := h.shortPathConstant_nonneg
  initialHeight_pos := h.initialHeight_pos
  endpointGrowth := h.endpointGrowth
  boundaryScale_gt_one := h.boundaryScale_gt_one
  boundaryScale_mono := h.boundaryScale_mono
  height_div_log_boundaryScale := h.height_div_log_boundaryScale
  shortPathRecurrence := h.chain.finiteBlockLength_recurrence
    h.shortPathConstant_nonneg
    (fun k ↦ zero_le_one.trans (h.boundaryScale_gt_one k).le)
    h.shortPathRecurrence
  segmentLogPosLower := by
    intro k j t ht
    apply h.positiveControl k
    simpa only [blocks, MatchingFinitePositiveArcs.toFiniteArcBlocks,
      FiniteArcBlocks.blockVertex, FiniteArcBlocks.blockVertexSucc, segmentPoint] using
      (h.chain.arc k).segment_positive j j.isLt t ht

end LRWPositiveArcConstruction

namespace LRWLogPosBlockConstruction

lemma height_tendsto_atTop {B : FiniteArcBlocks} {f : ℂ → ℂ}
    (h : LRWLogPosBlockConstruction B f) : Tendsto h.height atTop atTop :=
  endpoint_tendsto_atTop h.growthFactor_gt_one h.initialHeight_pos h.endpointGrowth

lemma height_pos {B : FiniteArcBlocks} {f : ℂ → ℂ}
    (h : LRWLogPosBlockConstruction B f) (k : ℕ) : 0 < h.height k := by
  have hq : 0 < h.growthFactor := zero_lt_one.trans h.growthFactor_gt_one
  have hgrowth := endpoint_growth hq.le h.endpointGrowth 0 k
  simpa using (mul_pos (pow_pos hq k) h.initialHeight_pos).trans_le hgrowth

lemma positivity_height_tendsto_atTop {B : FiniteArcBlocks} {f : ℂ → ℂ}
    (h : LRWLogPosBlockConstruction B f) :
    Tendsto (fun k ↦ h.positivityFactor * h.height k) atTop atTop :=
  h.height_tendsto_atTop.const_mul_atTop h.positivityFactor_pos

/-- The genuine LRW control inequality implies that every segment in every sufficiently late
finite block lies outside an arbitrary compact ball. -/
lemma block_escape {B : FiniteArcBlocks} {f : ℂ → ℂ}
    (h : LRWLogPosBlockConstruction B f) :
    ∀ R : ℝ, ∃ K : ℕ, ∀ k ≥ K, ∀ j : Fin (B.segCount k),
      ∀ t ∈ Icc (0 : ℝ) 1,
        R ≤ ‖segmentPoint (B.blockVertex k j) (B.blockVertexSucc k j) t‖ := by
  intro R
  obtain ⟨M, hM⟩ := bddAbove_def.mp
    ((isCompact_closedBall (0 : ℂ) R).bddAbove_image
      (continuous_logPosNorm h.f_continuous).continuousOn)
  have hevent : ∀ᶠ k in atTop, M + 1 ≤ h.positivityFactor * h.height k :=
    h.positivity_height_tendsto_atTop.eventually (eventually_ge_atTop (M + 1))
  obtain ⟨K, hK⟩ := eventually_atTop.1 hevent
  refine ⟨K, fun k hk j t ht ↦ ?_⟩
  by_contra hnorm
  have hlt : ‖segmentPoint (B.blockVertex k j) (B.blockVertexSucc k j) t‖ < R :=
    lt_of_not_ge hnorm
  have hzball : segmentPoint (B.blockVertex k j) (B.blockVertexSucc k j) t ∈
      Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall]
    simpa only [dist_zero_right] using hlt.le
  have hupper : logPosNorm f
      (segmentPoint (B.blockVertex k j) (B.blockVertexSucc k j) t) ≤ M :=
    hM _ ⟨_, hzball, rfl⟩
  have hlower : M + 1 ≤ logPosNorm f
      (segmentPoint (B.blockVertex k j) (B.blockVertexSucc k j) t) :=
    (hK k hk).trans (h.segmentLogPosLower k j t ht)
  linarith

lemma boundaryScale_subexponential {B : FiniteArcBlocks} {f : ℂ → ℂ}
    (h : LRWLogPosBlockConstruction B f) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ, ∀ k ≥ N,
      h.boundaryScale k ≤ Real.exp (epsilon * h.height k) :=
  boundaryScale_subexponential_of_ratio_tendsto h.boundaryScale_gt_one
    h.height_div_log_boundaryScale

lemma arcLength_eventually_le_exp {B : FiniteArcBlocks} {f : ℂ → ℂ}
    (h : LRWLogPosBlockConstruction B f) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (N : ℕ) (A C : ℝ), ∀ k ≥ N,
      finiteBlockLength (B.point k) ≤
        Real.exp (A + C * (k : ℝ) + epsilon * h.height k) := by
  obtain ⟨N, hscale⟩ := h.boundaryScale_subexponential epsilon hepsilon
  refine ⟨N, h.shortPathConstant, Real.log (1 + h.shortPathConstant), fun k hk ↦ ?_⟩
  have hcpos : 0 < 1 + h.shortPathConstant := by
    linarith [h.shortPathConstant_nonneg]
  have hclosed := length_recurrence h.shortPathConstant_nonneg h.boundaryScale_mono
    h.shortPathRecurrence k
  have hcle : h.shortPathConstant ≤ Real.exp h.shortPathConstant :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  have hscaleNonneg : 0 ≤ h.boundaryScale k :=
    zero_le_one.trans (h.boundaryScale_gt_one k).le
  calc
    finiteBlockLength (B.point k) ≤
        h.shortPathConstant * (1 + h.shortPathConstant) ^ k * h.boundaryScale k := hclosed
    _ ≤ Real.exp h.shortPathConstant * (1 + h.shortPathConstant) ^ k *
        Real.exp (epsilon * h.height k) := by
      exact mul_le_mul
        (mul_le_mul hcle le_rfl (pow_nonneg hcpos.le k) (Real.exp_nonneg _))
        (hscale k hk) hscaleNonneg
        (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hcpos.le k))
    _ = Real.exp
        (h.shortPathConstant + Real.log (1 + h.shortPathConstant) * (k : ℝ) +
          epsilon * h.height k) := by
      rw [← Real.exp_log hcpos, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      simp only [Real.log_exp]
      ring

lemma blockCost_le {B : FiniteArcBlocks} {f : ℂ → ℂ}
    (h : LRWLogPosBlockConstruction B f) (lambda : ℝ) (hlambda : 0 < lambda) (k : ℕ) :
    B.blockCost f lambda k ≤ ENNReal.ofReal
      (finiteBlockLength (B.point k) *
        Real.exp (-lambda * h.positivityFactor * h.height k)) := by
  have hA : 0 < h.positivityFactor * h.height k :=
    mul_pos h.positivityFactor_pos (h.height_pos k)
  have hcost := finiteBlockCost_le_of_logPosNorm_ge hlambda hA (B.point k)
    (fun j t ht ↦ h.segmentLogPosLower k j t ht)
  have hblock : B.blockCost f lambda k = finiteBlockCost f lambda (B.point k) := by
    unfold FiniteArcBlocks.blockCost finiteBlockCost
    apply Finset.sum_congr rfl
    intro j _hj
    congr 2
  rw [hblock]
  simpa only [mul_assoc] using hcost

/-- All fields of the abstract LRW inequality package are consequences of the concrete finite
block construction. -/
noncomputable def toArcInequalities {B : FiniteArcBlocks} {f : ℂ → ℂ}
    (h : LRWLogPosBlockConstruction B f) :
    LRWArcInequalities (B.blockCost f) where
  height := h.height
  arcLength := fun k ↦ finiteBlockLength (B.point k)
  growthFactor := h.growthFactor
  positivityFactor := h.positivityFactor
  growthFactor_gt_one := h.growthFactor_gt_one
  positivityFactor_pos := h.positivityFactor_pos
  initialHeight_pos := h.initialHeight_pos
  endpointGrowth := h.endpointGrowth
  lengthBound := h.arcLength_eventually_le_exp
  costBound := h.blockCost_le

/-- Concrete end of the LRW construction: concatenate the finite short-path blocks and invoke the
summability engine. -/
theorem exists_path {B : FiniteArcBlocks} {f : ℂ → ℂ}
    (h : LRWLogPosBlockConstruction B f) :
    ∃ C : LocallyRectifiablePath,
      C.vertex = B.vertex ∧
      ∀ lambda : ℝ, 0 < lambda → lineIntegral C f lambda ≠ ∞ := by
  let hescape := h.block_escape
  let hflat := B.eventually_flattened_segment_norm_ge hescape
  apply exists_path_of_lrw_arc_inequalities f B.vertex hflat (B.blockCost f)
    h.toArcInequalities
  intro lambda _hlambda
  have heq := B.lineIntegral_toLocallyRectifiablePath hescape f lambda
  simpa [lineIntegral, lrwPath] using heq.le

end LRWLogPosBlockConstruction

namespace LRWPositiveArcConstruction

/-- Final path theorem directly in terms of the matching positive arcs supplied by the analytic
construction. -/
theorem exists_path {D : ℕ → Set ℂ} {v : ℕ → ℂ → ℝ} {f : ℂ → ℂ}
    (h : LRWPositiveArcConstruction D v f) :
    ∃ C : LocallyRectifiablePath,
      C.vertex = h.blocks.vertex ∧
      ∀ lambda : ℝ, 0 < lambda → lineIntegral C f lambda ≠ ∞ :=
  h.toLogPosBlockConstruction.exists_path

end LRWPositiveArcConstruction

end Erdos515
