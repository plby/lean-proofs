/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos515.Path
import ErdosProblems.Erdos515.Estimates

/-!
# The abstract Lewis--Rossi--Weitsman summability engine

The potential-theoretic part of the Lewis--Rossi--Weitsman construction produces a sequence of
positive polygonal arcs.  After the short-path and boundary-distance estimates have been combined,
the integral over the `k`th arc has the characteristic bound

`exp (A + C * k - b * a ^ k)`, with `1 < a` and `0 < b`.

This file isolates the last, purely sequential, step of the argument.  It deliberately does not
know how the arcs were found.  Instead it consumes their block costs, their LRW tail bounds, and a
regrouping estimate comparing the segment-by-segment integral of a polygonal ray with those block
costs.  Thus the short-positive-path theorem and the boundary-distance theorem enter only through
proved data supplied by callers.
-/

open Filter Set

open scoped ENNReal NNReal Topology

namespace Erdos515

/-- The final quantitative estimate in the LRW construction.

The additive constant `A` absorbs the factor denoted `B_n` in the paper.  The term `C * k` comes
from the length recurrence, while `b * a ^ k` comes from geometric endpoint growth and positivity
on the `k`th arc.  We ask for the estimate only eventually; the finitely many earlier arcs are
handled separately by `LRWBlockBounds.finite`.
-/
def HasLRWTailMajorant (cost : ℕ → ℝ≥0∞) : Prop :=
  ∃ (N : ℕ) (A C a b : ℝ), 1 < a ∧ 0 < b ∧
    ∀ k ≥ N,
      cost k ≤ ENNReal.ofReal (Real.exp (A + C * (k : ℝ) - b * a ^ k))

/-- Block-integral data sufficient for the final LRW summation, simultaneously for every positive
exponent.  A block is normally one finite polygonal arc, hence may contain several affine
segments. -/
structure LRWBlockBounds (blockCost : ℝ → ℕ → ℝ≥0∞) : Prop where
  finite : ∀ lambda, 0 < lambda → ∀ k, blockCost lambda k ≠ ∞
  majorant : ∀ lambda, 0 < lambda → HasLRWTailMajorant (blockCost lambda)

/-- The abstract inequalities produced by the nested-domain construction.

`height` is `u(a_k)` in the subharmonic proof (or the corresponding logarithmic modulus in the
specialized holomorphic proof), and `arcLength` is the length of the `k`th positive polygonal arc.
The first inequality is endpoint growth.  The `lengthBound` field is the output of the
boundary-distance estimate followed by the length recurrence: its coefficient `epsilon` can be
chosen after the path has been constructed.  Finally, `costBound` is precisely the consequence of
the short-positive-path principle for the integral over the arc.
-/
structure LRWArcInequalities (blockCost : ℝ → ℕ → ℝ≥0∞) where
  height : ℕ → ℝ
  arcLength : ℕ → ℝ
  growthFactor : ℝ
  positivityFactor : ℝ
  growthFactor_gt_one : 1 < growthFactor
  positivityFactor_pos : 0 < positivityFactor
  initialHeight_pos : 0 < height 0
  endpointGrowth : ∀ k, growthFactor * height k ≤ height (k + 1)
  lengthBound : ∀ epsilon : ℝ, 0 < epsilon →
    ∃ (N : ℕ) (A C : ℝ), ∀ k ≥ N,
      arcLength k ≤ Real.exp (A + C * (k : ℝ) + epsilon * height k)
  costBound : ∀ lambda : ℝ, 0 < lambda → ∀ k,
    blockCost lambda k ≤ ENNReal.ofReal
      (arcLength k * Real.exp (-lambda * positivityFactor * height k))

/-- Build the polygonal ray once a sequence of vertices has been shown to escape uniformly on
whole segments.  Keeping this constructor explicit makes the interface usable by either the
subharmonic LRW construction or the specialized holomorphic construction. -/
def lrwPath (vertex : ℕ → ℂ)
    (hescape : ∀ R : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) 1,
      R ≤ ‖segmentPoint (vertex n) (vertex (n + 1)) t‖) :
    LocallyRectifiablePath where
  vertex := vertex
  tendsToInfinity := hescape

@[simp] lemma lrwPath_vertex (vertex : ℕ → ℂ)
    (hescape : ∀ R : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) 1,
      R ≤ ‖segmentPoint (vertex n) (vertex (n + 1)) t‖)
    (n : ℕ) :
    (lrwPath vertex hescape).vertex n = vertex n :=
  rfl

private lemma tsum_ne_top_of_eventually_le
    {g h : ℕ → ℝ≥0∞}
    (hg : ∀ k, g k ≠ ∞)
    (hh : ∑' k, h k ≠ ∞)
    (hgh : ∀ᶠ k in atTop, g k ≤ h k) :
    ∑' k, g k ≠ ∞ := by
  have hh_point : ∀ k, h k ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hh
  have hh' : Summable (fun k ↦ (h k).toReal) := ENNReal.summable_toReal hh
  have hgh' : ∀ᶠ k in atTop, ‖(g k).toReal‖ ≤ (h k).toReal := by
    filter_upwards [hgh] with k hk
    simpa only [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using
      ENNReal.toReal_mono (hh_point k) hk
  have hg' : Summable (fun k ↦ (g k).toReal) :=
    hh'.of_norm_bounded_eventually_nat hgh'
  have hgnn : Summable (fun k ↦ (g k).toNNReal) := by
    rw [← NNReal.summable_coe]
    simpa only [ENNReal.coe_toNNReal_eq_toReal] using hg'
  have hcoe : (fun k ↦ (((g k).toNNReal : ℝ≥0) : ℝ≥0∞)) = g := by
    funext k
    exact ENNReal.coe_toNNReal (hg k)
  rw [← hcoe, ENNReal.tsum_coe_ne_top_iff_summable]
  exact hgnn

/-- The LRW majorant has finite `ENNReal` sum.  This is the formal summability step following
equation (32), including the harmless finite prefix before that estimate becomes valid. -/
theorem HasLRWTailMajorant.tsum_ne_top {cost : ℕ → ℝ≥0∞}
    (hcost : ∀ k, cost k ≠ ∞) (hmajorant : HasLRWTailMajorant cost) :
    ∑' k, cost k ≠ ∞ := by
  obtain ⟨N, A, C, a, b, ha, hb, hbound⟩ := hmajorant
  have hsummable :
      Summable (fun k : ℕ ↦ Real.exp (A + C * (k : ℝ) - b * a ^ k)) := by
    have hbase := summable_exp_linear_sub_geometric C ha hb
    have heq :
        (fun k : ℕ ↦ Real.exp A * Real.exp (C * (k : ℝ) - b * a ^ k)) =
          fun k : ℕ ↦ Real.exp (A + C * (k : ℝ) - b * a ^ k) := by
      funext k
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← heq]
    exact hbase.mul_left (Real.exp A)
  apply tsum_ne_top_of_eventually_le hcost hsummable.tsum_ofReal_ne_top
  filter_upwards [eventually_ge_atTop N] with k hk
  exact hbound k hk

/-- The nested-domain inequalities imply the quantitative block bounds used by the summability
engine.  Here the auxiliary coefficient in the boundary-distance estimate is chosen only after
`lambda`; the vertices, arcs, and hence the resulting ray do not depend on `lambda`. -/
theorem LRWArcInequalities.toBlockBounds
    {blockCost : ℝ → ℕ → ℝ≥0∞} (h : LRWArcInequalities blockCost) :
    LRWBlockBounds blockCost := by
  constructor
  · intro lambda hlambda k
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.costBound lambda hlambda k)
  · intro lambda hlambda
    let epsilon : ℝ := lambda * h.positivityFactor / 2
    have hepsilon : 0 < epsilon := by
      exact div_pos (mul_pos hlambda h.positivityFactor_pos) (by norm_num)
    obtain ⟨N, A, C, hlength⟩ := h.lengthBound epsilon hepsilon
    have hq_nonneg : 0 ≤ h.growthFactor :=
      zero_le_one.trans h.growthFactor_gt_one.le
    have hheight : ∀ k, h.growthFactor ^ k * h.height 0 ≤ h.height k := by
      intro k
      simpa using endpoint_growth hq_nonneg h.endpointGrowth 0 k
    refine ⟨N, A, C, h.growthFactor, epsilon * h.height 0,
      h.growthFactor_gt_one, mul_pos hepsilon h.initialHeight_pos, ?_⟩
    intro k hk
    calc
      blockCost lambda k
          ≤ ENNReal.ofReal
              (h.arcLength k * Real.exp (-lambda * h.positivityFactor * h.height k)) :=
        h.costBound lambda hlambda k
      _ ≤ ENNReal.ofReal
              (Real.exp (A + C * (k : ℝ) + epsilon * h.height k) *
                Real.exp (-lambda * h.positivityFactor * h.height k)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right (hlength k hk)
          (Real.exp_pos _).le
      _ = ENNReal.ofReal
              (Real.exp (A + C * (k : ℝ) - epsilon * h.height k)) := by
        congr 1
        rw [← Real.exp_add]
        congr 1
        dsimp only [epsilon]
        ring
      _ ≤ ENNReal.ofReal
              (Real.exp
                (A + C * (k : ℝ) -
                  (epsilon * h.height 0) * h.growthFactor ^ k)) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hscaled :
            epsilon * (h.growthFactor ^ k * h.height 0) ≤ epsilon * h.height k :=
          mul_le_mul_of_nonneg_left (hheight k) hepsilon.le
        nlinarith [hscaled]

/-- Every positive exponent has a finite sum of LRW block costs. -/
theorem LRWBlockBounds.tsum_ne_top {blockCost : ℝ → ℕ → ℝ≥0∞}
    (h : LRWBlockBounds blockCost) (lambda : ℝ) (hlambda : 0 < lambda) :
    ∑' k, blockCost lambda k ≠ ∞ :=
  HasLRWTailMajorant.tsum_ne_top (h.finite lambda hlambda) (h.majorant lambda hlambda)

/-- A sequence satisfying the nested-domain inequalities has finite total block cost for every
positive exponent. -/
theorem LRWArcInequalities.tsum_ne_top
    {blockCost : ℝ → ℕ → ℝ≥0∞} (h : LRWArcInequalities blockCost)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ∑' k, blockCost lambda k ≠ ∞ :=
  h.toBlockBounds.tsum_ne_top lambda hlambda

/-- Abstract finite-block conclusion.  The regrouping inequality is where a caller records that
the finite segments in each constructed arc account for the whole ray. -/
theorem exists_path_of_block_tsum_ne_top
    (f : ℂ → ℂ) (vertex : ℕ → ℂ)
    (hescape : ∀ R : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) 1,
      R ≤ ‖segmentPoint (vertex n) (vertex (n + 1)) t‖)
    (blockCost : ℝ → ℕ → ℝ≥0∞)
    (hblock : ∀ lambda, 0 < lambda → ∑' k, blockCost lambda k ≠ ∞)
    (hregroup : ∀ lambda, 0 < lambda →
      lineIntegral (lrwPath vertex hescape) f lambda ≤ ∑' k, blockCost lambda k) :
    ∃ C : LocallyRectifiablePath,
      C.vertex = vertex ∧
      ∀ lambda : ℝ, 0 < lambda → lineIntegral C f lambda ≠ ∞ := by
  refine ⟨lrwPath vertex hescape, rfl, fun lambda hlambda ↦ ?_⟩
  exact ne_top_of_le_ne_top (hblock lambda hlambda) (hregroup lambda hlambda)

/-- Construct the requested polygonal ray from LRW block inequalities and a proved regrouping of
the finite polygonal arcs into its affine segments. -/
theorem exists_path_of_lrw_block_bounds
    (f : ℂ → ℂ) (vertex : ℕ → ℂ)
    (hescape : ∀ R : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) 1,
      R ≤ ‖segmentPoint (vertex n) (vertex (n + 1)) t‖)
    (blockCost : ℝ → ℕ → ℝ≥0∞)
    (hblocks : LRWBlockBounds blockCost)
    (hregroup : ∀ lambda, 0 < lambda →
      lineIntegral (lrwPath vertex hescape) f lambda ≤ ∑' k, blockCost lambda k) :
    ∃ C : LocallyRectifiablePath,
      C.vertex = vertex ∧
      ∀ lambda : ℝ, 0 < lambda → lineIntegral C f lambda ≠ ∞ := by
  exact exists_path_of_block_tsum_ne_top f vertex hescape blockCost
    hblocks.tsum_ne_top hregroup

/-- Main abstract LRW engine.  It consumes the explicit endpoint/arc sequences and the three LRW
inequalities (endpoint growth, boundary-distance/length control, and the short-positive-arc cost
bound), then returns one polygonal ray working for every positive exponent. -/
theorem exists_path_of_lrw_arc_inequalities
    (f : ℂ → ℂ) (vertex : ℕ → ℂ)
    (hescape : ∀ R : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) 1,
      R ≤ ‖segmentPoint (vertex n) (vertex (n + 1)) t‖)
    (blockCost : ℝ → ℕ → ℝ≥0∞)
    (h : LRWArcInequalities blockCost)
    (hregroup : ∀ lambda, 0 < lambda →
      lineIntegral (lrwPath vertex hescape) f lambda ≤ ∑' k, blockCost lambda k) :
    ∃ C : LocallyRectifiablePath,
      C.vertex = vertex ∧
      ∀ lambda : ℝ, 0 < lambda → lineIntegral C f lambda ≠ ∞ := by
  exact exists_path_of_lrw_block_bounds f vertex hescape blockCost h.toBlockBounds hregroup

/-- One-segment-per-arc specialization of the LRW engine.  This is often the most convenient
interface after a short path has already been flattened to its polygonal vertex sequence. -/
theorem exists_path_of_lrw_segment_inequalities
    (f : ℂ → ℂ) (vertex : ℕ → ℂ)
    (hescape : ∀ R : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (0 : ℝ) 1,
      R ≤ ‖segmentPoint (vertex n) (vertex (n + 1)) t‖)
    (h : LRWArcInequalities (fun lambda k ↦
      segmentIntegral f lambda (vertex k) (vertex (k + 1)))) :
    ∃ C : LocallyRectifiablePath,
      C.vertex = vertex ∧
      ∀ lambda : ℝ, 0 < lambda → lineIntegral C f lambda ≠ ∞ := by
  apply exists_path_of_lrw_arc_inequalities f vertex hescape _ h
  intro lambda _hlambda
  exact le_rfl

end Erdos515
