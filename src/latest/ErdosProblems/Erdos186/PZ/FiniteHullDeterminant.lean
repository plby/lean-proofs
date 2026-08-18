/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.OneStepAssembly

/-!
# Determinant cancellation for finite lattice hulls

This file proves the full-span maximal-simplex estimate used by the
finite-hull discrete-John reduction.  After normalizing a determinant-maximal
simplex, the hull lies in `[-1,1]^d`, hence its difference body lies in
`[-2,2]^d`.  The same affine determinant multiplies the hull and its
difference body, so it cancels.
-/

namespace Erdos186.PZ.OneStepAssembly

open Set MeasureTheory
open ConvexDensity
open scoped Pointwise BigOperators ENNReal

noncomputable section

/-- The maximal-simplex comparison constant is finite. -/
theorem normalizedBoxConstant_ne_top (d : ℕ) :
    normalizedBoxConstant d ≠ ⊤ := by
  exact ENNReal.div_ne_top (volume_closedAxisBox_ne_top _ _)
    (volume_normalizedInnerCube_ne_zero d)

/-- A real version of the dimension-only constant in the difference-body
estimate.  Taking a maximum with one matches the source interface without
changing the quantitative content. -/
def finiteHullDeterminantVolumeFactor (d : ℕ) : ℝ :=
  max 1 (((2 : ℝ≥0∞) ^ d * normalizedBoxConstant d).toReal)

theorem one_le_finiteHullDeterminantVolumeFactor (d : ℕ) :
    1 ≤ finiteHullDeterminantVolumeFactor d :=
  le_max_left _ _

theorem normalizedDifferenceConstant_le_ofReal (d : ℕ) :
    (2 : ℝ≥0∞) ^ d * normalizedBoxConstant d ≤
      ENNReal.ofReal (finiteHullDeterminantVolumeFactor d) := by
  have htop : (2 : ℝ≥0∞) ^ d * normalizedBoxConstant d ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (normalizedBoxConstant_ne_top d)
  rw [← ENNReal.ofReal_toReal htop]
  exact ENNReal.ofReal_mono (le_max_right _ _)

/-- The full-dimensional finite-hull determinant cancellation.  Both the
hull and its closed difference body are transformed by the same affine
Jacobian; after maximal-simplex normalization the latter lies in the
doubled cube, so that Jacobian cancels exactly. -/
theorem fullSpanFiniteHullDeterminantCancellation :
    FullSpanFiniteHullDeterminantCancellationStatement := by
  intro d _hd
  refine ⟨finiteHullDeterminantVolumeFactor d,
    one_le_finiteHullDeterminantVolumeFactor d, ?_⟩
  intro B Omega hOmega _hsub hspan
  rw [finiteHullDifferenceBody, volume_closedCoordinateDifferenceBody]
  let X : Finset (EuclideanPoint d) :=
    Intersection.realImage (boxLatticePointsIn B Omega)
  let L : Set (EuclideanPoint d) := convexHull ℝ (X : Set (EuclideanPoint d))
  obtain ⟨p, hp, e, hpX, he, _hinner, houter, hbox⟩ :=
    exists_comparable_enclosing_box X hspan
  have hbody :
      e.linear '' euclideanClosedDifferenceBody L ⊆
        normalizedDoubleCube d :=
    linear_image_closedDifferenceBody_subset_normalizedDoubleCube e L houter
  let c : ℝ≥0∞ := affineEquivVolumeFactor e
  have hc0 : c ≠ 0 := affineEquivVolumeFactor_ne_zero e
  have hctop : c ≠ ⊤ := affineEquivVolumeFactor_ne_top e
  have hscaled :
      c * volume (euclideanClosedDifferenceBody L) ≤
        c * (((2 : ℝ≥0∞) ^ d * normalizedBoxConstant d) * volume L) := by
    calc
      c * volume (euclideanClosedDifferenceBody L) =
          volume (e.linear '' euclideanClosedDifferenceBody L) := by
        simpa [c, affineEquivVolumeFactor] using
          (volume_linearEquivImage e.linear
            (euclideanClosedDifferenceBody L)).symm
      _ ≤ volume (normalizedDoubleCube d) := measure_mono hbody
      _ = (2 : ℝ≥0∞) ^ d * volume (normalizedOuterCube d) :=
        volume_normalizedDoubleCube d
      _ ≤ (2 : ℝ≥0∞) ^ d *
          (normalizedBoxConstant d * volume (e '' L)) := by
        gcongr
      _ = c * (((2 : ℝ≥0∞) ^ d * normalizedBoxConstant d) * volume L) := by
        rw [volume_affineEquivImage]
        change (2 : ℝ≥0∞) ^ d *
            (normalizedBoxConstant d * (c * volume L)) = _
        ac_rfl
  have hcancelled :
      volume (euclideanClosedDifferenceBody L) ≤
        ((2 : ℝ≥0∞) ^ d * normalizedBoxConstant d) * volume L :=
    (ENNReal.mul_le_mul_iff_right hc0 hctop).mp hscaled
  have hconstant := normalizedDifferenceConstant_le_ofReal d
  have hL : L ⊆ Omega := by
    simpa [L, X, finiteLatticeHull] using
      (finiteLatticeHull_subset (B := B) hOmega)
  calc
    volume (euclideanClosedDifferenceBody L) ≤
        ((2 : ℝ≥0∞) ^ d * normalizedBoxConstant d) * volume L :=
      hcancelled
    _ ≤ ENNReal.ofReal (finiteHullDeterminantVolumeFactor d) * volume L := by
      gcongr
    _ ≤ ENNReal.ofReal (finiteHullDeterminantVolumeFactor d) * volume Omega := by
      gcongr

/-- The determinant-cancellation estimate in the exact all-rank form used by
the finite-hull discrete-John reduction. -/
theorem finiteHullDeterminantCancellation :
    FiniteHullDeterminantCancellationStatement :=
  finiteHullDeterminantCancellation_of_fullSpan
    fullSpanFiniteHullDeterminantCancellation

/-- The determinant normalization and unconditional discrete-John theorem
remove every geometric premise of PZ Lemma 7 except the active full-rank
lattice-count/volume bridge. -/
theorem pzLemmaSeven_of_fullRankVolumeBridge
    (hFullRank : FullRankVolumeBridgeStatement) :
    PZLemmaSevenStatement :=
  pzLemmaSeven_of_maximalSimplex
    fullSpanFiniteHullDeterminantCancellation hFullRank

end

end Erdos186.PZ.OneStepAssembly
