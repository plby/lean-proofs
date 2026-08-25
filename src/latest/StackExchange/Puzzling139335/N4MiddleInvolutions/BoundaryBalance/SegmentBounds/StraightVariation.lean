import StackExchange.Puzzling139335.LoopVariation.Geometric.Arc
import Wikipedia.SchoenfliesTheorem.Polygonal
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-! Concrete upper and lower bounds for variation on a straight segment. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

open ArcVariation

noncomputable section

/-- The finite-chain variation of a straight parametrization never exceeds
the distance between its endpoints. -/
theorem variationOn_lineMap_le_dist {ε : ℝ} (hε : 0 ≤ ε)
    (a b : Schoenflies.Plane) :
    variationOn ε (AffineMap.lineMap a b : ℝ → Schoenflies.Plane)
      (Icc (0 : ℝ) 1) ≤ dist a b := by
  apply csSup_le (scoresOn_nonempty _ _ _)
  rintro r ⟨xs, hxs, rfl⟩
  have hbound := chainScore_le_mul_interval (by norm_num : (0 : ℝ) ≤ 1)
    (dist_nonneg (x := a) (y := b)) (f := AffineMap.lineMap a b)
    (ε := ε) (fun u _ v _ huv => ?_) hxs
  · simpa using hbound
  · rw [chord, dist_lineMap_lineMap, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr huv)]
    apply max_le
    · nlinarith
    · exact mul_nonneg dist_nonneg (sub_nonneg.mpr huv)

/-- For a genuine straight segment, its intrinsic arc variation is bounded
by its Euclidean length. This follows from the concrete chain supremum. -/
theorem arcVariation_segment_le_dist {ε : ℝ} (hε : 0 ≤ ε)
    {a b : Schoenflies.Plane} (hab : a ≠ b) :
    LoopVariation.arcVariation ε (segment ℝ a b) ≤ dist a b := by
  rw [LoopVariation.arcVariation_eq_of_parametrization ε
    (Schoenflies.isArc_segment hab) AffineMap.lineMap_continuous.continuousOn
    (Schoenflies.injOn_lineMap hab) (segment_eq_image_lineMap ℝ a b).symm]
  exact variationOn_lineMap_le_dist hε a b

/-- The endpoint chord gives the companion lower estimate; the discrepancy
from Euclidean length is at most the resolution. -/
theorem dist_sub_le_arcVariation_segment {ε : ℝ} (hε : 0 < ε)
    {a b : Schoenflies.Plane} (hab : a ≠ b) :
    dist a b - ε ≤ LoopVariation.arcVariation ε (segment ℝ a b) := by
  rw [LoopVariation.arcVariation_eq_of_parametrization ε
    (Schoenflies.isArc_segment hab) AffineMap.lineMap_continuous.continuousOn
    (Schoenflies.injOn_lineMap hab) (segment_eq_image_lineMap ℝ a b).symm]
  have h := chord_le_variationOn_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (f := AffineMap.lineMap a b) AffineMap.lineMap_continuous.continuousOn hε
  simp only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at h
  exact (le_max_left (dist a b - ε) 0).trans h

end

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
