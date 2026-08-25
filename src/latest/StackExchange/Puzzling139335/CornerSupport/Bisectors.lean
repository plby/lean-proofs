import StackExchange.Puzzling139335.Definitions

/-!
# Separation of opposite corner bisectors

Two vectors of squared length `2` have nonpositive inner product when their
projections onto a nonzero vector are at most `-1` and at least `1`, respectively.
The proof uses Cauchy–Schwarz on their difference, so it does not require a choice
of planar coordinates.
-/

namespace Puzzling139335.CornerSupport

/-- Opposite support inequalities separate corner bisectors by at least a right angle. -/
theorem inner_le_zero_of_opposed_bisectors (u v δ : Plane) (hδ : δ ≠ 0)
    (hu : ‖u‖ ^ 2 = 2) (hv : ‖v‖ ^ 2 = 2)
    (huδ : inner ℝ u δ ≤ -‖δ‖) (hvδ : ‖δ‖ ≤ inner ℝ v δ) :
    inner ℝ u v ≤ 0 := by
  have hδpos : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  have hcs := real_inner_le_norm (v - u) δ
  rw [inner_sub_left] at hcs
  have hdist : (2 : ℝ) ≤ ‖v - u‖ := by nlinarith
  have hnorm := norm_sub_sq_real v u
  rw [hu, hv, real_inner_comm u v] at hnorm
  nlinarith [sq_nonneg (‖v - u‖ - 2)]

end Puzzling139335.CornerSupport
