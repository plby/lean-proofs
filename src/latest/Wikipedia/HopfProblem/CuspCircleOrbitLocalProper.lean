import Wikipedia.HopfProblem.CuspCircleOrbitLocalAlgebra
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Properness of the opposite-weight Hopf invariant

The original radius identity gives an explicit bound on the two normal
coordinates in terms of their invariant. Consequently inverse images of
compact sets are compact, and the local Hopf map is a proper closed map.
No assertion about the global orbit space is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit

/-- A concrete coercive estimate for the unchanged Hopf invariant. -/
theorem norm_le_norm_hopfMap_add_one (z : ℂ × ℂ) :
    ‖z‖ ≤ ‖hopfMap z‖ + 1 := by
  have hfst : Complex.normSq (hopfMap z).1 ≤ ‖hopfMap z‖ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_fst_le _)
  have hsnd : (hopfMap z).2 ^ 2 ≤ ‖hopfMap z‖ ^ 2 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (sq_le_sq₀ (norm_nonneg (hopfMap z).2) (norm_nonneg (hopfMap z))).mpr
        (norm_snd_le (hopfMap z))
  have hsum : Complex.normSq z.1 + Complex.normSq z.2 ≤ 2 * ‖hopfMap z‖ := by
    apply (sq_le_sq₀
      (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
      (mul_nonneg (by norm_num) (norm_nonneg _))).mp
    nlinarith only [hfst, hsnd, hopfMap_radius_squared z, sq_nonneg ‖hopfMap z‖]
  simp only [Complex.normSq_eq_norm_sq] at hsum
  rw [Prod.norm_def]
  apply max_le
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    nlinarith only [hsum, sq_nonneg ‖z.2‖, sq_nonneg ‖hopfMap z‖]
  · apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    nlinarith only [hsum, sq_nonneg ‖z.1‖, sq_nonneg ‖hopfMap z‖]

/-- Bounded invariant coordinates have bounded original normal coordinates. -/
theorem hopfMap_preimage_isBounded {K : Set (ℂ × ℝ)} (hK : Bornology.IsBounded K) :
    Bornology.IsBounded (hopfMap ⁻¹' K) := by
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨R + 1, fun z hz => ?_⟩
  exact (norm_le_norm_hopfMap_add_one z).trans (add_le_add (hR _ hz) le_rfl)

/-- The actual opposite-weight Hopf invariant is proper. -/
theorem hopfMap_isProperMap : IsProperMap hopfMap := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hopfMap_continuous, fun K hK => ?_⟩
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨hK.isClosed.preimage hopfMap_continuous, hopfMap_preimage_isBounded hK.isBounded⟩

/-- Closed sets of original normal coordinates have closed invariant images. -/
theorem hopfMap_isClosedMap : IsClosedMap hopfMap :=
  hopfMap_isProperMap.isClosedMap

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit
