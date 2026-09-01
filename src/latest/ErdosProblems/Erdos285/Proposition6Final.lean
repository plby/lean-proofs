/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.MovingBounds
import ErdosProblems.Erdos285.ScoreCrossing

/-!
# Erdős 285: unconditional final form of Martin's Proposition 6

This module joins the three independently verified parts of the construction:

* `ScoreCrossing` chooses the last scale whose full smooth-block score fits the
  requested number of terms and bounds its exact deficit by one deletion
  budget;
* `Proposition6` performs the concrete Lemma 12 descent and the exact finite
  padding/cardinality bookkeeping;
* `MovingBounds` proves the residual, deletion-budget, and five-prime-reservoir
  estimates at the moving lower endpoint.

The theorem below has no Martin-content hypotheses: it supplies the eventual
stream of finite approximation certificates used directly by Proposition 4.
-/

namespace Erdos285

open Filter Finset Real
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-- At every sufficiently large requested cardinality, the selected scale
carries an exact Proposition 6 certificate with precisely the number of main
terms left after reserving Proposition 7's correction count. -/
theorem eventually_martinApproximationCertificate :
    ∀ᶠ t : ℕ in atTop,
      Nonempty (ApproximationCertificate (1 : ℚ)
        (ScoreCrossing.martinSelectedScale t)
        (mainCount t
          (Proposition4.fifthRootFloor
            (ScoreCrossing.martinSelectedScale t)))) := by
  let X := ScoreCrossing.martinSelectedScale
  have hXtop : Tendsto X atTop atTop :=
    ScoreCrossing.martinSelectedScale_tendsto_atTop
  have hdescent := hXtop.eventually eventually_concreteRemovalDescent_one
  have hmoving := hXtop.eventually eventually_moving_proposition6_bounds
  have hreservoir := hXtop.eventually
    (eventually_two_budget_le_smoothReservoir (Real.exp (-1))
      (Real.exp_pos _) (by
        rw [Real.exp_le_one_iff]
        norm_num))
  have halphaBounds := hXtop.eventually
    Proposition4.eventually_martinLowerRatio_bounds
  have halphaThreeFourths := hXtop.eventually
    (Proposition4.martinLowerRatio_tendsto.eventually
      (Iio_mem_nhds (show Real.exp (-1) < (3 : ℝ) / 4 by
        exact Real.exp_neg_one_lt_half.trans (by norm_num))))
  have hxLarge := hXtop.eventually (eventually_ge_atTop 3)
  have hdeficit := ScoreCrossing.eventually_selected_deficit_le_deletionBudget
  filter_upwards [hdescent, hmoving, hreservoir, halphaBounds, halphaThreeFourths,
    hxLarge, hdeficit] with t hdescent hmoving hreservoir halphaBounds halphaXi hx hdeficit
  let x := X t
  let alpha := Proposition4.martinLowerRatio x
  let z := proposition6MainCutoff x
  let y := approximationCorrectionScale x
  let correction := correctionCount (Proposition4.fifthRootFloor x)
  let D := proposition6DeletionBudget x
  have halpha : 0 < alpha :=
    (Real.exp_pos (-1)).trans halphaBounds.1
  have halphaOne : alpha ≤ 1 := halphaBounds.2.le
  have hExpLe : Real.exp (-1) ≤ alpha := halphaBounds.1.le
  have hxpos : 0 < x := by omega
  obtain ⟨out⟩ := hdescent alpha halpha.le halphaXi
  have hscore : (initialSmoothBlock alpha x z).card + correction ≤ t := by
    simpa [x, alpha, z, correction, X, Proposition4.martinScore,
      Proposition4.martinInitialBlock, initialBlockAt] using
        ScoreCrossing.martinScore_selected_le t
  have hdeficit' :
      t - ((initialSmoothBlock alpha x z).card + correction) ≤ D := by
    simpa [x, alpha, z, correction, D, X, Proposition4.martinScore,
      Proposition4.martinInitialBlock, initialBlockAt] using hdeficit
  have hstartMeasure :
      (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure ≤
        ⌊z⌋₊ :=
    initialResidualApproximationState_one_measure_le_floor
  have hbudget : totalEliminationBudget x
      (initialResidualApproximationState (1 : ℚ) alpha x z).primePowerMeasure ≤ D := by
    exact (totalEliminationBudget_mono x hstartMeasure).trans (by
      simpa [x, z, D] using hmoving.2.2)
  have hrootNonneg : 0 ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹) :=
    Real.rpow_nonneg (Nat.cast_nonneg x) _
  have hyRoot : (y : ℝ) ≤ (x : ℝ) ^ ((5 : ℝ)⁻¹) := by
    dsimp [y, approximationCorrectionScale]
    exact Nat.floor_le hrootNonneg
  have hlogpos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlowerPositive : 0 < (Real.log (x : ℝ))⁻¹ := inv_pos.mpr hlogpos
  have hcertificate := exists_approximationCertificate_one_of_budget
    halpha halphaOne (Real.exp_pos (-1)) hExpLe le_rfl hxpos out
    hscore hdeficit' hbudget
    (by simpa [x, D] using hreservoir) hyRoot hlowerPositive
    (by simpa [x, alpha, z, D, div_eq_mul_inv, mul_assoc] using hmoving.1)
    (by simpa [x, alpha, z, D] using hmoving.2.1)
  simpa [x, correction, X, mainCount] using hcertificate

end

end Erdos285

#print axioms Erdos285.eventually_martinApproximationCertificate
