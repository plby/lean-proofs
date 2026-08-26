import ErdosProblems.Erdos1164.SpatialPotential
import ErdosProblems.Erdos1164.HitRace

/-! # Uniform finite-disc hitting estimates from the boundary potential window -/

open MeasureTheory

namespace Erdos1164

open Erdos1165 Erdos1165.Annulus Erdos1165.AnnulusHarnack
open Erdos1165.PotentialConvergence Erdos1165.PotentialEuclideanGeometry
open Erdos1165.PlanarPotential Erdos1165.GreenFunction Erdos1165.GreenProbability
open Erdos1165.GreenAsymptotic Erdos1165.GreenHarnack

private theorem hitProbability_green_quotient (R : ℕ) (x y : Point)
    (hy : y ∈ closedDisc R) :
    fairSteps.real (hitBeforeExitEvent (closedDisc R) x y) =
      (infiniteGreen (closedDisc R) x y).toReal /
        (infiniteGreen (closedDisc R) y y).toReal := by
  rw [measureReal_def, fairSteps_hitBeforeExitEvent,
    ← simpleRandomWalkFrom_walkHitBeforeExit,
    simpleRandomWalkFrom_hitBeforeExit_closedDisc_toReal_eq_green_div R x y hy]

private theorem green_boundary_window {R : ℕ} (hR : 8 ≤ R) {x y : Point}
    (hx : x ∈ closedDisc R) (hy : euclideanRadius y ≤ (R : ℝ) / 4) :
    potentialSlope * Real.log (R : ℝ) - potentialError - planarPotentialKernel (x - y) ≤
        (infiniteGreen (closedDisc R) x y).toReal ∧
      (infiniteGreen (closedDisc R) x y).toReal ≤
        potentialSlope * Real.log (R : ℝ) + potentialError - planarPotentialKernel (x - y) := by
  exact ⟨potentialBoundaryLower_sub_le_infiniteGreen_toReal R hx
      (fun z hz ↦ (boundary_potential_window hR hy hz).1),
    infiniteGreen_toReal_le_of_potentialBoundary_le R hx
      (fun z hz ↦ (boundary_potential_window hR hy hz).2)⟩

/-- Lower killed hitting probability, with an explicit nonnegative numerator. -/
theorem killedHit_lower {R : ℕ} (hR : 8 ≤ R) {x y : Point}
    (hx : x ∈ closedDisc R) (hy : y ∈ closedDisc R)
    (hyquarter : euclideanRadius y ≤ (R : ℝ) / 4)
    (hnum : 0 ≤ potentialSlope * Real.log (R : ℝ) - potentialError -
      planarPotentialKernel (x - y)) :
    (potentialSlope * Real.log (R : ℝ) - potentialError - planarPotentialKernel (x - y)) /
      (potentialSlope * Real.log (R : ℝ) + potentialError) ≤
        fairSteps.real (hitBeforeExitEvent (closedDisc R) x y) := by
  rw [hitProbability_green_quotient R x y hy]
  have hxy := green_boundary_window hR hx hyquarter
  have hyy := green_boundary_window hR hy hyquarter
  simp only [sub_self, planarPotentialKernel_zero, sub_zero] at hyy
  have hdiag := one_le_infiniteGreen_closedDisc_diagonal_toReal R hy
  have hpos : 0 < (infiniteGreen (closedDisc R) y y).toReal := by linarith
  have hupper : 0 < potentialSlope * Real.log (R : ℝ) + potentialError :=
    hpos.trans_le hyy.2
  apply (div_le_div_iff₀ hupper hpos).mpr
  calc
    _ ≤ (potentialSlope * Real.log (R : ℝ) - potentialError - planarPotentialKernel (x - y)) *
        (potentialSlope * Real.log (R : ℝ) + potentialError) :=
      mul_le_mul_of_nonneg_left hyy.2 hnum
    _ ≤ _ := mul_le_mul_of_nonneg_right hxy.1 hupper.le

/-- Upper killed hitting probability, requiring only positivity of the lower
Green denominator. -/
theorem killedHit_upper {R : ℕ} (hR : 8 ≤ R) {x y : Point}
    (hx : x ∈ closedDisc R) (hy : y ∈ closedDisc R)
    (hyquarter : euclideanRadius y ≤ (R : ℝ) / 4)
    (hden : 0 < potentialSlope * Real.log (R : ℝ) - potentialError) :
    fairSteps.real (hitBeforeExitEvent (closedDisc R) x y) ≤
      (potentialSlope * Real.log (R : ℝ) + potentialError - planarPotentialKernel (x - y)) /
        (potentialSlope * Real.log (R : ℝ) - potentialError) := by
  rw [hitProbability_green_quotient R x y hy]
  have hxy := green_boundary_window hR hx hyquarter
  have hyy := green_boundary_window hR hy hyquarter
  simp only [sub_self, planarPotentialKernel_zero, sub_zero] at hyy
  have hdiag := one_le_infiniteGreen_closedDisc_diagonal_toReal R hy
  have hpos : 0 < (infiniteGreen (closedDisc R) y y).toReal := by linarith
  apply (div_le_div_iff₀ hpos hden).mpr
  calc
    _ ≤ (infiniteGreen (closedDisc R) x y).toReal *
        (infiniteGreen (closedDisc R) y y).toReal :=
      mul_le_mul_of_nonneg_left hyy.1 ENNReal.toReal_nonneg
    _ ≤ _ := mul_le_mul_of_nonneg_right hxy.2 hpos.le

end Erdos1164
