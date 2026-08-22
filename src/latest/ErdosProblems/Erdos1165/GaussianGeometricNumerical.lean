/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.GaussianGeometricSchedule
import ErdosProblems.Erdos1165.AppendixA11A12Numerical

/-!
# Absorption of the geometric A.11--A.12 cost

For a fixed first scale, the centered-prefix reserve is constant.  The
shifted A.11 error and the sharply summed geometric A.12 cost are both a
constant times `q^(3/5)`.  The positive slack in
`Proposition13Scales.costExponent` therefore absorbs their sum.
-/

open Filter

namespace Erdos1165.GaussianGeometricNumerical

noncomputable section

open ProfileA11Assembly GaussianBlockFactorization GaussianGeometricSchedule
  AppendixA11A12OnePoint AppendixA11A12ScaleCertificate
  AppendixA11A12Numerical Proposition13Scales

/-- Fixed coefficient containing the exact prefix reserve, the complete
A.11 coefficient, and the sharp A.12 geometric cost coefficient. -/
def geometricProfileCostCoefficient (s : ℕ) : ℝ :=
  max (centeredPrefixReserve s) 0 +
    a11ErrorCoefficient (1 / 5 : ℝ) 2 1 10 + 26214505

lemma geometricProfileCostCoefficient_nonneg (s : ℕ) :
    0 ≤ geometricProfileCostCoefficient s := by
  unfold geometricProfileCostCoefficient
  have ha11 : 0 ≤ a11ErrorCoefficient (1 / 5 : ℝ) 2 1 10 :=
    a11ErrorCoefficient_nonneg (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  positivity

/-- Finite cost estimate for the canonical geometric schedule. -/
lemma canonicalGeometric_multiblockProfileCost_le
    {s q : ℕ} (hs : 32 ≤ s) (hsq : s ≤ q) :
    multiblockProfileCost q s (1 / 5 : ℝ) 2 1 10
        (geometricSchedule s (geometricDepth s q) q) ≤
      geometricProfileCostCoefficient s * (q : ℝ) ^ (3 / 5 : ℝ) := by
  have hterminal := geometricDepth_terminal_lower (show 0 < s by omega) hsq
  have hupper := geometricDepth_terminal_upper (show 0 < s by omega) hsq
  have hblock := geometricSchedule_totalCost_le_sharp hs hterminal hupper
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hpowOne : (1 : ℝ) ≤ (q : ℝ) ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow hqOne (by norm_num)
  have hprefix : centeredPrefixReserve s ≤
      max (centeredPrefixReserve s) 0 * (q : ℝ) ^ (3 / 5 : ℝ) := by
    calc
      centeredPrefixReserve s ≤ max (centeredPrefixReserve s) 0 := le_max_left _ _
      _ ≤ max (centeredPrefixReserve s) 0 * (q : ℝ) ^ (3 / 5 : ℝ) := by
        have hmax : 0 ≤ max (centeredPrefixReserve s) 0 := le_max_right _ _
        nlinarith
  unfold multiblockProfileCost geometricProfileCostCoefficient
  calc
    centeredPrefixReserve s +
          a11ErrorCoefficient (1 / 5 : ℝ) 2 1 10 *
            (q : ℝ) ^ (3 * (1 / 5 : ℝ)) +
          gaussianBlockTotalCost
            (geometricSchedule s (geometricDepth s q) q) ≤
        max (centeredPrefixReserve s) 0 * (q : ℝ) ^ (3 / 5 : ℝ) +
          a11ErrorCoefficient (1 / 5 : ℝ) 2 1 10 *
            (q : ℝ) ^ (3 / 5 : ℝ) +
          26214505 * (q : ℝ) ^ (3 / 5 : ℝ) := by
      norm_num only [mul_div_cancel_left] at hblock ⊢
      exact add_le_add (add_le_add hprefix le_rfl) hblock
    _ = (max (centeredPrefixReserve s) 0 +
          a11ErrorCoefficient (1 / 5 : ℝ) 2 1 10 + 26214505) *
        (q : ℝ) ^ (3 / 5 : ℝ) := by ring

/-- For every positive target slack, the entire fixed-prefix geometric
A.11--A.12 cost eventually fits inside the analytic half of `scaleCost`. -/
theorem eventually_canonicalGeometric_multiblockProfileCost_le_half_scaleCost
    {delta : ℝ} (hdelta : 0 < delta) {s : ℕ} (hs : 32 ≤ s) :
    ∀ᶠ n : ℕ in atTop,
      multiblockProfileCost (scaleIndex delta n) s (1 / 5 : ℝ) 2 1 10
          (geometricSchedule s (geometricDepth s (scaleIndex delta n))
            (scaleIndex delta n)) ≤
        (1 / 2 : ℝ) * scaleCost delta n := by
  have hexp : (3 / 5 : ℝ) < costExponent delta := by
    unfold costExponent
    linarith [scaleSlack_pos hdelta]
  have hcoeff := geometricProfileCostCoefficient_nonneg s
  have habsorbReal := eventually_const_mul_rpow_le_half_rpow hexp hcoeff
  have habsorb := (tendsto_scaleIndex_atTop delta).eventually habsorbReal
  have hqtop := (tendsto_scaleIndex_atTop delta).eventually
    (eventually_ge_atTop (s : ℝ))
  filter_upwards [habsorb, hqtop, eventually_scaleIndex_pos delta]
      with n habsorbN hqs hqpos
  have hsq : s ≤ scaleIndex delta n := by exact_mod_cast hqs
  have hfinite := canonicalGeometric_multiblockProfileCost_le hs hsq
  have hpowNonneg : 0 ≤
      (scaleIndex delta n : ℝ) ^ costExponent delta := by positivity
  calc
    multiblockProfileCost (scaleIndex delta n) s (1 / 5 : ℝ) 2 1 10
        (geometricSchedule s (geometricDepth s (scaleIndex delta n))
          (scaleIndex delta n)) ≤
      geometricProfileCostCoefficient s *
        (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ) := hfinite
    _ ≤ (1 / 2 : ℝ) *
        (scaleIndex delta n : ℝ) ^ costExponent delta := habsorbN
    _ = (1 / 2 : ℝ) * scaleCost delta n := rfl

/-- Compatibility form: the analytic profile cost also fits inside the full
budget. -/
theorem eventually_canonicalGeometric_multiblockProfileCost_le_scaleCost
    {delta : ℝ} (hdelta : 0 < delta) {s : ℕ} (hs : 32 ≤ s) :
    ∀ᶠ n : ℕ in atTop,
      multiblockProfileCost (scaleIndex delta n) s (1 / 5 : ℝ) 2 1 10
          (geometricSchedule s (geometricDepth s (scaleIndex delta n))
            (scaleIndex delta n)) ≤
        scaleCost delta n := by
  filter_upwards
      [eventually_canonicalGeometric_multiblockProfileCost_le_half_scaleCost
        hdelta hs]
      with n hcost
  have hscale : 0 ≤ scaleCost delta n := by
    unfold scaleCost
    positivity
  linarith

/-- Eventual numerical one-point comparison for the canonical geometric
schedule, before the deterministic profile embedding is applied. -/
theorem eventually_onePointBound_le_canonicalGeometricProfileLower
    {delta : ℝ} (hdelta : 0 < delta) {s : ℕ} (hs : 32 ≤ s) :
    ∀ᶠ n : ℕ in atTop,
      onePointBound delta n ≤
        multiblockProfileLower (scaleIndex delta n) (1 / 5 : ℝ) 2 1 10
          (geometricSchedule s (geometricDepth s (scaleIndex delta n))
            (scaleIndex delta n)) := by
  filter_upwards
      [eventually_canonicalGeometric_multiblockProfileCost_le_scaleCost
        hdelta hs,
       (tendsto_scaleIndex_atTop delta).eventually
        (eventually_ge_atTop (s : ℝ))]
      with n hcost hqs
  have hsq : s ≤ scaleIndex delta n := by exact_mod_cast hqs
  cases hdepth : geometricDepth s (scaleIndex delta n) with
  | zero =>
      change onePointBound delta n ≤
        multiblockProfileLower (scaleIndex delta n) (1 / 5 : ℝ) 2 1 10
          ([terminalGeometricBlock s (scaleIndex delta n)])
      apply onePointBound_le_multiblockProfileLower_of_cost hsq
      simpa [hdepth, chosenProfileDelta] using hcost
  | succ j =>
      change onePointBound delta n ≤
        multiblockProfileLower (scaleIndex delta n) (1 / 5 : ℝ) 2 1 10
          (completeGeometricBlock s ::
            geometricSchedule (2 * s) j (scaleIndex delta n))
      apply onePointBound_le_multiblockProfileLower_of_cost hsq
      simpa [hdepth, chosenProfileDelta] using hcost

/-- Eventual numerical comparison with the walk-facing annular-history loss
kept explicit. -/
theorem eventually_onePointBound_le_annularHistoryLoss_mul_canonicalGeometricProfileLower
    {delta : ℝ} (hdelta : 0 < delta) {s : ℕ} (hs : 32 ≤ s) :
    ∀ᶠ n : ℕ in atTop,
      onePointBound delta n ≤
        annularHistoryLoss delta n *
          multiblockProfileLower (scaleIndex delta n) (1 / 5 : ℝ) 2 1 10
            (geometricSchedule s (geometricDepth s (scaleIndex delta n))
              (scaleIndex delta n)) := by
  filter_upwards
      [eventually_canonicalGeometric_multiblockProfileCost_le_half_scaleCost
        hdelta hs,
       (tendsto_scaleIndex_atTop delta).eventually
        (eventually_ge_atTop (s : ℝ))]
      with n hcost hqs
  have hsq : s ≤ scaleIndex delta n := by exact_mod_cast hqs
  cases hdepth : geometricDepth s (scaleIndex delta n) with
  | zero =>
      change onePointBound delta n ≤ annularHistoryLoss delta n *
        multiblockProfileLower (scaleIndex delta n) (1 / 5 : ℝ) 2 1 10
          ([terminalGeometricBlock s (scaleIndex delta n)])
      apply onePointBound_le_annularHistoryLoss_mul_multiblockProfileLower_of_cost hsq
      simpa [hdepth, chosenProfileDelta] using hcost
  | succ j =>
      change onePointBound delta n ≤ annularHistoryLoss delta n *
        multiblockProfileLower (scaleIndex delta n) (1 / 5 : ℝ) 2 1 10
          (completeGeometricBlock s ::
            geometricSchedule (2 * s) j (scaleIndex delta n))
      apply onePointBound_le_annularHistoryLoss_mul_multiblockProfileLower_of_cost hsq
      simpa [hdepth, chosenProfileDelta] using hcost
end

end Erdos1165.GaussianGeometricNumerical
