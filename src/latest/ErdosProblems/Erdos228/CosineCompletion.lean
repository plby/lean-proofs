import ErdosProblems.Erdos228.CosineGeometry
import ErdosProblems.Erdos228.CosineParameters
import ErdosProblems.Erdos228.CosineRootContactCount
import ErdosProblems.Erdos228.FinalAssembly

/-!
# Unconditional cosine package for Erdős Problem 228

This module combines the normalized derivative argument, maximal bad-cell
runs, the endpoint geometry, and the Chebyshev root count into the concrete
cosine package consumed by the final analytic assembly.
-/

namespace Erdos228.CosineConstruction

open Filter Set

noncomputable section

/-- All data furnished by the cosine construction at a fixed scale. -/
structure CosinePackage (n : ℕ) where
  t : ℕ
  gamma : ℝ
  parameters : Parameters n t gamma
  family : Erdos228.OddSine.SuitableIntervalFamily n
  base_card : (family.base.card : ℝ) ≤ gamma * n
  upper : ∀ theta, |evenCosine t theta| ≤ Real.sqrt n
  lower : ∀ theta, Erdos228.InFundamentalAngle theta →
    ¬Erdos228.OddSine.IsDangerous family theta →
      cosineDelta gamma * Real.sqrt n ≤ |evenCosine t theta|

theorem sevenCellProperty_of_parameters
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    SevenCellProperty n t gamma := by
  apply sevenCellProperty_of_normalized_good hparam
  exact normalizedH_re_hasGoodCellInEverySeven t hparam.eta_pos hparam.eta_lt

theorem endpoint_threshold_bounds
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    cosineThreshold n gamma ≤ |evenCosine t 0| ∧
      cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)| := by
  have hthreshold := cosineThreshold_lt_half_normalization hparam
  have hscale : 0 < Real.sqrt (2 ^ (t + 1) : ℝ) := by positivity
  constructor
  · rw [evenCosine_eq_normalizedH]
    simp only [mul_zero]
    rw [normalizedH_re_zero_of_odd hparam.t_odd]
    simp only [abs_mul, abs_one, mul_one, abs_of_pos hscale]
    linarith
  · rw [evenCosine_eq_normalizedH]
    have harg : 2 * (evenT t : ℝ) * (Real.pi / 2) =
        (evenT t : ℝ) * Real.pi := by ring
    rw [harg, normalizedH_re_evenT_mul_pi_of_odd hparam.t_odd]
    simp only [abs_mul, abs_one, mul_one, abs_of_pos hscale]
    linarith

theorem suitableFamily_base_card_le
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma)
    (hseven : SevenCellProperty n t gamma)
    (hgeom : GeometricCertificate n t gamma) :
    ((suitableIntervalFamilyOfDangerousRuns hparam.n_pos hseven hgeom).base.card : ℝ) ≤
      gamma * n := by
  have hend := endpoint_threshold_bounds hparam
  have hcard := card_firstQuadrantRuns_le_parameterNumerator hparam.n_pos
    (cosineThreshold_pos hparam.n_pos hparam.gamma_pos).le hend.1 hend.2
  rw [suitableFamily_base_card hparam.n_pos hseven hgeom]
  have hcardR : ((firstQuadrantRuns n t gamma).card : ℝ) ≤
      parameterNumerator t := by exact_mod_cast hcard
  rwa [hparam.equation]

/-- The complete cosine package associated to any admissible parameter
triple. -/
def cosinePackageOfParameters
    {n t : ℕ} {gamma : ℝ} (hparam : Parameters n t gamma) :
    CosinePackage n := by
  let hseven : SevenCellProperty n t gamma :=
    sevenCellProperty_of_parameters hparam
  let hgeom : GeometricCertificate n t gamma :=
    geometricCertificate_of_parameters hparam
  let F : Erdos228.OddSine.SuitableIntervalFamily n :=
    suitableIntervalFamilyOfDangerousRuns hparam.n_pos hseven hgeom
  refine
    { t := t
      gamma := gamma
      parameters := hparam
      family := F
      base_card := ?_
      upper := ?_
      lower := ?_ }
  · simpa only [F] using suitableFamily_base_card_le hparam hseven hgeom
  · intro theta
    exact abs_evenCosine_le_sqrt_of_parameters hparam.toEvenParameters theta
  · intro theta htheta hout
    have hfirst : ∀ x ∈ Icc (0 : ℝ) (Real.pi / 2),
        ¬InBaseFamily F x → cosineThreshold n gamma ≤ |evenCosine t x| := by
      intro x hx hbase
      apply le_of_not_gt
      intro hsmall
      apply hbase
      obtain ⟨I, hI, hxI⟩ :=
        low_point_covered_by_firstQuadrantIntervals hparam hx hsmall
      refine ⟨I, ?_, hxI⟩
      change I ∈ firstQuadrantIntervals n t gamma
      exact hI
    have hlower := lower_on_fundamental_of_lower_off_base F hfirst theta
      (by simpa only [Erdos228.InFundamentalAngle] using htheta) hout
    simpa only [cosineThreshold] using hlower

/-- For every sufficiently large scale, the concrete cosine parameters and
dangerous interval family exist with all bounds needed by the final
assembly. -/
theorem eventually_exists_cosinePackage :
    ∀ᶠ n : ℕ in atTop, Nonempty (CosinePackage n) := by
  filter_upwards [eventually_exists_parameters] with n hparam
  obtain ⟨t, gamma, hparam⟩ := hparam
  exact ⟨cosinePackageOfParameters hparam⟩

end

end Erdos228.CosineConstruction
