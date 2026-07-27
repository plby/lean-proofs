import Arxiv.Arxiv2407_19026.RegionBoost
import LeanCert.Tactic.IntervalAuto

/-!
# Certified numerical facts for the Section 4 profiles

The paper delegates its profile inequalities to Mathematica.  Here numerical
claims are kernel-checked using rational interval subdivision.  In particular,
the four profiles have *positive* slope on `[0.05,1]`; this certifies the sign
correction made in `Profiles.lean`.
-/

noncomputable section

namespace Arxiv2407_19026

set_option maxRecDepth 10000 in
theorem optimizedRamseySlope_beta0_pos :
    ∀ z ∈ Set.Icc (1 / 20 : ℝ) 1,
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (2 / 25) z := by
  unfold optimizedRamseySlope
  interval_bound_subdiv 20 8

set_option maxRecDepth 10000 in
theorem optimizedRamseySlope_beta1_pos :
    ∀ z ∈ Set.Icc (1 / 20 : ℝ) 1,
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (9 / 200) z := by
  unfold optimizedRamseySlope
  interval_bound_subdiv 20 8

set_option maxRecDepth 10000 in
theorem optimizedRamseySlope_beta2_pos :
    ∀ z ∈ Set.Icc (1 / 20 : ℝ) 1,
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (33 / 1000) z := by
  unfold optimizedRamseySlope
  interval_bound_subdiv 20 8

set_option maxRecDepth 10000 in
theorem optimizedRamseySlope_beta3_pos :
    ∀ z ∈ Set.Icc (1 / 20 : ℝ) 1,
      (1 / 10 : ℝ) ≤ optimizedRamseySlope (3 / 100) z := by
  unfold optimizedRamseySlope
  interval_bound_subdiv 20 8

end Arxiv2407_19026
