/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.FixedMultiplicityTransfer
import ErdosProblems.Erdos446.UpperAsymptoticAssembly

/-!
# Erdős Problem 446: draft public interface and final assembly

This file records the exact, unconditional statements that the final main file
must expose.  Its assembly theorems are deliberately named `_of_...`: they do
not replace the missing analytic estimates, but show that those estimates have
exactly the strength needed for the public resolution.
-/

namespace Erdos446

open Filter Real Asymptotics
open scoped Topology

/-- Ford's sharp answer to the growth-rate question. -/
def GrowthResolution446 : Prop :=
  delta =Θ[atTop] growth446

/-- Ford's fixed-multiplicity theorem.  The direction is important:
`delta = O(deltaR r)` says that `deltaR r` is bounded below by a positive
constant (depending on the fixed `r`) times `delta`. -/
def FixedMultiplicityResolution446 : Prop :=
  ∀ r : ℕ, 1 ≤ r → delta =O[atTop] (deltaR r)

/-- The complete resolution, including the literal negative answer to the
question whether `deltaR 1 = o(delta)`. -/
def Resolution446 : Prop :=
  GrowthResolution446 ∧
    FixedMultiplicityResolution446 ∧
      ¬ (deltaR 1 =o[atTop] delta)

/-- The half-open exact-multiplicity density is at most the corresponding
half-open union density. -/
theorem epsilonR_le_epsilon (r y z : ℕ) (hr : 1 ≤ r) :
    epsilonR r y z ≤ epsilon y z := by
  unfold epsilonR epsilon
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Finset.card_le_card (by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
      exact And.intro hm.1 (by omega))
  · exact_mod_cast Nat.zero_le (intervalLcmIoc y z)

/-- The sharp growth theorem makes `delta` eventually nonzero.  This is the
non-vacuity input needed to turn Ford's fixed-multiplicity lower comparison
into a disproof of a little-oh assertion. -/
theorem delta_eventually_ne_zero_of_growthResolution
    (hgrowth : GrowthResolution446) :
    ∀ᶠ n : ℕ in atTop, delta n ≠ 0 := by
  rcases hgrowth.2.bound with ⟨C, hC⟩
  filter_upwards [eventually_growthDenominator446_pos, hC] with n hden hbound
  intro hzero
  have hgrowthPos : 0 < growth446 n := inv_pos.mpr hden
  rw [hzero, norm_zero, mul_zero] at hbound
  have hgrowthNonpos : growth446 n ≤ 0 := by
    simpa [Real.norm_eq_abs, abs_of_pos hgrowthPos] using hbound
  exact (not_lt_of_ge hgrowthNonpos) hgrowthPos

/-- Ford's stronger fixed-multiplicity theorem really disproves the proposed
little-oh statement; this is not merely a comparison between potentially zero
functions. -/
theorem not_deltaR_one_isLittleO_delta_of_resolutions
    (hgrowth : GrowthResolution446)
    (hfixed : FixedMultiplicityResolution446) :
    ¬ (deltaR 1 =o[atTop] delta) := by
  exact (hfixed 1 (by omega)).not_isLittleO
    (delta_eventually_ne_zero_of_growthResolution hgrowth).frequently

/-- Assembly of the exact public resolution from its two substantive parts. -/
theorem resolution446_of_growth_and_fixedMultiplicity
    (hgrowth : GrowthResolution446)
    (hfixed : FixedMultiplicityResolution446) :
    Resolution446 :=
  ⟨hgrowth, hfixed,
    not_deltaR_one_isLittleO_delta_of_resolutions hgrowth hfixed⟩

/-- Transfer a half-open fixed-multiplicity lower bound to a Theta estimate
for the half-open exact-multiplicity density. -/
theorem epsilonR_isTheta_growth446_of_lower
    {r : ℕ} (hr : 1 ≤ r)
    (hepsilon : (fun n => epsilon n (2 * n)) =Θ[atTop] growth446)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ᶠ n : ℕ in atTop,
      c * epsilon n (2 * n) ≤ epsilonR r n (2 * n)) :
    (fun n => epsilonR r n (2 * n)) =Θ[atTop] growth446 := by
  constructor
  · have hle : (fun n => epsilonR r n (2 * n)) =O[atTop]
        (fun n => epsilon n (2 * n)) := by
      apply IsBigO.of_bound 1
      filter_upwards [] with n
      have hR := epsilonR_nonneg r n (2 * n)
      have hE := epsilon_nonneg n (2 * n)
      simpa [Real.norm_eq_abs, abs_of_nonneg hR, abs_of_nonneg hE] using
        epsilonR_le_epsilon r n (2 * n) hr
    exact hle.trans hepsilon.1
  · have hle : (fun n => epsilon n (2 * n)) =O[atTop]
        (fun n => epsilonR r n (2 * n)) := by
      apply IsBigO.of_bound c⁻¹
      filter_upwards [hlower] with n hn
      have hR := epsilonR_nonneg r n (2 * n)
      have hE := epsilon_nonneg n (2 * n)
      rw [Real.norm_eq_abs, abs_of_nonneg hE, Real.norm_eq_abs,
        abs_of_nonneg hR, inv_mul_eq_div]
      exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hn)
    exact hepsilon.2.trans hle

/-- The one-endpoint error transfers the half-open exact-multiplicity Theta
estimate to the literal open interval in the problem. -/
theorem deltaR_isTheta_growth446_of_epsilonR
    {r : ℕ}
    (hepsilonR : (fun n => epsilonR r n (2 * n)) =Θ[atTop] growth446) :
    (deltaR r) =Θ[atTop] growth446 := by
  apply isTheta_of_isTheta_of_abs_sub_isLittleO hepsilonR
    endpointError_isLittleO_growth446
  filter_upwards [eventually_gt_atTop 0] with n hn
  have h := abs_deltaR_sub_epsilonR_le r n hn
  have herrpos : 0 < (1 / (2 * n : Real)) := by positivity
  simpa only [abs_abs, abs_of_pos herrpos] using h

/-- Exact final assembly from the two half-open analytic statements.  These
are the natural outputs of Ford's counting argument. -/
theorem resolution446_of_halfOpen_estimates
    (hepsilon : (fun n => epsilon n (2 * n)) =Θ[atTop] growth446)
    (hfixed : ∀ r : ℕ, 1 ≤ r → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        c * epsilon n (2 * n) ≤ epsilonR r n (2 * n)) :
    Resolution446 := by
  have hgrowth : GrowthResolution446 :=
    delta_isTheta_growth446_of_epsilon hepsilon
  have hfixedOpen : FixedMultiplicityResolution446 := by
    intro r hr
    rcases hfixed r hr with ⟨c, hc, hcr⟩
    have hRhalf := epsilonR_isTheta_growth446_of_lower hr hepsilon hc hcr
    have hRopen := deltaR_isTheta_growth446_of_epsilonR hRhalf
    exact hgrowth.1.trans hRopen.2
  exact resolution446_of_growth_and_fixedMultiplicity hgrowth hfixedOpen

/-- Minimal analytic dependency package for the complete result: the sharp
upper bound plus Ford's positive fixed-multiplicity lower comparison. -/
theorem resolution446_of_upper_and_fixedMultiplicity_lower
    (hupper : (fun n => epsilon n (2 * n)) =O[atTop] growth446)
    (hfixed : ∀ r : ℕ, 1 ≤ r → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        c * epsilon n (2 * n) ≤ epsilonR r n (2 * n)) :
    Resolution446 :=
  resolution446_of_halfOpen_estimates
    (epsilon_isTheta_growth446_of_upper hupper) hfixed

end Erdos446
