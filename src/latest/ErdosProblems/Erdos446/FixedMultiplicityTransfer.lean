/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.Counting

/-!
# Erdős Problem 446: transfer of the fixed-multiplicity estimate

Ford's prescribed-multiplicity argument is most naturally proved for the
half-open interval `(y, 2y]`.  This file isolates the exact asymptotic
bookkeeping needed after that analytic estimate is known.  In particular,
the density of the single endpoint is absorbed with an explicit loss of only
a factor two in the comparison constant.
-/

namespace Erdos446

open Filter Real
open scoped Topology

/-- Both literal open-interval densities are nonnegative. -/
theorem delta_nonneg (n : ℕ) : 0 ≤ delta n := by
  unfold delta
  positivity

theorem deltaR_nonneg (r n : ℕ) : 0 ≤ deltaR r n := by
  unfold deltaR
  positivity

/-- For positive multiplicity the exact level set is contained in the union
event.  Thus every fixed-multiplicity density is at most the union density. -/
theorem deltaR_le_delta {r n : ℕ} (hr : 1 ≤ r) : deltaR r n ≤ delta n := by
  have hcard :
      ((Finset.range (intervalLcm n)).filter
          (fun m ↦ divisorCount n m = r)).card ≤
        ((Finset.range (intervalLcm n)).filter
          (fun m ↦ 0 < divisorCount n m)).card := by
    apply Finset.card_le_card
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, hm.2.symm ▸ hr⟩
  unfold deltaR delta
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast hcard

/-- The tautological upper comparison `δ_r ≤ δ` in asymptotic notation. -/
theorem deltaR_isBigO_delta {r : ℕ} (hr : 1 ≤ r) :
    (fun n : ℕ ↦ deltaR r n) =O[atTop] delta := by
  apply Asymptotics.IsBigO.of_bound 1
  exact Eventually.of_forall fun n ↦ by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (deltaR_nonneg r n),
      abs_of_nonneg (delta_nonneg n), one_mul]
    exact deltaR_le_delta hr

/-- An eventual positive lower comparison is the reverse big-O relation. -/
theorem delta_isBigO_deltaR_of_eventual_lower
    {r : ℕ} {c : ℝ} (hc : 0 < c)
    (hcomp : ∀ᶠ n : ℕ in atTop, c * delta n ≤ deltaR r n) :
    delta =O[atTop] (fun n : ℕ ↦ deltaR r n) := by
  apply Asymptotics.IsBigO.of_bound c⁻¹
  filter_upwards [hcomp] with n hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (delta_nonneg n),
    abs_of_nonneg (deltaR_nonneg r n)]
  have hdiv : delta n ≤ deltaR r n / c :=
    (le_div_iff₀ hc).2 (by simpa only [mul_comm] using hn)
  simpa only [div_eq_inv_mul] using hdiv

/-- For positive `r`, Ford's lower comparison is equivalent to
`δ_r = Θ(δ)`, since the reverse inequality is automatic. -/
theorem deltaR_isTheta_delta_of_eventual_lower
    {r : ℕ} {c : ℝ} (hr : 1 ≤ r) (hc : 0 < c)
    (hcomp : ∀ᶠ n : ℕ in atTop, c * delta n ≤ deltaR r n) :
    (fun n : ℕ ↦ deltaR r n) =Θ[atTop] delta :=
  ⟨deltaR_isBigO_delta hr,
    delta_isBigO_deltaR_of_eventual_lower hc hcomp⟩

/-- A fixed lower comparison for Ford's half-open densities survives removal
of the right endpoint.  The explicit output constant `c / 2` is convenient
for the final statement of the problem.

The only asymptotic input used here is that the union density has Ford's
scale.  It makes the endpoint density `1 / (2n)` little-oh of the half-open
union density. -/
theorem eventually_deltaR_lower_of_epsilonR_lower
    {r : ℕ} {c : ℝ} (hc : 0 < c)
    (hTheta : (fun n : ℕ ↦ epsilon n (2 * n)) =Θ[atTop] growth446)
    (hFord : ∀ᶠ n : ℕ in atTop,
      c * epsilon n (2 * n) ≤ epsilonR r n (2 * n)) :
    ∀ᶠ n : ℕ in atTop, (c / 2) * delta n ≤ deltaR r n := by
  have hendpointEpsilon :
      (fun n : ℕ ↦ 1 / (2 * n : ℝ)) =o[atTop]
        (fun n : ℕ ↦ epsilon n (2 * n)) :=
    endpointError_isLittleO_growth446.trans_isBigO hTheta.2
  have hcoeff : 0 < c / (c + 2) := by positivity
  have hsmall := hendpointEpsilon.bound hcoeff
  filter_upwards [hFord, hsmall, eventually_gt_atTop 0]
    with n hFordn hsmalln hn
  have hdelta := abs_delta_sub_epsilon_le n hn
  have hdeltaR := abs_deltaR_sub_epsilonR_le r n hn
  have heps0 := epsilon_nonneg n (2 * n)
  have herr0 : 0 ≤ (1 / (2 * n : ℝ)) := by positivity
  have hsmall' :
      1 / (2 * n : ℝ) ≤ (c / (c + 2)) * epsilon n (2 * n) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg herr0,
      abs_of_nonneg heps0] using hsmalln
  rw [abs_le] at hdelta hdeltaR
  have hden : 0 < c + 2 := by positivity
  have hscaled :
      (c + 2) * (1 / (2 * n : ℝ)) ≤ c * epsilon n (2 * n) := by
    calc
      (c + 2) * (1 / (2 * n : ℝ)) ≤
          (c + 2) * ((c / (c + 2)) * epsilon n (2 * n)) :=
        mul_le_mul_of_nonneg_left hsmall' hden.le
      _ = c * epsilon n (2 * n) := by field_simp [hden.ne']
  nlinarith

/-- The finite prefix form of Ford's fixed-multiplicity theorem implies the
literal open-interval lower comparison, once the dyadic union estimate is
available. -/
theorem eventually_deltaR_lower_of_prefix_bounds
    {r : ℕ} {c cUnion CUnion : ℝ} {YUnion YR : ℕ}
    (hc : 0 < c) (hcUnion : 0 < cUnion) (hCUnion : 0 < CUnion)
    (hYUnion : 1 ≤ YUnion) (hYR : 1 ≤ YR)
    (hUnion : DyadicPrefixBounds cUnion CUnion YUnion)
    (hR : FixedMultiplicityPrefixLower r c YR) :
    ∀ᶠ n : ℕ in atTop, (c / 2) * delta n ≤ deltaR r n := by
  have hTheta := epsilon_isTheta_growth446_of_dyadicPrefixBounds
    hYUnion hcUnion hCUnion hUnion
  have hhalf : ∀ᶠ n : ℕ in atTop,
      c * epsilon n (2 * n) ≤ epsilonR r n (2 * n) := by
    filter_upwards [eventually_ge_atTop YR] with n hn
    exact epsilonR_lower_of_fixedMultiplicityPrefixLower hYR hR n hn
  exact eventually_deltaR_lower_of_epsilonR_lower hc hTheta hhalf

/-- An eventual positive lower comparison rules out little-oh.  This generic
form is useful independently of the divisor problem. -/
theorem not_isLittleO_of_eventually_pos_of_eventually_const_mul_le
    {f g : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hg : ∀ᶠ n : ℕ in atTop, 0 < g n)
    (hcomp : ∀ᶠ n : ℕ in atTop, c * g n ≤ f n) :
    ¬ f =o[atTop] g := by
  intro hlittle
  have hbound := hlittle.bound (half_pos hc)
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [hg, hcomp, hbound] with n hgn hcompn hboundn
    have hfn : 0 < f n := lt_of_lt_of_le (mul_pos hc hgn) hcompn
    simp only [Real.norm_eq_abs, abs_of_pos hfn, abs_of_pos hgn] at hboundn
    nlinarith
  exact hfalse.exists.elim fun _ h ↦ h

/-- A function Theta-equivalent to Ford's positive scale is eventually
strictly positive when it is pointwise nonnegative. -/
theorem eventually_pos_of_isTheta_growth446
    {f : ℕ → ℝ} (hf0 : ∀ n, 0 ≤ f n)
    (hTheta : f =Θ[atTop] growth446) :
    ∀ᶠ n : ℕ in atTop, 0 < f n := by
  rcases hTheta.2.bound with ⟨C, hC⟩
  filter_upwards [hC, eventually_growthDenominator446_pos]
    with n hCn hgrowthDen
  have hgrowth : 0 < growth446 n := inv_pos.mpr hgrowthDen
  have hfn0 := hf0 n
  have hfnne : f n ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero, mul_zero] at hCn
    have : ‖growth446 n‖ > 0 := norm_pos_iff.mpr hgrowth.ne'
    linarith
  exact lt_of_le_of_ne hfn0 (Ne.symm hfnne)

/-- Ford's fixed-`r` lower comparison directly gives the negative answer to
Erdős's little-oh question. -/
theorem deltaR_not_isLittleO_delta_of_eventual_lower
    {r : ℕ} {c : ℝ} (hc : 0 < c)
    (hTheta : delta =Θ[atTop] growth446)
    (hcomp : ∀ᶠ n : ℕ in atTop, c * delta n ≤ deltaR r n) :
    ¬ (fun n : ℕ ↦ deltaR r n) =o[atTop] delta := by
  apply not_isLittleO_of_eventually_pos_of_eventually_const_mul_le hc
    (eventually_pos_of_isTheta_growth446 delta_nonneg hTheta)
    hcomp

/-- Fully assembled fixed-multiplicity consequence of the two finite-count
inputs.  It returns both Ford's eventual comparison for the literal interval
and the resulting failure of little-oh. -/
theorem fixedMultiplicity_resolution_of_prefix_bounds
    {r : ℕ} {c cUnion CUnion : ℝ} {YUnion YR : ℕ}
    (hc : 0 < c) (hcUnion : 0 < cUnion) (hCUnion : 0 < CUnion)
    (hYUnion : 1 ≤ YUnion) (hYR : 1 ≤ YR)
    (hUnion : DyadicPrefixBounds cUnion CUnion YUnion)
    (hR : FixedMultiplicityPrefixLower r c YR) :
    (∀ᶠ n : ℕ in atTop, (c / 2) * delta n ≤ deltaR r n) ∧
      ¬ (fun n : ℕ ↦ deltaR r n) =o[atTop] delta := by
  have hcomp := eventually_deltaR_lower_of_prefix_bounds hc hcUnion hCUnion
    hYUnion hYR hUnion hR
  refine ⟨hcomp, ?_⟩
  have hepsTheta := epsilon_isTheta_growth446_of_dyadicPrefixBounds
    hYUnion hcUnion hCUnion hUnion
  have hdeltaTheta := delta_isTheta_growth446_of_epsilon hepsTheta
  exact deltaR_not_isLittleO_delta_of_eventual_lower (half_pos hc)
    hdeltaTheta hcomp

/-- In fact every fixed positive multiplicity has the same Ford scale as the
union density.  This is the two-sided form implicit in Ford's lower theorem
and the tautological inclusion of level sets. -/
theorem deltaR_isTheta_growth446_of_prefix_bounds
    {r : ℕ} {c cUnion CUnion : ℝ} {YUnion YR : ℕ}
    (hr : 1 ≤ r)
    (hc : 0 < c) (hcUnion : 0 < cUnion) (hCUnion : 0 < CUnion)
    (hYUnion : 1 ≤ YUnion) (hYR : 1 ≤ YR)
    (hUnion : DyadicPrefixBounds cUnion CUnion YUnion)
    (hR : FixedMultiplicityPrefixLower r c YR) :
    (fun n : ℕ ↦ deltaR r n) =Θ[atTop] growth446 := by
  have hcomp := eventually_deltaR_lower_of_prefix_bounds hc hcUnion hCUnion
    hYUnion hYR hUnion hR
  have hRdelta := deltaR_isTheta_delta_of_eventual_lower hr (half_pos hc) hcomp
  have hepsTheta := epsilon_isTheta_growth446_of_dyadicPrefixBounds
    hYUnion hcUnion hCUnion hUnion
  exact hRdelta.trans (delta_isTheta_growth446_of_epsilon hepsTheta)

end Erdos446
