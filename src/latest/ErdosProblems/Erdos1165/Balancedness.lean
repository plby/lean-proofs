/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/

import ErdosProblems.Erdos1165.ModerateDeviation
import ErdosProblems.Erdos1165.Screening

/-!
# The finite balancedness reduction in HLOZ Proposition 4.5

Hao--Li--Okada--Zheng prove their balancedness estimate by conditioning on
the external walk.  For a fixed external path, only finitely many sites can
have been visited.  Those sites are split into two classes:

* a near-maximal class, whose cardinality is controlled by Proposition 4.4;
* the remaining visited sites, whose cardinality is bounded by the clock.

At each fixed site, the insertion count has the negative-binomial law from
`NegativeBinomial`.  A moderate-deviation bound gives one cost for a site in
the first class and a stronger cost for a site in the second.  Finite
subadditivity, followed by averaging over the external path, is all that is
left.  Finally one adds the exceptional late-clock and overcrowding events.

This file formalizes precisely those finite and measure-theoretic steps.  It
does **not** postulate Proposition 4.5 for planar random walk.  The hypotheses
named `hLaw` below are one-site comparisons with the explicit
negative-binomial tails.  In the application they must be proved from the
conditional insertion law.  Likewise, the final reduction exposes, rather
than assumes under another name, the deterministic event cover and the
disintegration identity which connect the conditional model to the original
walk.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Erdos1165.Balancedness

open ModerateDeviation

/-! ## Finite conditional union bounds -/

section ConditionalUnion

variable {External Ω Site : Type*} [MeasurableSpace Ω]

/-- Failure at a site in either of two finite, external-data-dependent
classes.  The two bad-event families are allowed to differ because HLOZ use
different deviation scales in the near and far classes. -/
def conditionalFailure
    (near far : External → Finset Site)
    (nearBad farBad : External → Site → Set Ω) (z : External) : Set Ω :=
  Screening.someCandidateBad (near z) (nearBad z) ∪
    Screening.someCandidateBad (far z) (farBad z)

/-- For a fixed value of the external data, finite subadditivity converts
uniform one-site estimates into the two-scale conditional estimate.  No
independence is needed for this implication. -/
theorem measure_conditionalFailure_le
    (κ : External → Measure Ω)
    (near far : External → Finset Site)
    (nearBad farBad : External → Site → Set Ω)
    (nearBudget farBudget : ℕ) (nearCost farCost : ℝ≥0∞)
    (hnearCard : ∀ z, (near z).card ≤ nearBudget)
    (hfarCard : ∀ z, (far z).card ≤ farBudget)
    (hnear : ∀ z x, x ∈ near z → κ z (nearBad z x) ≤ nearCost)
    (hfar : ∀ z x, x ∈ far z → κ z (farBad z x) ≤ farCost)
    (z : External) :
    κ z (conditionalFailure near far nearBad farBad z) ≤
      (nearBudget : ℝ≥0∞) * nearCost + (farBudget : ℝ≥0∞) * farCost := by
  unfold conditionalFailure
  calc
    κ z (Screening.someCandidateBad (near z) (nearBad z) ∪
        Screening.someCandidateBad (far z) (farBad z)) ≤
        κ z (Screening.someCandidateBad (near z) (nearBad z)) +
          κ z (Screening.someCandidateBad (far z) (farBad z)) :=
      measure_union_le _ _
    _ ≤ (nearBudget : ℝ≥0∞) * nearCost +
        (farBudget : ℝ≥0∞) * farCost :=
      add_le_add
        (Screening.measure_someCandidateBad_le_budget
          (κ z) (near z) (nearBad z) nearBudget nearCost
          (hnearCard z) (hnear z))
        (Screening.measure_someCandidateBad_le_budget
          (κ z) (far z) (farBad z) farBudget farCost
          (hfarCard z) (hfar z))

/-- Averaging the preceding conditional estimate over a probability law for
the external data does not change its deterministic upper bound.  The
integrand is the conditional probability appearing after HLOZ condition on
the external path. -/
theorem lintegral_conditionalFailure_le
    [MeasurableSpace External]
    (ν : Measure External) [IsProbabilityMeasure ν]
    (κ : External → Measure Ω)
    (near far : External → Finset Site)
    (nearBad farBad : External → Site → Set Ω)
    (nearBudget farBudget : ℕ) (nearCost farCost : ℝ≥0∞)
    (hnearCard : ∀ z, (near z).card ≤ nearBudget)
    (hfarCard : ∀ z, (far z).card ≤ farBudget)
    (hnear : ∀ z x, x ∈ near z → κ z (nearBad z x) ≤ nearCost)
    (hfar : ∀ z x, x ∈ far z → κ z (farBad z x) ≤ farCost) :
    ∫⁻ z, κ z (conditionalFailure near far nearBad farBad z) ∂ν ≤
      (nearBudget : ℝ≥0∞) * nearCost + (farBudget : ℝ≥0∞) * farCost := by
  calc
    ∫⁻ z, κ z (conditionalFailure near far nearBad farBad z) ∂ν ≤
        ∫⁻ _z, ((nearBudget : ℝ≥0∞) * nearCost +
          (farBudget : ℝ≥0∞) * farCost) ∂ν := by
      apply lintegral_mono
      exact measure_conditionalFailure_le κ near far nearBad farBad
        nearBudget farBudget nearCost farCost hnearCard hfarCard hnear hfar
    _ = (nearBudget : ℝ≥0∞) * nearCost +
        (farBudget : ℝ≥0∞) * farCost := by simp

end ConditionalUnion

/-! ## The exponential arithmetic in (4.24) -/

section ExponentialBudget

/-- If the number of candidates grows like `exp(growth)` and every candidate
costs `exp(-rate)`, the union costs at most `exp(-target)` whenever the rate
beats the growth exponent by `target`.  This is the exact numerical step
behind HLOZ's products
`exp(16 m^(1-2κ₁)) * exp(-17 m^(1-2κ₁))`. -/
theorem budget_mul_exp_neg_le {budget : ℕ} {growth rate target : ℝ}
    (hbudget : (budget : ℝ) ≤ Real.exp growth)
    (hgap : target ≤ rate - growth) :
    (budget : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-rate)) ≤
      ENNReal.ofReal (Real.exp (-target)) := by
  rw [← ENNReal.ofReal_natCast budget,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg budget)]
  apply ENNReal.ofReal_le_ofReal
  calc
    (budget : ℝ) * Real.exp (-rate) ≤
        Real.exp growth * Real.exp (-rate) :=
      mul_le_mul_of_nonneg_right hbudget (Real.exp_nonneg _)
    _ = Real.exp (-(rate - growth)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-target) := Real.exp_le_exp.mpr (neg_le_neg hgap)

/-- The constants `16` and `17` used in the near-maximal class leave one full
copy of the scale in the exponent. -/
theorem budget_mul_exp_seventeen_le {budget : ℕ} {u : ℝ}
    (hbudget : (budget : ℝ) ≤ Real.exp (16 * u)) :
    (budget : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-17 * u)) ≤
      ENNReal.ofReal (Real.exp (-u)) := by
  simpa only [neg_mul] using
    (budget_mul_exp_neg_le (growth := 16 * u) (rate := 17 * u)
      (target := u) hbudget (by linarith))

end ExponentialBudget

/-! ## Combining the two imbalance directions -/

section TwoSided

variable {Ω Site : Type*} [MeasurableSpace Ω]

/-- A two-sided imbalance at a site is the union of its lower and upper
deviation events. -/
def twoSidedBad (lowerBad upperBad : Site → Set Ω) (x : Site) : Set Ω :=
  lowerBad x ∪ upperBad x

/-- Union bound first over the two deviation directions and then over the
finite site family.  This is the finite calculation used for
`Θ⁻ ∪ Θ⁺` in HLOZ. -/
theorem measure_someTwoSidedBad_le_budget
    (μ : Measure Ω) (sites : Finset Site)
    (lowerBad upperBad : Site → Set Ω)
    (budget : ℕ) (lowerCost upperCost : ℝ≥0∞)
    (hcard : sites.card ≤ budget)
    (hlower : ∀ x ∈ sites, μ (lowerBad x) ≤ lowerCost)
    (hupper : ∀ x ∈ sites, μ (upperBad x) ≤ upperCost) :
    μ (Screening.someCandidateBad sites (twoSidedBad lowerBad upperBad)) ≤
      (budget : ℝ≥0∞) * (lowerCost + upperCost) := by
  apply Screening.measure_someCandidateBad_le_budget
    μ sites (twoSidedBad lowerBad upperBad) budget
      (lowerCost + upperCost) hcard
  intro x hx
  exact (measure_union_le (μ := μ) (lowerBad x) (upperBad x)).trans
    (add_le_add (hlower x hx) (hupper x hx))

end TwoSided

/-! ## One-site negative-binomial inputs -/

section OneSite

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The explicit upper-tail moderate-deviation theorem converts a comparison
with the HLOZ negative-binomial tail into a one-site event estimate. -/
theorem measure_upperImbalance_le_exp
    (μ : Measure Ω) (bad : Set Ω) {i k : ℕ} (hi : 0 < i)
    (habove : i < 15 * k) (hbelow : 15 * k ≤ 2 * i)
    (hLaw : μ bad ≤ ENNReal.ofReal (upperTailMass i k)) :
    μ bad ≤ ENNReal.ofReal
      (Real.exp (-((i : ℝ) * relativeExcess i k ^ 2 / 60))) := by
  exact hLaw.trans (ENNReal.ofReal_le_ofReal
    (upperTailMass_le_exp_neg_quadratic hi habove hbelow))

/-- A uniform lower bound on the quadratic rate gives a common one-site cost,
which is the form needed before taking a union over candidate sites. -/
theorem measure_upperImbalance_le_uniform
    (μ : Measure Ω) (bad : Set Ω) {i k : ℕ} (hi : 0 < i)
    (habove : i < 15 * k) (hbelow : 15 * k ≤ 2 * i)
    {rate : ℝ}
    (hrate : rate ≤ (i : ℝ) * relativeExcess i k ^ 2 / 60)
    (hLaw : μ bad ≤ ENNReal.ofReal (upperTailMass i k)) :
    μ bad ≤ ENNReal.ofReal (Real.exp (-rate)) := by
  refine (measure_upperImbalance_le_exp μ bad hi habove hbelow hLaw).trans ?_
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hrate))

/-- Lower imbalance uses the lower negative-binomial tail.  `ModerateDeviation`
already supplies Chernoff's inequality for every nonpositive parameter; the
remaining hypothesis here is only the explicit real-arithmetic comparison of
that Chernoff expression with the desired common exponential cost. -/
theorem measure_lowerImbalance_le_uniform
    (μ : Measure Ω) (bad : Set Ω) {i k : ℕ} (hi : 0 < i)
    {t rate : ℝ} (ht0 : t ≤ 0) (ht16 : Real.exp t < 16)
    (hchernoff :
      Real.exp (-t * k) * ((15 : ℝ) / (16 - Real.exp t)) ^ i ≤
        Real.exp (-rate))
    (hLaw : μ bad ≤ ENNReal.ofReal (lowerTailMass i k)) :
    μ bad ≤ ENNReal.ofReal (Real.exp (-rate)) := by
  refine hLaw.trans ?_
  exact (ENNReal.ofReal_le_ofReal (lowerTailMass_le_chernoff hi ht0 ht16)).trans
    (ENNReal.ofReal_le_ofReal hchernoff)

/-- Optimizing the lower-tail Chernoff parameter leaves only a comparison
between the exact Cramér rate and the common rate required by the candidate
union. -/
theorem measure_lowerImbalance_le_uniformRate
    (μ : Measure Ω) (bad : Set Ω) {i k : ℕ} (hi : 0 < i)
    (hk0 : 0 < k) (hbelowMean : 15 * k < i) {rate : ℝ}
    (hrate : rate ≤ upperRate i k)
    (hLaw : μ bad ≤ ENNReal.ofReal (lowerTailMass i k)) :
    μ bad ≤ ENNReal.ofReal (Real.exp (-rate)) := by
  refine hLaw.trans ?_
  exact (ENNReal.ofReal_le_ofReal
    (lowerTailMass_le_exp_neg_upperRate hi hk0 hbelowMean)).trans
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg hrate)))

end OneSite

/-! ## Finite candidate families with explicit deviation laws -/

section DeviationUnion

variable {Ω Site : Type*} [MeasurableSpace Ω]

/-- Finite union of upper imbalance events.  The sole probabilistic input at
each site is the comparison `hLaw` with the explicit negative-binomial tail;
all other assumptions are arithmetic facts about the tail parameters. -/
theorem measure_someUpperImbalance_le
    (μ : Measure Ω) (sites : Finset Site) (bad : Site → Set Ω)
    (budget : ℕ) (rate : ℝ)
    (i k : Site → ℕ)
    (hcard : sites.card ≤ budget)
    (hi : ∀ x ∈ sites, 0 < i x)
    (habove : ∀ x ∈ sites, i x < 15 * k x)
    (hbelow : ∀ x ∈ sites, 15 * k x ≤ 2 * i x)
    (hrate : ∀ x ∈ sites,
      rate ≤ (i x : ℝ) * relativeExcess (i x) (k x) ^ 2 / 60)
    (hLaw : ∀ x ∈ sites,
      μ (bad x) ≤ ENNReal.ofReal (upperTailMass (i x) (k x))) :
    μ (Screening.someCandidateBad sites bad) ≤
      (budget : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-rate)) := by
  apply Screening.measure_someCandidateBad_le_budget
    μ sites bad budget (ENNReal.ofReal (Real.exp (-rate))) hcard
  intro x hx
  exact measure_upperImbalance_le_uniform μ (bad x)
    (hi x hx) (habove x hx) (hbelow x hx) (hrate x hx) (hLaw x hx)

/-- Finite union of lower imbalance events.  The optimized lower-tail theorem
from `ModerateDeviation` reduces the analytic input to a uniform lower bound
on the exact Cramér rate. -/
theorem measure_someLowerImbalance_le
    (μ : Measure Ω) (sites : Finset Site) (bad : Site → Set Ω)
    (budget : ℕ) (rate : ℝ)
    (i k : Site → ℕ)
    (hcard : sites.card ≤ budget)
    (hi : ∀ x ∈ sites, 0 < i x)
    (hk0 : ∀ x ∈ sites, 0 < k x)
    (hbelowMean : ∀ x ∈ sites, 15 * k x < i x)
    (hrate : ∀ x ∈ sites, rate ≤ upperRate (i x) (k x))
    (hLaw : ∀ x ∈ sites,
      μ (bad x) ≤ ENNReal.ofReal (lowerTailMass (i x) (k x))) :
    μ (Screening.someCandidateBad sites bad) ≤
      (budget : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-rate)) := by
  apply Screening.measure_someCandidateBad_le_budget
    μ sites bad budget (ENNReal.ofReal (Real.exp (-rate))) hcard
  intro x hx
  exact measure_lowerImbalance_le_uniformRate μ (bad x)
    (hi x hx) (hk0 x hx) (hbelowMean x hx) (hrate x hx) (hLaw x hx)

end DeviationUnion

/-! ## The exceptional-event reduction -/

section Reduction

variable {External Ω Site : Type*} [MeasurableSpace External] [MeasurableSpace Ω]

/-- Abstract form of the last calculation in the proof of HLOZ Proposition
4.5.  The statement deliberately keeps every random-walk-specific bridge as
a visible hypothesis:

* `hcover` is the deterministic reduction after cutting off the clock;
* `hlate` and `hovercrowded` are the two earlier exceptional estimates;
* `hdisintegrate` identifies the residual probability with the average of
  the conditional insertion laws;
* `hnear` and `hfar` are the separately named one-site estimates.

The conclusion is derived solely by two finite union bounds and the tower
(disintegration) identity. -/
theorem measure_balancednessFailure_le
    (μ : Measure Ω)
    (ν : Measure External) [IsProbabilityMeasure ν]
    (κ : External → Measure Ω)
    (target late overcrowded residual : Set Ω)
    (near far : External → Finset Site)
    (nearBad farBad : External → Site → Set Ω)
    (lateCost overcrowdedCost nearCost farCost : ℝ≥0∞)
    (nearBudget farBudget : ℕ)
    (hcover : target ⊆ late ∪ overcrowded ∪ residual)
    (hlate : μ late ≤ lateCost)
    (hovercrowded : μ overcrowded ≤ overcrowdedCost)
    (hdisintegrate :
      μ residual =
        ∫⁻ z, κ z (conditionalFailure near far nearBad farBad z) ∂ν)
    (hnearCard : ∀ z, (near z).card ≤ nearBudget)
    (hfarCard : ∀ z, (far z).card ≤ farBudget)
    (hnear : ∀ z x, x ∈ near z → κ z (nearBad z x) ≤ nearCost)
    (hfar : ∀ z x, x ∈ far z → κ z (farBad z x) ≤ farCost) :
    μ target ≤ lateCost + overcrowdedCost +
      (nearBudget : ℝ≥0∞) * nearCost + (farBudget : ℝ≥0∞) * farCost := by
  have hresidual :
      μ residual ≤ (nearBudget : ℝ≥0∞) * nearCost +
        (farBudget : ℝ≥0∞) * farCost := by
    rw [hdisintegrate]
    exact lintegral_conditionalFailure_le ν κ near far nearBad farBad
      nearBudget farBudget nearCost farCost hnearCard hfarCard hnear hfar
  calc
    μ target ≤ μ (late ∪ overcrowded ∪ residual) := measure_mono hcover
    _ ≤ μ late + μ overcrowded + μ residual := by
      calc
        μ (late ∪ overcrowded ∪ residual) ≤ μ late + μ (overcrowded ∪ residual) :=
          by simpa only [union_assoc] using
            (measure_union_le (μ := μ) late (overcrowded ∪ residual))
        _ ≤ μ late + (μ overcrowded + μ residual) :=
          add_le_add_right (measure_union_le overcrowded residual) (μ late)
        _ = μ late + μ overcrowded + μ residual := by rw [add_assoc]
    _ ≤ lateCost + overcrowdedCost +
        ((nearBudget : ℝ≥0∞) * nearCost +
          (farBudget : ℝ≥0∞) * farCost) :=
      add_le_add (add_le_add hlate hovercrowded) hresidual
    _ = lateCost + overcrowdedCost +
        (nearBudget : ℝ≥0∞) * nearCost +
          (farBudget : ℝ≥0∞) * farCost := by ac_rfl

end Reduction

end Erdos1165.Balancedness
