import ErdosProblems.Erdos520.HarperPrefixGoodEvent
import ErdosProblems.Erdos520.HarperRestrictedVerticalSet
import ErdosProblems.Erdos520.HarperFractionalRecursion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# Prefix good events on the ambient sign space

The simultaneous prefix-energy window is naturally a finite-prime-cube
event.  The actual fractional moment, however, is integrated on the ambient
infinite sign space `Omega`.  This file pulls the good event back along the
prime-restriction map, proves exact fair-probability transport, and packages
the restricted first moment with Harper's `q < r` good--bad recursion.

All analytic energy-window and inverse-moment majorants remain visible as
hypotheses.  Likewise, the deterministic containment of the good event in a
vertical tilted barrier event is supplied by the caller.
-/

/-! ## Exact fair-cube transport -/

/-- The ambient event that all finite prefix Euler-energy windows hold. -/
def harperOmegaPrefixEnergyWindowGoodEvent
    (y start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ) : Set Omega :=
  harperPrimeRestriction y ⁻¹'
    harperPrefixEnergyWindowGoodSet y start n M lower upper

theorem measurableSet_harperOmegaPrefixEnergyWindowGoodEvent
    (y start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ) :
    MeasurableSet
      (harperOmegaPrefixEnergyWindowGoodEvent
        y start n M lower upper) := by
  exact (measurableSet_harperPrefixEnergyWindowGoodSet
    y start n M lower upper).preimage
      (measurable_harperPrimeRestriction y)

/-- Fair probability of the ambient event is exactly the finite fair-cube
probability, with no approximation or independence hypothesis. -/
theorem mu_real_harperOmegaPrefixEnergyWindowGoodEvent_eq_fairCube
    (y start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ) :
    μ.real
        (harperOmegaPrefixEnergyWindowGoodEvent
          y start n M lower upper) =
      (harperFairCubeLaw y).real
        (harperPrefixEnergyWindowGoodSet
          y start n M lower upper) := by
  have hmap := map_measureReal_apply
    (μ := μ) (measurable_harperPrimeRestriction y)
    (measurableSet_harperPrefixEnergyWindowGoodSet
      y start n M lower upper)
  rw [map_harperPrimeRestriction_mu] at hmap
  simpa only [harperOmegaPrefixEnergyWindowGoodEvent,
    harperFairCubeLaw] using! hmap.symm

/-- The same exact transport for the bad-event complement. -/
theorem mu_real_compl_harperOmegaPrefixEnergyWindowGoodEvent_eq_fairCube
    (y start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ) :
    μ.real
        (harperOmegaPrefixEnergyWindowGoodEvent
          y start n M lower upper)ᶜ =
      (harperFairCubeLaw y).real
        (harperPrefixEnergyWindowGoodSet
          y start n M lower upper)ᶜ := by
  have hmap := map_measureReal_apply
    (μ := μ) (measurable_harperPrimeRestriction y)
    (measurableSet_harperPrefixEnergyWindowGoodSet
      y start n M lower upper).compl
  rw [map_harperPrimeRestriction_mu] at hmap
  simpa only [harperOmegaPrefixEnergyWindowGoodEvent,
    harperFairCubeLaw, preimage_compl] using! hmap.symm

/-- The supplied first-moment prefix budget transfers verbatim to `Omega`. -/
theorem mu_real_compl_harperOmegaPrefixEnergyWindowGoodEvent_le_firstMomentBudget
    (y start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (upperFirstMoment : ℕ → ℝ)
    (inverseFirstMoment : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (hlower : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        0 < lower m u)
    (hupper : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        0 < upper m u)
    (hupperMoment : ∀ m, m ∈ Finset.Icc 1 n →
      harperPrefixEulerNormalizer y start m ≤ upperFirstMoment m)
    (hinverseMoment : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        harperPrefixEulerReciprocalFirstMoment y start m u ≤
          inverseFirstMoment m u) :
    μ.real
        (harperOmegaPrefixEnergyWindowGoodEvent
          y start n M lower upper)ᶜ ≤
      harperPrefixEnergyWindowFirstMomentBudget start n M lower upper
        upperFirstMoment inverseFirstMoment := by
  rw [mu_real_compl_harperOmegaPrefixEnergyWindowGoodEvent_eq_fairCube]
  exact
    harperFairCubeLaw_real_compl_prefixEnergyWindowGoodSet_le_firstMomentBudget
      y start n M lower upper upperFirstMoment inverseFirstMoment
        hlower hupper hupperMoment hinverseMoment

/-! ## Fractional-power helpers -/

/-- Jensen for a restricted event at any exponent in `(0,1]`.  The
indicator is taken on the ambient probability space, so no extra measure
factor appears. -/
theorem integralOn_rpow_le_rpow_integralOn_of_le_one
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {Z : α → ℝ} {G : Set α} {q : ℝ}
    (hG : MeasurableSet G) (hq : 0 < q) (hq1 : q ≤ 1)
    (hZ : Integrable Z ν) (hZnonneg : ∀ omega, 0 ≤ Z omega) :
    (∫ omega in G, Z omega ^ q ∂ν) ≤
      (∫ omega in G, Z omega ∂ν) ^ q := by
  let W : α → ℝ := G.indicator Z
  let g : ℝ → ℝ := fun x ↦ x ^ q
  have hW : Integrable W ν := hZ.indicator hG
  have hWnonneg : ∀ omega, 0 ≤ W omega := by
    intro omega
    by_cases homega : omega ∈ G
    · simp [W, homega, hZnonneg omega]
    · simp [W, homega]
  have hWq : Integrable (g ∘ W) ν := by
    simpa only [g, Function.comp_apply] using!
      integrable_rpow_of_integrable_nonneg hW hWnonneg hq.le hq1
  have hJ :=
    (Real.concaveOn_rpow hq.le hq1).le_map_integral
      (Real.continuous_rpow_const hq.le).continuousOn
      isClosed_Ici (ae_of_all ν hWnonneg) hW hWq
  have hpowIndicator : (fun omega ↦ W omega ^ q) =
      G.indicator (fun omega ↦ Z omega ^ q) := by
    funext omega
    by_cases homega : omega ∈ G
    · simp [W, homega]
    · simp [W, homega, hq.ne']
  rw [hpowIndicator, integral_indicator hG] at hJ
  simpa only [g, Function.comp_apply, W, integral_indicator hG] using! hJ

/-- If the `r`-th fractional moment is integrable, the `q`-th power has
the exact `L^(r/q)` membership required by Holder. -/
theorem memLp_rpow_of_integrable_rpow
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {Z : α → ℝ} {q r : ℝ}
    (hq : 0 < q) (hr : 0 < r)
    (hZ : Integrable Z ν) (hZnonneg : ∀ omega, 0 ≤ Z omega)
    (hZr : Integrable (fun omega ↦ Z omega ^ r) ν) :
    MemLp (fun omega ↦ Z omega ^ q)
      (ENNReal.ofReal (r / q)) ν := by
  have hmemZ : MemLp Z (ENNReal.ofReal r) ν := by
    apply (integrable_norm_rpow_iff hZ.aestronglyMeasurable
      (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hr.le]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hZnonneg _)] using! hZr
  have hpow := hmemZ.norm_rpow_div (ENNReal.ofReal q)
  have hfun :
      (fun omega ↦ ‖Z omega‖ ^ (ENNReal.ofReal q).toReal) =
        fun omega ↦ Z omega ^ q := by
    funext omega
    rw [ENNReal.toReal_ofReal hq.le, Real.norm_eq_abs,
      abs_of_nonneg (hZnonneg omega)]
  rw [hfun] at hpow
  rw [ENNReal.ofReal_div_of_pos hq]
  exact hpow

/-! ## Full good--bad assembly -/

/-- One exact Harper recursion step for an Euler energy over an arbitrary
finite vertical set.  The good-event first moment comes from the tilted
barrier probability, while the bad-event probability is the explicit
finite prefix-window budget.

The only bridge left to the caller is `hcontain`: on the simultaneous
prefix-energy good event, the relevant tilted event `A t` must occur. -/
theorem integral_harperEulerSetEnergy_rpow_le_of_prefixGoodEvent
    {y : ℕ} (hy : 2 ≤ y)
    {I : Set ℝ} (hI : MeasurableSet I) (hIfinite : volume I ≠ ∞)
    (start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (upperFirstMoment : ℕ → ℝ)
    (inverseFirstMoment : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (hlower : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        0 < lower m u)
    (hupper : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        0 < upper m u)
    (hupperMoment : ∀ m, m ∈ Finset.Icc 1 n →
      harperPrefixEulerNormalizer y start m ≤ upperFirstMoment m)
    (hinverseMoment : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        harperPrefixEulerReciprocalFirstMoment y start m u ≤
          inverseFirstMoment m u)
    (A : ℝ → Set (HarperPrimeCube y)) (H : ℝ) (hH : 0 ≤ H)
    (hcontain : ∀ t ∈ I,
      harperOmegaPrefixEnergyWindowGoodEvent y start n M lower upper ⊆
        harperPrimeRestriction y ⁻¹' A t)
    (hprob : ∀ t ∈ I,
      (harperTiltedCubeLaw y t).real (A t) ≤ H)
    {q r : ℝ} (hq : 0 < q) (hqr : q < r) (hr1 : r ≤ 1) :
    (∫ omega,
        harperEulerSetEnergy y I omega ^ q ∂μ) ≤
      (harperExplicitMertensConstant * (volume.real I * H)) ^ q +
        (harperPrefixEnergyWindowFirstMomentBudget
            start n M lower upper upperFirstMoment inverseFirstMoment) ^
            (1 - q / r) *
          (∫ omega, harperEulerSetEnergy y I omega ^ r ∂μ) ^
            (q / r) := by
  let G : Set Omega :=
    harperOmegaPrefixEnergyWindowGoodEvent y start n M lower upper
  let Z : Omega → ℝ := harperEulerSetEnergy y I
  let epsilon : ℝ :=
    harperPrefixEnergyWindowFirstMomentBudget
      start n M lower upper upperFirstMoment inverseFirstMoment
  have hy1 : 1 < y := by omega
  have hr : 0 < r := hq.trans hqr
  have hq1 : q ≤ 1 := hqr.le.trans hr1
  have hZ : Integrable Z μ := by
    exact integrable_harperEulerSetEnergy y hI hIfinite
  have hZnonneg : ∀ omega, 0 ≤ Z omega := by
    exact fun omega ↦ harperEulerSetEnergy_nonneg hy1 hI omega
  have hZq : Integrable (fun omega ↦ Z omega ^ q) μ :=
    integrable_rpow_of_integrable_nonneg hZ hZnonneg hq.le hq1
  have hZr : Integrable (fun omega ↦ Z omega ^ r) μ :=
    integrable_rpow_of_integrable_nonneg hZ hZnonneg hr.le hr1
  have hZqLp : MemLp (fun omega ↦ Z omega ^ q)
      (ENNReal.ofReal (r / q)) μ :=
    memLp_rpow_of_integrable_rpow hq hr hZ hZnonneg hZr
  have hG : MeasurableSet G := by
    exact measurableSet_harperOmegaPrefixEnergyWindowGoodEvent
      y start n M lower upper
  have hfirst :
      (∫ omega in G, Z omega ∂μ) ≤
        harperExplicitMertensConstant * (volume.real I * H) := by
    exact integral_harperEulerSetEnergy_restrict_le_explicitMertens
      hy hI hIfinite hG A H hH hcontain hprob
  have hgood :
      (∫ omega in G, Z omega ^ q ∂μ) ≤
        (harperExplicitMertensConstant * (volume.real I * H)) ^ q := by
    refine (integralOn_rpow_le_rpow_integralOn_of_le_one
      hG hq hq1 hZ hZnonneg).trans ?_
    exact Real.rpow_le_rpow
      (integral_nonneg hZnonneg) hfirst hq.le
  have hbad : μ.real Gᶜ ≤ epsilon := by
    exact
      mu_real_compl_harperOmegaPrefixEnergyWindowGoodEvent_le_firstMomentBudget
        y start n M lower upper upperFirstMoment inverseFirstMoment
          hlower hupper hupperMoment hinverseMoment
  have hrec := integral_rpow_le_of_good_bad_at_larger_exponent
    hG hq hqr hZnonneg hZq hZqLp hgood hbad
  simpa only [G, Z, epsilon] using! hrec

/-- Linearized version of the same assembly, ready for the finite
half-contraction iteration through Harper's dyadic exponents. -/
theorem integral_harperEulerSetEnergy_rpow_le_of_prefixGoodEvent_linearized
    {y : ℕ} (hy : 2 ≤ y)
    {I : Set ℝ} (hI : MeasurableSet I) (hIfinite : volume I ≠ ∞)
    (start n M : ℕ)
    (lower upper : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (upperFirstMoment : ℕ → ℝ)
    (inverseFirstMoment : (m : ℕ) → (Fin m → ℝ) → ℝ)
    (hlower : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        0 < lower m u)
    (hupper : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        0 < upper m u)
    (hupperMoment : ∀ m, m ∈ Finset.Icc 1 n →
      harperPrefixEulerNormalizer y start m ≤ upperFirstMoment m)
    (hinverseMoment : ∀ m, m ∈ Finset.Icc 1 n →
      ∀ u, u ∈ harperScheduledVerticalPrefixFamily start n m M →
        harperPrefixEulerReciprocalFirstMoment y start m u ≤
          inverseFirstMoment m u)
    (A : ℝ → Set (HarperPrimeCube y)) (H : ℝ) (hH : 0 ≤ H)
    (hcontain : ∀ t ∈ I,
      harperOmegaPrefixEnergyWindowGoodEvent y start n M lower upper ⊆
        harperPrimeRestriction y ⁻¹' A t)
    (hprob : ∀ t ∈ I,
      (harperTiltedCubeLaw y t).real (A t) ≤ H)
    {q r : ℝ} (hq : 0 < q) (hqr : q < r) (hr1 : r ≤ 1) :
    (∫ omega,
        harperEulerSetEnergy y I omega ^ q ∂μ) ≤
      (harperExplicitMertensConstant * (volume.real I * H)) ^ q +
        (harperPrefixEnergyWindowFirstMomentBudget
            start n M lower upper upperFirstMoment inverseFirstMoment) ^
            (1 - q / r) *
          (1 + ∫ omega,
            harperEulerSetEnergy y I omega ^ r ∂μ) := by
  have hbase :=
    integral_harperEulerSetEnergy_rpow_le_of_prefixGoodEvent
      hy hI hIfinite start n M lower upper upperFirstMoment
        inverseFirstMoment hlower hupper hupperMoment hinverseMoment
        A H hH hcontain hprob hq hqr hr1
  have hr : 0 < r := hq.trans hqr
  have hratio0 : 0 ≤ q / r := div_nonneg hq.le hr.le
  have hratio1 : q / r ≤ 1 := (div_le_one hr).mpr hqr.le
  have hmoment0 :
      0 ≤ ∫ omega, harperEulerSetEnergy y I omega ^ r ∂μ :=
    integral_nonneg fun omega ↦ Real.rpow_nonneg
      (harperEulerSetEnergy_nonneg (by omega) hI omega) r
  have hpower := rpow_le_one_add_self hmoment0 hratio0 hratio1
  have hbad :=
    mu_real_compl_harperOmegaPrefixEnergyWindowGoodEvent_le_firstMomentBudget
      y start n M lower upper upperFirstMoment inverseFirstMoment
        hlower hupper hupperMoment hinverseMoment
  have hepsilon : 0 ≤
      harperPrefixEnergyWindowFirstMomentBudget
        start n M lower upper upperFirstMoment inverseFirstMoment :=
    measureReal_nonneg.trans hbad
  exact hbase.trans (add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_left hpower
      (Real.rpow_nonneg hepsilon _)))

end Problem520
end Erdos
