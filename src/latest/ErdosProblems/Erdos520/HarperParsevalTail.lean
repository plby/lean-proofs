import ErdosProblems.Erdos520.HarperParsevalAssembly
import ErdosProblems.Erdos520.MertensProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos
namespace Problem520

/-!
# The explicit Parseval tail

This file discharges the tail term in `HarperParsevalAssembly`.  The main
input is only the exact first moment of the finite Euler density.  Fubini,
the elementary `t⁻²` tail bound, the explicit Mertens estimate, and Jensen's
inequality then give a completely explicit `2/3`-moment bound.
-/

/-- A deterministic pointwise upper bound for the finite Euler density. -/
noncomputable def harperEulerDensityUniformBound (y : ℕ) : ℝ :=
  ∏ p ∈ (y + 1).primesBelow,
    (1 + (p : ℝ)⁻¹ + 2 / Real.sqrt (p : ℝ))

theorem measurable_harperEulerFactor_joint (p : ℕ) :
    Measurable (fun w : ℝ × Omega ↦ harperEulerFactor w.2 p w.1) := by
  unfold harperEulerFactor
  have heps : Measurable (fun w : ℝ × Omega ↦ ε w.2 p) :=
    (measurable_ε p).comp measurable_snd
  exact ((measurable_const.add
      ((heps.mul (Real.measurable_cos.comp
        (measurable_fst.mul measurable_const))).div measurable_const)).pow_const 2).add
    (((heps.mul (Real.measurable_sin.comp
      (measurable_fst.mul measurable_const))).div measurable_const).pow_const 2)

theorem measurable_harperEulerDensity_joint (y : ℕ) :
    Measurable (fun w : ℝ × Omega ↦ harperEulerDensity y w.2 w.1) := by
  unfold harperEulerDensity
  exact Finset.measurable_fun_prod _ fun p _ ↦
    measurable_harperEulerFactor_joint p

theorem harperEulerFactor_le_uniformFactor
    (omega : Omega) {p : ℕ} (hp : 0 < p) (t : ℝ) :
    harperEulerFactor omega p t ≤
      1 + (p : ℝ)⁻¹ + 2 / Real.sqrt (p : ℝ) := by
  rw [harperEulerFactor_eq omega hp]
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hsqrt : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hpR
  have hprod :
      ε omega p * Real.cos (t * Real.log (p : ℝ)) ≤ 1 := by
    calc
      ε omega p * Real.cos (t * Real.log (p : ℝ)) ≤
          |ε omega p * Real.cos (t * Real.log (p : ℝ))| :=
        le_abs_self _
      _ = |Real.cos (t * Real.log (p : ℝ))| := by
        rw [abs_mul, abs_ε, one_mul]
      _ ≤ 1 := Real.abs_cos_le_one _
  have hdiv :
      2 * ε omega p * Real.cos (t * Real.log (p : ℝ)) /
          Real.sqrt (p : ℝ) ≤
        2 / Real.sqrt (p : ℝ) :=
    (div_le_div_iff_of_pos_right hsqrt).2 (by nlinarith)
  linarith

theorem harperEulerDensity_le_uniformBound
    (y : ℕ) (omega : Omega) (t : ℝ) :
    harperEulerDensity y omega t ≤ harperEulerDensityUniformBound y := by
  classical
  unfold harperEulerDensity harperEulerDensityUniformBound
  apply Finset.prod_le_prod
  · intro p hp
    exact harperEulerFactor_nonneg omega p t
  · intro p hp
    exact harperEulerFactor_le_uniformFactor omega
      (Nat.Prime.pos (Nat.prime_of_mem_primesBelow hp)) t

theorem harperEulerDensityUniformBound_nonneg (y : ℕ) :
    0 ≤ harperEulerDensityUniformBound y := by
  classical
  unfold harperEulerDensityUniformBound
  apply Finset.prod_nonneg
  intro p hp
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  positivity

/-- The scalar Cauchy kernel is globally integrable. -/
theorem integrable_one_div_harperCauchyKernel :
    Integrable (fun t : ℝ ↦ 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) := by
  have heq :
      (fun t : ℝ ↦ 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) =
        fun t : ℝ ↦ 1 / ((1 / 4 : ℝ) + t ^ 2) := by
    funext t
    norm_num
  rw [heq]
  have h := integrable_harperEulerDensity_div_cauchyKernel 0 (fun _ ↦ false)
  have hempty : (0 + 1).primesBelow = ∅ := by
    ext p
    constructor
    · intro hp
      have hp2 := (Nat.prime_of_mem_primesBelow hp).two_le
      have hplt := Nat.lt_of_mem_primesBelow hp
      omega
    · intro hp
      simp at hp
  simpa [harperEulerDensity, hempty] using! h

/-- The unnormalized Cauchy-weighted Euler mass outside `[-M,M]`. -/
noncomputable def harperEulerTailMass
    (y M : ℕ) (omega : Omega) : ℝ :=
  ∫ t in harperEulerTailSet M,
    harperEulerDensity y omega t / ((1 / 2 : ℝ) ^ 2 + t ^ 2)

theorem harperEulerTailRemainder_eq_tailMass_div
    (y M : ℕ) (omega : Omega) :
    harperEulerTailRemainder y M omega =
      harperEulerTailMass y M omega / Real.log (y : ℝ) := by
  rfl

theorem measurable_harperEulerDensity_div_cauchyKernel_joint (y : ℕ) :
    Measurable (fun w : ℝ × Omega ↦
      harperEulerDensity y w.2 w.1 /
        ((1 / 2 : ℝ) ^ 2 + w.1 ^ 2)) := by
  exact (measurable_harperEulerDensity_joint y).div
    (measurable_const.add (measurable_fst.pow_const 2))

/-- Joint integrability on the two tails.  The finite deterministic bound is
used only to justify Fubini; it does not enter the final estimate. -/
theorem integrable_harperEulerDensity_div_cauchyKernel_prod_tail
    (y M : ℕ) :
    Integrable
      (fun w : ℝ × Omega ↦
        harperEulerDensity y w.2 w.1 /
          ((1 / 2 : ℝ) ^ 2 + w.1 ^ 2))
      ((volume.restrict (harperEulerTailSet M)).prod μ) := by
  let ν : Measure ℝ := volume.restrict (harperEulerTailSet M)
  let k : ℝ → ℝ := fun t ↦ 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)
  let B : ℝ := harperEulerDensityUniformBound y
  let F : ℝ × Omega → ℝ := fun w ↦
    harperEulerDensity y w.2 w.1 /
      ((1 / 2 : ℝ) ^ 2 + w.1 ^ 2)
  have hk : Integrable k ν := by
    simpa only [ν, k] using!
      integrable_one_div_harperCauchyKernel.integrableOn
  have hmajor : Integrable
      (fun w : ℝ × Omega ↦ (B * k w.1) * (1 : ℝ)) (ν.prod μ) :=
    (hk.const_mul B).mul_prod (integrable_const (1 : ℝ))
  apply hmajor.mono'
    (measurable_harperEulerDensity_div_cauchyKernel_joint y).aestronglyMeasurable
  exact ae_of_all _ fun w ↦ by
    have hden : 0 < (1 / 2 : ℝ) ^ 2 + w.1 ^ 2 := by positivity
    have hquot :
        harperEulerDensity y w.2 w.1 /
              ((1 / 2 : ℝ) ^ 2 + w.1 ^ 2) ≤
            harperEulerDensityUniformBound y /
              ((1 / 2 : ℝ) ^ 2 + w.1 ^ 2) :=
      (div_le_div_iff_of_pos_right hden).2
        (harperEulerDensity_le_uniformBound y w.2 w.1)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (harperEulerDensity_nonneg y w.2 w.1) hden.le)]
    simpa only [F, B, k, mul_one, one_mul, div_eq_mul_inv] using! hquot

theorem integrable_harperEulerTailMass (y M : ℕ) :
    Integrable (harperEulerTailMass y M) μ := by
  let ν : Measure ℝ := volume.restrict (harperEulerTailSet M)
  let F : ℝ × Omega → ℝ := fun w ↦
    harperEulerDensity y w.2 w.1 /
      ((1 / 2 : ℝ) ^ 2 + w.1 ^ 2)
  have hF : Integrable F (ν.prod μ) := by
    simpa only [ν, F] using!
      integrable_harperEulerDensity_div_cauchyKernel_prod_tail y M
  simpa only [harperEulerTailMass, ν, F] using! hF.integral_prod_right

theorem harperEulerTailMass_nonneg
    (y M : ℕ) (omega : Omega) :
    0 ≤ harperEulerTailMass y M omega := by
  unfold harperEulerTailMass
  exact setIntegral_nonneg (measurableSet_harperEulerTailSet M)
    fun t ht ↦ div_nonneg (harperEulerDensity_nonneg y omega t) (by positivity)

/-- Fubini turns the mean tail mass into the deterministic Cauchy-kernel
tail times the exact Euler normalizer. -/
theorem integral_harperEulerTailMass (y M : ℕ) :
    (∫ omega, harperEulerTailMass y M omega ∂μ) =
      primeEnergyNormalizer y *
        ∫ t in harperEulerTailSet M,
          1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2) := by
  let ν : Measure ℝ := volume.restrict (harperEulerTailSet M)
  let F : ℝ × Omega → ℝ := fun w ↦
    harperEulerDensity y w.2 w.1 /
      ((1 / 2 : ℝ) ^ 2 + w.1 ^ 2)
  have hF : Integrable F (ν.prod μ) := by
    simpa only [ν, F] using!
      integrable_harperEulerDensity_div_cauchyKernel_prod_tail y M
  calc
    (∫ omega, harperEulerTailMass y M omega ∂μ) =
        ∫ omega, ∫ t, F (t, omega) ∂ν ∂μ := by
      rfl
    _ = ∫ w, F w ∂ν.prod μ :=
      (integral_prod_symm F hF).symm
    _ = ∫ t, ∫ omega, F (t, omega) ∂μ ∂ν :=
      integral_prod F hF
    _ = ∫ t,
        primeEnergyNormalizer y /
          ((1 / 2 : ℝ) ^ 2 + t ^ 2) ∂ν := by
      apply integral_congr_ae
      exact ae_of_all ν fun t ↦ by
        simp only [F]
        rw [integral_div, integral_harperEulerDensity]
    _ = primeEnergyNormalizer y *
        ∫ t in harperEulerTailSet M,
          1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2) := by
      change (∫ t,
          primeEnergyNormalizer y /
            ((1 / 2 : ℝ) ^ 2 + t ^ 2) ∂ν) =
        primeEnergyNormalizer y *
          ∫ t, 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2) ∂ν
      simp_rw [div_eq_mul_inv]
      rw [integral_const_mul]
      congr 2
      funext t
      ring

theorem integrable_harperEulerTailRemainder (y M : ℕ) :
    Integrable (harperEulerTailRemainder y M) μ := by
  rw [show harperEulerTailRemainder y M =
      fun omega ↦ harperEulerTailMass y M omega / Real.log (y : ℝ) by
    funext omega
    exact harperEulerTailRemainder_eq_tailMass_div y M omega]
  exact (integrable_harperEulerTailMass y M).div_const _

theorem integral_harperEulerTailRemainder (y M : ℕ) :
    (∫ omega, harperEulerTailRemainder y M omega ∂μ) =
      (primeEnergyNormalizer y *
        (∫ t in harperEulerTailSet M,
          1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2))) /
        Real.log (y : ℝ) := by
  rw [show harperEulerTailRemainder y M =
      fun omega ↦ harperEulerTailMass y M omega / Real.log (y : ℝ) by
    funext omega
    exact harperEulerTailRemainder_eq_tailMass_div y M omega,
    integral_div, integral_harperEulerTailMass]

/-- One positive half of the elementary Cauchy-kernel tail. -/
theorem integral_Ici_one_div_harperCauchyKernel_le
    {m : ℝ} (hm : 0 < m) :
    (∫ t in Ici m, 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) ≤ 1 / m := by
  let k : ℝ → ℝ := fun t ↦ 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)
  have hk : IntegrableOn k (Ioi m) :=
    integrable_one_div_harperCauchyKernel.integrableOn
  have hpow : IntegrableOn (fun t : ℝ ↦ t ^ (-2 : ℝ)) (Ioi m) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hm
  rw [integral_Ici_eq_integral_Ioi]
  calc
    (∫ t in Ioi m, k t) ≤ ∫ t in Ioi m, t ^ (-2 : ℝ) := by
      apply integral_mono_ae hk hpow
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := hm.trans ht
      have hsqpos : 0 < t ^ 2 := sq_pos_of_pos htpos
      have hdenle : t ^ 2 ≤ (1 / 2 : ℝ) ^ 2 + t ^ 2 := by norm_num
      calc
        k t ≤ 1 / t ^ 2 := one_div_le_one_div_of_le hsqpos hdenle
        _ = t ^ (-2 : ℝ) := by
          rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
            Real.rpow_neg htpos.le, Real.rpow_two]
          rw [one_div]
    _ = 1 / m := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hm]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      ring

/-- Reflection preserves the Cauchy-kernel half-tail. -/
theorem integral_Iic_neg_one_div_harperCauchyKernel_eq_Ici
    (m : ℝ) :
    (∫ t in Iic (-m), 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) =
      ∫ t in Ici m, 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2) := by
  let k : ℝ → ℝ := fun t ↦ 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)
  calc
    (∫ t in Iic (-m), k t) = ∫ t in Iic (-m), k (-t) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro t ht
      unfold k
      ring
    _ = ∫ t in Ioi m, k t := by
      simpa only [neg_neg] using! integral_comp_neg_Iic (-m) k
    _ = ∫ t in Ici m, k t := integral_Ici_eq_integral_Ioi.symm

/-- The complete two-sided scalar tail is at most `2/M`. -/
theorem integral_harperEulerTailSet_one_div_cauchyKernel_le
    {M : ℕ} (hM : 1 ≤ M) :
    (∫ t in harperEulerTailSet M,
      1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) ≤ 2 / (M : ℝ) := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hdisj : Disjoint (Iic (-((M : ℕ) : ℝ))) (Ici (M : ℝ)) := by
    rw [Set.disjoint_left]
    intro t htleft htright
    change t ≤ -((M : ℕ) : ℝ) at htleft
    change (M : ℝ) ≤ t at htright
    linarith
  have hk := integrable_one_div_harperCauchyKernel
  rw [harperEulerTailSet,
    setIntegral_union hdisj measurableSet_Ici hk.integrableOn hk.integrableOn,
    integral_Iic_neg_one_div_harperCauchyKernel_eq_Ici]
  have hhalf := integral_Ici_one_div_harperCauchyKernel_le hMR
  calc
    (∫ t in Ici (M : ℝ), 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) +
          ∫ t in Ici (M : ℝ), 1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2) ≤
        1 / (M : ℝ) + 1 / (M : ℝ) := add_le_add hhalf hhalf
    _ = 2 / (M : ℝ) := by ring

/-- The explicit constant supplied by the formalized elementary Mertens
bound. -/
noncomputable def harperExplicitMertensConstant : ℝ :=
  Real.exp
    (1 - Real.log (Real.log 2) +
      2 * (Real.log 4 + 4) / Real.log 2)

theorem harperExplicitMertensConstant_pos :
    0 < harperExplicitMertensConstant := by
  unfold harperExplicitMertensConstant
  positivity

/-- The mean normalized tail is explicitly `O(1/M)`, uniformly in the
Euler cutoff. -/
theorem integral_harperEulerTailRemainder_le
    {y M : ℕ} (hy : 2 ≤ y) (hM : 1 ≤ M) :
    (∫ omega, harperEulerTailRemainder y M omega ∂μ) ≤
      2 * harperExplicitMertensConstant / (M : ℝ) := by
  have hlog : 0 < Real.log (y : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < y by omega)
  have hnormalizer :
      primeEnergyNormalizer y / Real.log (y : ℝ) ≤
        harperExplicitMertensConstant := by
    apply (div_le_iff₀ hlog).2
    simpa only [harperExplicitMertensConstant] using!
      primeEnergyNormalizer_le_mertensConstant_mul_log hy
  have hkernel_nonneg :
      0 ≤ ∫ t in harperEulerTailSet M,
        1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2) :=
    setIntegral_nonneg (measurableSet_harperEulerTailSet M)
      fun t ht ↦ by positivity
  have hkernel := integral_harperEulerTailSet_one_div_cauchyKernel_le hM
  rw [integral_harperEulerTailRemainder]
  calc
    (primeEnergyNormalizer y *
          (∫ t in harperEulerTailSet M,
            1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2))) /
        Real.log (y : ℝ) =
      (primeEnergyNormalizer y / Real.log (y : ℝ)) *
        (∫ t in harperEulerTailSet M,
          1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) := by ring
    _ ≤ harperExplicitMertensConstant *
        (∫ t in harperEulerTailSet M,
          1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) :=
      mul_le_mul_of_nonneg_right hnormalizer hkernel_nonneg
    _ ≤ harperExplicitMertensConstant * (2 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hkernel harperExplicitMertensConstant_pos.le
    _ = 2 * harperExplicitMertensConstant / (M : ℝ) := by ring

theorem integrable_harperEulerTailRemainder_twoThird
    {y : ℕ} (hy : 1 < y) (M : ℕ) :
    Integrable (fun omega ↦
      harperEulerTailRemainder y M omega ^ harperTwoThird) μ := by
  apply integrable_rpow_of_integrable_nonneg
    (integrable_harperEulerTailRemainder y M)
  · exact harperEulerTailRemainder_nonneg hy M
  · norm_num [harperTwoThird]
  · norm_num [harperTwoThird]

/-- Jensen upgrades the first-moment tail estimate to the required
fractional moment. -/
theorem integral_harperEulerTailRemainder_twoThird_le_rpow_integral
    {y : ℕ} (hy : 1 < y) (M : ℕ) :
    (∫ omega,
      harperEulerTailRemainder y M omega ^ harperTwoThird ∂μ) ≤
      (∫ omega, harperEulerTailRemainder y M omega ∂μ) ^
        harperTwoThird := by
  let g : ℝ → ℝ := fun x ↦ x ^ harperTwoThird
  let R : Omega → ℝ := harperEulerTailRemainder y M
  have hR : Integrable R μ := integrable_harperEulerTailRemainder y M
  have hRq : Integrable (g ∘ R) μ := by
    simpa only [g, R, Function.comp_apply] using!
      integrable_harperEulerTailRemainder_twoThird hy M
  have hJ :=
    (Real.concaveOn_rpow
      (by norm_num [harperTwoThird])
      (by norm_num [harperTwoThird])).le_map_integral
      (Real.continuous_rpow_const
        (by norm_num [harperTwoThird])).continuousOn
      isClosed_Ici
      (ae_of_all μ fun omega ↦
        harperEulerTailRemainder_nonneg hy M omega)
      hR hRq
  simpa only [g, R, Function.comp_apply] using! hJ

/-- Explicit polynomial decay of the exact omitted tail in the `2/3`
moment required by `HarperWeightedAssembly`. -/
theorem integral_harperEulerTailRemainder_twoThird_le
    {y M : ℕ} (hy : 2 ≤ y) (hM : 1 ≤ M) :
    (∫ omega,
      harperEulerTailRemainder y M omega ^ harperTwoThird ∂μ) ≤
      (2 * harperExplicitMertensConstant / (M : ℝ)) ^
        harperTwoThird := by
  have hy1 : 1 < y := by omega
  have hJ :=
    integral_harperEulerTailRemainder_twoThird_le_rpow_integral hy1 M
  have hmean := integral_harperEulerTailRemainder_le hy hM
  have hmean_nonneg :
      0 ≤ ∫ omega, harperEulerTailRemainder y M omega ∂μ :=
    integral_nonneg fun omega ↦ harperEulerTailRemainder_nonneg hy1 M omega
  exact hJ.trans (Real.rpow_le_rpow hmean_nonneg hmean
    (by norm_num [harperTwoThird]))

/-- Joint integrability of the unweighted density on an actual unit
interval. -/
theorem integrable_harperEulerDensity_prod_unitInterval
    (y : ℕ) (positive : Bool) (n : ℕ) :
    Integrable
      (fun w : ℝ × Omega ↦ harperEulerDensity y w.2 w.1)
      ((volume.restrict (harperEulerUnitInterval positive n)).prod μ) := by
  cases positive with
  | false =>
      simp only [harperEulerUnitInterval, Bool.false_eq_true, if_false]
      apply Integrable.of_bound
        (measurable_harperEulerDensity_joint y).aestronglyMeasurable
        (harperEulerDensityUniformBound y)
      exact ae_of_all _ fun w ↦ by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (harperEulerDensity_nonneg y w.2 w.1)]
        exact harperEulerDensity_le_uniformBound y w.2 w.1
  | true =>
      simp only [harperEulerUnitInterval, if_true]
      apply Integrable.of_bound
        (measurable_harperEulerDensity_joint y).aestronglyMeasurable
        (harperEulerDensityUniformBound y)
      exact ae_of_all _ fun w ↦ by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (harperEulerDensity_nonneg y w.2 w.1)]
        exact harperEulerDensity_le_uniformBound y w.2 w.1

theorem integrable_harperEulerLocalEnergy
    (y : ℕ) (positive : Bool) (n : ℕ) :
    Integrable (harperEulerLocalEnergy y positive n) μ := by
  let ν : Measure ℝ :=
    volume.restrict (harperEulerUnitInterval positive n)
  let F : ℝ × Omega → ℝ := fun w ↦ harperEulerDensity y w.2 w.1
  have hF : Integrable F (ν.prod μ) := by
    simpa only [ν, F] using!
      integrable_harperEulerDensity_prod_unitInterval y positive n
  have hinner : Integrable (fun omega ↦ ∫ t, F (t, omega) ∂ν) μ :=
    hF.integral_prod_right
  simpa only [harperEulerLocalEnergy, ν, F] using!
    hinner.div_const (Real.log (y : ℝ))

theorem integrable_harperEulerLocalEnergy_twoThird
    {y : ℕ} (hy : 1 < y) (positive : Bool) (n : ℕ) :
    Integrable (fun omega ↦
      harperEulerLocalEnergy y positive n omega ^ harperTwoThird) μ := by
  apply integrable_rpow_of_integrable_nonneg
    (integrable_harperEulerLocalEnergy y positive n)
  · exact harperEulerLocalEnergy_nonneg hy positive n
  · norm_num [harperTwoThird]
  · norm_num [harperTwoThird]

/-- The concrete Parseval assembly with its remainder fully discharged.
Only the scheduled local interval estimates remain as inputs. -/
theorem integral_harperInitialNormalizedEnergy_twoThird_le_of_eulerLocalIntervals
    {A : ℝ} {y M : ℕ} (hy : 2 ≤ y) (hM : 1 ≤ M)
    (hmoment : ∀ d n, n < M →
      (∫ omega,
        harperEulerLocalEnergy y d n omega ^ harperTwoThird ∂μ) ≤
          A * harperLocalMomentLoss n) :
    (∫ omega,
      harperInitialNormalizedEnergy y omega ^ harperTwoThird ∂μ) ≤
      2 * A * 4 ^ harperTwoThird *
          ∑ n ∈ Finset.range M, harperGlobalMomentSeriesTerm n +
        (2 * harperExplicitMertensConstant / (M : ℝ)) ^
          harperTwoThird := by
  have hy1 : 1 < y := by omega
  apply integral_harperInitialNormalizedEnergy_twoThird_le_of_localIntervals
    hy1 (harperEulerLocalEnergy y) (harperEulerTailRemainder y M)
  · intro d n hn omega
    exact harperEulerLocalEnergy_nonneg hy1 d n omega
  · intro d n hn
    exact (integrable_harperEulerLocalEnergy y d n).aestronglyMeasurable
  · intro d n hn
    exact integrable_harperEulerLocalEnergy_twoThird hy1 d n
  · exact hmoment
  · exact harperEulerTailRemainder_nonneg hy1 M
  · exact integrable_harperEulerTailRemainder_twoThird hy1 M
  · exact integral_harperEulerTailRemainder_twoThird_le hy hM
  · exact harperInitialNormalizedEnergy_le_eulerAssembly_add_tail hy1 M

end Problem520
end Erdos
