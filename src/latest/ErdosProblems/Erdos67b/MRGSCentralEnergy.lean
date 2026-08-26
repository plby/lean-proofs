import ErdosProblems.Erdos67b.MRGSCentralDyadicProfile
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Vanishing central-window energy for the actual scheduled polynomial -/

open Filter MeasureTheory
open scoped Topology Interval

namespace Erdos67b

noncomputable section

theorem mrIntegral_normSq_le_of_reciprocal_profile
    (G : ℝ → ℂ) (hG : Continuous G) {a b R : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hprofile : ∀ u : ℝ, |u| ≤ R → ‖G u‖ ≤ a * (1 + |u|)⁻¹ + b) :
    (∫ u in -R..R, Complex.normSq (G u)) ≤ 2 * Real.pi * a ^ 2 + 4 * R * b ^ 2 := by
  have hbase : Continuous (fun u : ℝ ↦ 1 + u ^ 2) := by fun_prop
  have hkernel : Continuous (fun u : ℝ ↦ (1 + u ^ 2)⁻¹) :=
    hbase.inv₀ (fun u ↦ (show 1 + u ^ 2 ≠ 0 from ne_of_gt (by positivity)))
  have hmajor : Continuous (fun u : ℝ ↦ 2 * a ^ 2 * (1 + u ^ 2)⁻¹ + 2 * b ^ 2) :=
    (hkernel.const_mul _).add continuous_const
  have hmono : (∫ u in -R..R, Complex.normSq (G u)) ≤
      ∫ u in -R..R, 2 * a ^ 2 * (1 + u ^ 2)⁻¹ + 2 * b ^ 2 := by
    apply intervalIntegral.integral_mono_on (by linarith)
      ((Complex.continuous_normSq.comp hG).intervalIntegrable _ _)
      (hmajor.intervalIntegrable _ _)
    intro u hu
    have hp := hprofile u (abs_le.mpr ⟨hu.1, hu.2⟩)
    have hpos : 0 < 1 + |u| := by positivity
    have hinv : ((1 + |u|)⁻¹) ^ 2 ≤ (1 + u ^ 2)⁻¹ := by
      rw [inv_pow]
      apply inv_anti₀ (by positivity)
      nlinarith [sq_abs u, abs_nonneg u]
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hp
    have hcost := mul_le_mul_of_nonneg_left hinv (sq_nonneg a)
    simp only [Function.comp_apply, Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (a * (1 + |u|)⁻¹ - b)]
  have hintegral : (∫ u in -R..R, 2 * a ^ 2 * (1 + u ^ 2)⁻¹ + 2 * b ^ 2) =
      2 * a ^ 2 * (Real.arctan R - Real.arctan (-R)) + 4 * R * b ^ 2 := by
    rw [intervalIntegral.integral_add
      ((hkernel.const_mul (2 * a ^ 2)).intervalIntegrable _ _)
      intervalIntegrable_const, intervalIntegral.integral_const_mul,
      integral_inv_one_add_sq, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  apply hmono.trans
  rw [hintegral, Real.arctan_neg]
  have hpi := (Real.arctan_lt_pi_div_two R).le
  nlinarith [sq_nonneg a]

theorem mrGS_central_error_energy_eq {X : ℕ} (hlog : 0 < Real.log (X : ℝ)) (C : ℝ) :
    4 * (Real.log (X : ℝ)) ^ (1 / 16 : ℝ) *
        (C * (Real.log (X : ℝ)) ^ (-1 / 20 : ℝ)) ^ 2 =
      4 * C ^ 2 * (Real.log (X : ℝ)) ^ (-3 / 80 : ℝ) := by
  have hpower : ((Real.log (X : ℝ)) ^ (-1 / 20 : ℝ)) ^ 2 =
      (Real.log (X : ℝ)) ^ (-1 / 10 : ℝ) := by
    rw [← Real.rpow_mul_natCast hlog.le]
    norm_num
  rw [mul_pow, hpower]
  have hsum : (Real.log (X : ℝ)) ^ (1 / 16 : ℝ) *
      (Real.log (X : ℝ)) ^ (-1 / 10 : ℝ) =
        (Real.log (X : ℝ)) ^ (-3 / 80 : ℝ) := by
    rw [← Real.rpow_add hlog]
    norm_num
  calc
    _ = 4 * C ^ 2 * ((Real.log (X : ℝ)) ^ (1 / 16 : ℝ) *
        (Real.log (X : ℝ)) ^ (-1 / 10 : ℝ)) := by ring
    _ = _ := by rw [hsum]

theorem mrGS_tendsto_central_error_energy (C : ℝ) :
    Tendsto (fun X : ℕ ↦ 4 * C ^ 2 * (Real.log (X : ℝ)) ^ (-3 / 80 : ℝ))
      atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 80)).comp
    EulerSubpower.tendsto_log_nat_atTop
  simpa only [Function.comp_apply, neg_div, mul_zero] using h.const_mul (4 * C ^ 2)

theorem mrGS_exists_scheduled_central_energy_small
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ M₀ X₀ : ℕ, 0 < M₀ ∧ 2 ≤ X₀ ∧
      ∀ {M X : ℕ}, M₀ ≤ M → X₀ ≤ X →
      ∀ {eta p₁ q₁ : ℝ}, eta ≤ 1 / 12 → 2 ≤ p₁ → 1 ≤ q₁ →
        2 * p₁ ≤ q₁ → 1 ≤ Real.log q₁ →
        4096 * Real.log q₁ ≤ eta * p₁ →
        Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁ →
      ∀ J : ℕ, mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)) →
      ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
        (∀ n, ‖f n‖ ≤ 1) → MRArchimedeanNonpretentious f M X →
      ∀ t₁ : ℝ, |t₁| ≤ 3 * (X : ℝ) / 4 →
        pretentiousDistSq f (archimedeanTwist t₁) X ≤
          Real.log (Real.log (X : ℝ)) / 8 →
        let R := (Real.log (X : ℝ)) ^ (1 / 16 : ℝ)
        (∫ u in -R..R, Complex.normSq
          (dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X))
            (mrIndexedTypicalCoefficient (Finset.Icc 1 J)
              (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f) X (t₁ + u))) ≤
          epsilon := by
  let a := Real.sqrt (epsilon / (4 * Real.pi))
  have ha : 0 < a := Real.sqrt_pos.2 (div_pos hepsilon (by positivity))
  have haSq : a ^ 2 = epsilon / (4 * Real.pi) := Real.sq_sqrt (by positivity)
  have haBudget : 2 * Real.pi * a ^ 2 = epsilon / 2 := by
    rw [haSq]
    field_simp
    norm_num
  obtain ⟨M₀, X₁, hM₀, hX₁, hprofile⟩ := mrGS_exists_scheduled_central_dyadic_profile ha
  have hsmall := (tendsto_order.1
    (mrGS_tendsto_central_error_energy mrGSCentralDyadicErrorConstant)).2
      (epsilon / 2) (by positivity)
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.1 hsmall
  refine ⟨M₀, max X₁ X₂, hM₀, hX₁.trans (le_max_left _ _), ?_⟩
  intro M X hM hX eta p₁ q₁ heta hp hq hpq hlogq hbudget hmertens
    J hupper f hmul hbound hnonpret t₁ ht₁ hdist
  have hXX₁ : X₁ ≤ X := (le_max_left _ _).trans hX
  have hXX₂ : X₂ ≤ X := (le_max_right _ _).trans hX
  have hXtwo : 2 ≤ X := hX₁.trans hXX₁
  have hLX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  let R := (Real.log (X : ℝ)) ^ (1 / 16 : ℝ)
  let b := mrGSCentralDyadicErrorConstant * (Real.log (X : ℝ)) ^ (-1 / 20 : ℝ)
  let coeff := mrIndexedTypicalCoefficient (Finset.Icc 1 J)
    (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f
  let G : ℝ → ℂ := fun u ↦
    dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X)) coeff X (t₁ + u)
  have hG : Continuous G :=
    (continuous_dyadicVerticalDirichletPolynomial _ _ _).comp (continuous_const.add continuous_id)
  have hb : 0 ≤ b := mul_nonneg mrGSCentralDyadicErrorConstant_nonneg (Real.rpow_nonneg hLX.le _)
  have hR : 0 ≤ R := Real.rpow_nonneg hLX.le _
  have henergy := mrIntegral_normSq_le_of_reciprocal_profile G hG ha.le hb hR (by
    intro u hu
    exact hprofile hM hXX₁ heta hp hq hpq hlogq hbudget hmertens J hupper
      hmul hbound hnonpret t₁ ht₁ hdist u hu)
  have herror : 4 * R * b ^ 2 < epsilon / 2 := by
    dsimp only [R, b]
    rw [mrGS_central_error_energy_eq hLX]
    exact hX₂ X hXX₂
  change (∫ u in -R..R, Complex.normSq (G u)) ≤ epsilon
  rw [haBudget] at henergy
  linarith

end

end Erdos67b
