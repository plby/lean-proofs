import ErdosProblems.Erdos67b.MRGSCentralAmplitude
import ErdosProblems.Erdos67b.MRGSTypicalSourceRenormalization

/-!
# The actual scheduled central dyadic profile

The center amplitude is proved small. The upper distance transfers to all
dyadic prefixes with one fixed Mertens allowance, and the finite Abel
bridge retains reciprocal decay with a vanishing logarithmic error.
-/

open Filter
open scoped BigOperators

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrGS_pretentiousDistSq_dyadic_upper
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {X Z : ℕ} (hX : 2 ≤ X) (hXZ : X ≤ Z) (hZX : Z ≤ 2 * X) (t : ℝ)
    (hdist : pretentiousDistSq f (archimedeanTwist t) X ≤
      Real.log (Real.log (X : ℝ)) / 8) :
    pretentiousDistSq f (archimedeanTwist t) Z ≤
      Real.log (Real.log (Z : ℝ)) / 8 + mrCofactorDistanceLoss := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogXZ : Real.log (X : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.log_le_log hXpos (by exact_mod_cast hXZ)
  have hlogZX : Real.log (Z : ℝ) ≤ 2 * Real.log (X : ℝ) := by
    have hupper := Real.log_le_log
      (show (0 : ℝ) < Z by exact_mod_cast (show 0 < Z by omega))
      (show (Z : ℝ) ≤ 2 * X by exact_mod_cast hZX)
    rw [Real.log_mul (by norm_num) hXpos.ne'] at hupper
    have htwo : Real.log 2 ≤ Real.log (X : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hX)
    linarith
  have htail := mrPretentiousDistSq_tail_le_cofactorLoss hX hXZ hlogZX
    (fun p hp ↦ hbound p hp.pos) (fun p hp ↦ (norm_archimedeanTwist hp.pos t).le)
  have hloglog := Real.log_le_log hlogX hlogXZ
  linarith

def mrGSCentralDyadicErrorConstant : ℝ :=
  6 * (mrGSTypicalSourceErrorConstant * Real.exp (7 * mrCofactorDistanceLoss))

theorem mrGSCentralDyadicErrorConstant_nonneg : 0 ≤ mrGSCentralDyadicErrorConstant := by
  have hC := mrGSTypicalSourceErrorConstant_nonneg
  unfold mrGSCentralDyadicErrorConstant
  positivity

theorem mrGS_exists_scheduled_central_dyadic_profile
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
      ∀ u : ℝ, |u| ≤ (Real.log (X : ℝ)) ^ (1 / 16 : ℝ) →
        ‖dyadicVerticalDirichletPolynomial (Finset.Ioc X (2 * X))
          (mrIndexedTypicalCoefficient (Finset.Icc 1 J)
            (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f) X (t₁ + u)‖ ≤
          epsilon * (1 + |u|)⁻¹ +
            mrGSCentralDyadicErrorConstant * (Real.log (X : ℝ)) ^ (-1 / 20 : ℝ) := by
  obtain ⟨M₀, X₁, hM₀, hX₁, hcenter⟩ :=
    mrExists_uniform_small_scheduled_central_prefixes (by positivity : 0 < epsilon / 6)
  obtain ⟨X₂, _, hcount⟩ := mrExists_eventually_source_maskCount_le_log_rpow
    (by norm_num : (0 : ℝ) < 1 / 80)
  obtain ⟨X₃, hX₃⟩ := eventually_atTop.1
    (EulerSubpower.tendsto_log_nat_atTop.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨M₀, max X₁ (max X₂ X₃), hM₀, hX₁.trans (le_max_left _ _), ?_⟩
  intro M X hM hX eta p₁ q₁ heta hp hq hpq hlogq hbudget hmertens
    J hupper f hmul hbound hnonpret t₁ ht₁ hdist u hu
  have hXX₁ : X₁ ≤ X := (le_max_left _ _).trans hX
  have hXX₂ : X₂ ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX)
  have hXX₃ : X₃ ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hX)
  have hXtwo : 2 ≤ X := hX₁.trans hXX₁
  have hXpos : 0 < X := by omega
  have hlogX := hX₃ X hXX₃
  have hLX : 0 < Real.log (X : ℝ) := by linarith
  let C := mrGSTypicalSourceErrorConstant * Real.exp (7 * mrCofactorDistanceLoss)
  have hC : 0 ≤ C :=
    mul_nonneg mrGSTypicalSourceErrorConstant_nonneg (Real.exp_pos _).le
  let a := mrIndexedTypicalCoefficient (Finset.Icc 1 J)
    (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f
  have hprefix : ∀ Z ∈ Finset.Icc X (2 * X),
      ‖gsTwistedPositivePrefixSum a (t₁ + u) Z / (Z : ℂ)‖ ≤
        2 * (epsilon / 6) * (1 + |u|)⁻¹ +
          2 * C * (Real.log (X : ℝ)) ^ (-1 / 20 : ℝ) := by
    intro Z hZ
    have hXZ := (Finset.mem_Icc.mp hZ).1
    have hZX := (Finset.mem_Icc.mp hZ).2
    have hZpos : 0 < Z := hXpos.trans_le hXZ
    have hlogXZ : Real.log (X : ℝ) ≤ Real.log (Z : ℝ) :=
      Real.log_le_log (by exact_mod_cast hXpos) (by exact_mod_cast hXZ)
    have hLZ : 1 ≤ Real.log (Z : ℝ) := hlogX.trans hlogXZ
    have hcountZ : (2 : ℝ) ^ (Finset.Icc 1 J).card ≤
        (Real.log (Z : ℝ)) ^ (1 / 80 : ℝ) := by
      simp only [Nat.card_Icc, Nat.add_sub_cancel_right]
      exact (hcount X hXX₂ hq J hupper).trans
        (Real.rpow_le_rpow hLX.le hlogXZ (by norm_num))
    have hwindowZ : |u| ≤ (Real.log (Z : ℝ)) ^ (1 / 16 : ℝ) :=
      hu.trans (Real.rpow_le_rpow hLX.le hlogXZ (by norm_num))
    have hr := mrGS_norm_indexedTypical_central_error_le_source_of_distanceAllowance
      (Finset.Icc 1 J) (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j))
      (fun j hj p hpB ↦ (mem_primesInBlock.mp hpB).1) hmul hbound t₁ u
      mrCofactorDistanceLoss_nonneg (hXtwo.trans hXZ) hLZ hwindowZ hcountZ (by
        intro j hj p hpB
        exact (mrScheduledPrime_log_le_sqrt heta hp hq (by linarith) hlogq hbudget
          hupper hj hpB).trans (Real.sqrt_le_sqrt hlogXZ))
      (mrGS_pretentiousDistSq_dyadic_upper (fun n _ ↦ hbound n) hXtwo hXZ hZX t₁ hdist)
    have hc := hcenter hM hXX₁ heta hp hq hpq hlogq hbudget hmertens J hupper
      hmul (fun n _ ↦ hbound n) hnonpret t₁ ht₁ Z hZ
    have hnorm := norm_le_two_mul_inv_one_add_abs_mul_add_of_renormalized
      (show 0 ≤ 2 * C * (Real.log (Z : ℝ)) ^ (-1 / 20 : ℝ) by positivity)
      (show 0 ≤ epsilon / 6 by positivity)
      (norm_gsPrefixArchimedeanFactor_le_two_div_one_add_abs u hZpos) hc hr
    apply hnorm.trans
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hLX hlogXZ (by norm_num)) (by positivity)
  have hdyadic := norm_dyadicVerticalDirichletPolynomial_le_of_normalized_gsPrefixes
    a hXpos (t₁ + u) (by positivity : 0 ≤ 2 * (epsilon / 6) * (1 + |u|)⁻¹ +
      2 * C * (Real.log (X : ℝ)) ^ (-1 / 20 : ℝ)) hprefix
  apply hdyadic.trans_eq
  dsimp only [C, mrGSCentralDyadicErrorConstant]
  ring

end

end Erdos67b
