import ErdosProblems.Erdos67.MRGSA10SecondSecondaryChebyshevReduction
import ErdosProblems.Erdos67.MRGSA10GlobalSecondary

/-!
# Integrated Chebyshev reduction for the second GS A.10 secondary

The generalized-Mangoldt variable has already been summed in
`MRGSA10SecondSecondaryChebyshevReduction`.  Here the remaining
`X^(1-alpha)` is integrated exactly.  This is the source-faithful step which
produces `X / log X`, rather than the weaker interval-length bound.
-/

open scoped BigOperators
open Set MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Finite positive Dirichlet masses decrease as their real exponent
increases. -/
theorem gsFiniteNormDirichletMass_antitone
    (a : ArithmeticFunction ℂ) (X : ℕ) {sigma tau : ℝ}
    (hst : sigma ≤ tau) :
    gsFiniteNormDirichletMass a X tau ≤
      gsFiniteNormDirichletMass a X sigma := by
  classical
  unfold gsFiniteNormDirichletMass
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast (Finset.mem_Icc.mp hn).1
    · linarith
  · exact norm_nonneg _

/-- The actual second-secondary integrand is continuous in its shift. -/
theorem continuous_positivePrefixSum_secondSecondaryIntegrand
    (low high lambda : ArithmeticFunction ℂ) (X : ℕ) (eta : ℝ) :
    Continuous (fun alpha : ℝ ↦
      positivePrefixSum
        (fun n ↦ ((low * gsRealShift alpha lambda) *
          gsRealShift (2 * eta + alpha) high) n) X) := by
  unfold positivePrefixSum
  simp only [ArithmeticFunction.map_zero, sub_zero,
    ArithmeticFunction.mul_apply]
  apply continuous_finsetSum
  intro n hn
  apply continuous_finsetSum
  intro xy hxy
  apply Continuous.mul
  · apply continuous_finsetSum
    intro uv huv
    exact (continuous_gsRealShift_apply lambda uv.2).const_mul (low uv.1)
  · exact (continuous_gsRealShift_apply high xy.2).comp
      (continuous_const.add continuous_id)

private theorem rpow_one_sub_eq_mul_exp
    {X : ℕ} (hX : 0 < X) (alpha : ℝ) :
    (X : ℝ) ^ (1 - alpha) =
      (X : ℝ) * Real.exp (-Real.log (X : ℝ) * alpha) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hX)]
  rw [show Real.log (X : ℝ) * (1 - alpha) =
      Real.log (X : ℝ) + (-Real.log (X : ℝ) * alpha) by ring,
    Real.exp_add, Real.exp_log (by exact_mod_cast hX)]

private theorem intervalIntegral_exp_neg_log_le
    {X : ℕ} (hX : 2 ≤ X) {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ alpha in (0 : ℝ)..eta,
        Real.exp (-Real.log (X : ℝ) * alpha)) ≤
      1 / Real.log (X : ℝ) := by
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hneg : -Real.log (X : ℝ) < 0 := neg_neg_of_pos hlog
  rw [intervalIntegral.integral_of_le heta]
  have hmono := MeasureTheory.integral_mono_measure
    (Measure.restrict_mono_set volume
      (show Set.Ioc (0 : ℝ) eta ⊆ Set.Ioi 0 by
        intro x hx
        exact hx.1))
    (show 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
        (fun alpha : ℝ ↦ Real.exp (-Real.log (X : ℝ) * alpha)) from
      Filter.Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)
    (integrableOn_exp_mul_Ioi hneg 0)
  rw [integral_exp_mul_Ioi hneg 0] at hmono
  simpa [one_div] using hmono

/-- Source Lemma 2.4 after integrating the distinguished-prime Chebyshev
estimate.  Only the two finite Euler masses remain; both are evaluated at
fixed exponents independent of the integration variable. -/
theorem norm_gsA10SecondSecondaryPrefix_le_chebyshev_masses
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ}
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {eta : ℝ} (heta0 : 0 ≤ eta) (hetaHalf : eta ≤ 1 / 2)
    (hX : 2 ≤ X) :
    ‖gsA10SecondSecondaryPrefix
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y) X eta‖ ≤
      12 * (Real.log 4 + 4) *
        ((X : ℝ) / Real.log (X : ℝ)) *
        gsFiniteNormDirichletMass
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y) X (1 - eta) *
        gsFiniteNormDirichletMass
          (gsA9HighArithmetic f y) X (1 + 2 * eta) := by
  let low := gsA10TwoBlockAlternatingLow f P₁ P₂ y
  let high := gsA9HighArithmetic f y
  let lambda := gsA9HighGeneralizedMangoldt hmul y
  let C : ℝ := 12 * (Real.log 4 + 4)
  let L : ℝ := gsFiniteNormDirichletMass low X (1 - eta)
  let H : ℝ := gsFiniteNormDirichletMass high X (1 + 2 * eta)
  have hXpos : 0 < X := by omega
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX)
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    unfold gsFiniteNormDirichletMass
    positivity
  have hHnonneg : 0 ≤ H := by
    dsimp [H]
    unfold gsFiniteNormDirichletMass
    positivity
  have hcont : Continuous (fun alpha : ℝ ↦
      positivePrefixSum
        (fun n ↦ ((low * gsRealShift alpha lambda) *
          gsRealShift (2 * eta + alpha) high) n) X) :=
    continuous_positivePrefixSum_secondSecondaryIntegrand low high lambda X eta
  have hpoint : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ‖positivePrefixSum
          (fun n ↦ ((low * gsRealShift alpha lambda) *
            gsRealShift (2 * eta + alpha) high) n) X‖ ≤
        C * (X : ℝ) * L * H *
          Real.exp (-Real.log (X : ℝ) * alpha) := by
    intro alpha halpha
    have hraw := norm_positivePrefixSum_secondSecondaryIntegrand_le
      (y := y) (X := X) (eta := eta) (alpha := alpha)
      hmul hcomp hbound P₁ P₂ hQ₂ hQ₃ halpha.1
        (halpha.2.trans hetaHalf) (by linarith [halpha.2, hetaHalf])
    have hmass : gsFiniteNormDirichletMass low X (1 - alpha) ≤ L := by
      exact gsFiniteNormDirichletMass_antitone low X (by linarith [halpha.2])
    rw [rpow_one_sub_eq_mul_exp hXpos alpha] at hraw
    calc
      ‖positivePrefixSum
          (fun n ↦ ((low * gsRealShift alpha lambda) *
            gsRealShift (2 * eta + alpha) high) n) X‖ ≤
          C * ((X : ℝ) * Real.exp (-Real.log (X : ℝ) * alpha)) *
            gsFiniteNormDirichletMass low X (1 - alpha) * H := hraw
      _ ≤ C * ((X : ℝ) * Real.exp (-Real.log (X : ℝ) * alpha)) *
            L * H := by
        apply mul_le_mul_of_nonneg_right _ hHnonneg
        apply mul_le_mul_of_nonneg_left hmass
        exact mul_nonneg hCnonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
      _ = C * (X : ℝ) * L * H *
            Real.exp (-Real.log (X : ℝ) * alpha) := by ring
  unfold gsA10SecondSecondaryPrefix
  change ‖∫ alpha in (0 : ℝ)..eta,
      positivePrefixSum
        (fun n ↦ ((low * gsRealShift alpha lambda) *
          gsRealShift (2 * eta + alpha) high) n) X‖ ≤ _
  calc
    ‖∫ alpha in (0 : ℝ)..eta,
        positivePrefixSum
          (fun n ↦ ((low * gsRealShift alpha lambda) *
            gsRealShift (2 * eta + alpha) high) n) X‖ ≤
        ∫ alpha in (0 : ℝ)..eta,
          ‖positivePrefixSum
            (fun n ↦ ((low * gsRealShift alpha lambda) *
              gsRealShift (2 * eta + alpha) high) n) X‖ :=
      intervalIntegral.norm_integral_le_integral_norm heta0
    _ ≤ ∫ alpha in (0 : ℝ)..eta,
          C * (X : ℝ) * L * H *
            Real.exp (-Real.log (X : ℝ) * alpha) := by
      apply intervalIntegral.integral_mono_on heta0
      · exact hcont.norm.intervalIntegrable 0 eta
      · have hmajorcont : Continuous (fun alpha : ℝ ↦
            C * (X : ℝ) * L * H *
              Real.exp (-Real.log (X : ℝ) * alpha)) := by
          fun_prop
        exact hmajorcont.intervalIntegrable 0 eta
      · exact hpoint
    _ = C * (X : ℝ) * L * H *
          (∫ alpha in (0 : ℝ)..eta,
            Real.exp (-Real.log (X : ℝ) * alpha)) := by
      simp only [intervalIntegral.integral_const_mul]
    _ ≤ C * (X : ℝ) * L * H *
          (1 / Real.log (X : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact intervalIntegral_exp_neg_log_le hX heta0
      · exact mul_nonneg (mul_nonneg (mul_nonneg hCnonneg (by positivity)) hLnonneg)
          hHnonneg
    _ = 12 * (Real.log 4 + 4) *
        ((X : ℝ) / Real.log (X : ℝ)) *
        gsFiniteNormDirichletMass low X (1 - eta) *
        gsFiniteNormDirichletMass high X (1 + 2 * eta) := by
      dsimp [C, L, H]
      rw [div_eq_mul_inv]
      ring

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.gsFiniteNormDirichletMass_antitone
#print axioms Erdos67.MRHalaszBands.norm_gsA10SecondSecondaryPrefix_le_chebyshev_masses
