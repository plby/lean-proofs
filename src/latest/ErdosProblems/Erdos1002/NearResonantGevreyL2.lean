import ErdosProblems.Erdos1002.NearResonantGevrey
import ErdosProblems.Erdos1002.NearResonantPoleL2
import ErdosProblems.Erdos1002.NearResonantPeriodicSmooth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Integrated Gevrey bounds for the near-resonant pole

This file integrates the pointwise estimate from `NearResonantGevrey`.
The deleted interval `|x| < a` is used explicitly, and the residual
`|x|⁻¹` factor is integrated rather than replaced by `a⁻¹`.  This is the
source of the sharp extra factor `a⁻¹` in the squared derivative mass.
-/

open Filter MeasureTheory Set
open scoped BigOperators Real

namespace Erdos1002

noncomputable section

private theorem inv_abs_sq_le_nearWPositiveSqEnvelope
    (a x : ℝ) (ha : 0 < a) (hax : a ≤ |x|) :
    |x|⁻¹ ^ 2 ≤ nearWPositiveSqEnvelope a |x| := by
  have hx : 0 < |x| := ha.trans_le hax
  have hsum : a + |x| ≤ 2 * |x| := by linarith
  have hsquare : (a + |x|) ^ 2 ≤ (2 * |x|) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsum 2
  have henv : nearWPositiveSqEnvelope a |x| =
      16 / (a + |x|) ^ 2 := by
    unfold nearWPositiveSqEnvelope scaleDecayEnvelope
    field_simp [ha.ne']
  rw [henv, inv_pow, inv_eq_one_div]
  rw [div_le_div_iff₀ (sq_pos_of_pos hx)
    (sq_pos_of_pos (add_pos ha hx))]
  nlinarith

private theorem integrable_nearWPositiveSqEnvelope_comp_abs
    (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ nearWPositiveSqEnvelope a |x|) := by
  have hpos : IntegrableOn
      (fun x : ℝ ↦ nearWPositiveSqEnvelope a |x|) (Ioi 0) := by
    refine (nearWPositiveSqEnvelope_integrableOn_Ioi a ha).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [abs_of_pos hx]
  have hneg : IntegrableOn
      (fun x : ℝ ↦ nearWPositiveSqEnvelope a |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ ↦ -x) :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  have hunion := hneg.union hpos
  rw [Iic_union_Ioi] at hunion
  simpa only [IntegrableOn, Measure.restrict_univ] using! hunion

private theorem integral_nearWPositiveSqEnvelope_comp_abs
    (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, nearWPositiveSqEnvelope a |x| = 32 / a := by
  rw [integral_comp_abs, integral_nearWPositiveSqEnvelope_Ioi a ha]
  ring

/-- The integrated Gevrey estimate with every constant and every
dependence on `j` and `a` explicit. -/
theorem nearWDerivNormSqMass_le_gevrey
    (j : ℕ) (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε)
    (haε : a ≤ ε / 4) :
    nearWDerivNormSqMass a ε j ≤
      (2 * nearGevreyProfileConstant * 192 ^ j *
          (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j) ^ 2 * (32 / a) := by
  let B : ℝ := 2 * nearGevreyProfileConstant * 192 ^ j *
    (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j
  have hf : Integrable
      (fun x : ℝ ↦ ‖iteratedDeriv j (nearW a ε) x‖ ^ 2) :=
    integrable_norm_iteratedDeriv_nearW_sq a ε ha hε haε j
  have hg : Integrable
      (fun x : ℝ ↦ B ^ 2 * nearWPositiveSqEnvelope a |x|) :=
    (integrable_nearWPositiveSqEnvelope_comp_abs a ha).const_mul (B ^ 2)
  have hpoint : ∀ x : ℝ,
      ‖iteratedDeriv j (nearW a ε) x‖ ^ 2 ≤
        B ^ 2 * nearWPositiveSqEnvelope a |x| := by
    intro x
    by_cases hxa : |x| < a
    · rw [iteratedDeriv_nearW_eq_zero_of_abs_lt j a ε x ha haε hxa,
        norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0)]
      exact mul_nonneg (sq_nonneg _) (by
        unfold nearWPositiveSqEnvelope scaleDecayEnvelope
        positivity)
    · have hax : a ≤ |x| := le_of_not_gt hxa
      have hnorm := norm_iteratedDeriv_nearW_le
        j a ε x ha hε haε hax
      have hnormB : ‖iteratedDeriv j (nearW a ε) x‖ ≤ B * |x|⁻¹ := by
        simpa only [B] using! hnorm
      calc
        ‖iteratedDeriv j (nearW a ε) x‖ ^ 2 ≤
            (B * |x|⁻¹) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnormB 2
        _ = B ^ 2 * |x|⁻¹ ^ 2 := by ring
        _ ≤ B ^ 2 * nearWPositiveSqEnvelope a |x| :=
          mul_le_mul_of_nonneg_left
            (inv_abs_sq_le_nearWPositiveSqEnvelope a x ha hax)
            (sq_nonneg B)
  have hmono := integral_mono_ae hf hg (Filter.Eventually.of_forall hpoint)
  unfold nearWDerivNormSqMass
  calc
    ∫ x : ℝ, ‖iteratedDeriv j (nearW a ε) x‖ ^ 2 ≤
        ∫ x : ℝ, B ^ 2 * nearWPositiveSqEnvelope a |x| := hmono
    _ = B ^ 2 * (32 / a) := by
      rw [integral_const_mul,
        integral_nearWPositiveSqEnvelope_comp_abs a ha]
    _ = (2 * nearGevreyProfileConstant * 192 ^ j *
          (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j) ^ 2 * (32 / a) := by
      rfl

/-- The preceding one-dimensional bound inserted into the exact disjoint-cell
identity.  This is the literal physical-space estimate for the function
called `b_p` in Proposition 3.2 of the manuscript. -/
theorem integral_unit_norm_iteratedDeriv_smoothNearPrimitivePoleSum_sq_le_gevrey
    (j p : ℕ) (a ε : ℝ) (hp : 2 ≤ p)
    (ha : 0 < a) (hε : 0 < ε) (haε : a ≤ ε / 4)
    (hεhalf : ε < 1 / 2) :
    (∫ alpha in (0 : ℝ)..1,
      ‖iteratedDeriv j (smoothNearPrimitivePoleSum a ε p) alpha‖ ^ 2) ≤
      (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) *
        (((p : ℝ) ^ 2) ^ j) ^ 2 *
          ((2 * nearGevreyProfileConstant * 192 ^ j *
              (j.factorial : ℝ) ^ 2 * a⁻¹ ^ j) ^ 2 * (32 / a)) := by
  rw [integral_unit_norm_iteratedDeriv_smoothNearPrimitivePoleSum_sq_eq
    a ε p j hp ha hε haε hεhalf]
  have hcoef : 0 ≤
      (Nat.totient p : ℝ) * (1 / (p : ℝ) ^ 2) *
        (((p : ℝ) ^ 2) ^ j) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left
    (nearWDerivNormSqMass_le_gevrey j a ε ha hε haε) hcoef

end

end Erdos1002
