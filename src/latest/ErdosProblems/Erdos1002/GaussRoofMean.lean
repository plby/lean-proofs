import ErdosProblems.Erdos1002.GaussRoofIntegrability
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact mean of the Gauss roof

The first step is the endpoint-sensitive monomial identity
`∫₀¹ x^k (-log x) dx = 1/(k+1)^2`.  It is proved from an explicit primitive;
the limit at zero is included.  This is later summed against the even
geometric approximants to `(1+x)⁻¹`.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology Interval BigOperators

namespace Erdos1002

noncomputable section

/-- An explicit primitive for `x^k (-log x)` away from zero. -/
def negLogMonomialPrimitive (k : ℕ) (x : ℝ) : ℝ :=
  x ^ (k + 1) / ((k + 1 : ℕ) : ℝ) ^ 2 -
    x ^ (k + 1) * Real.log x / ((k + 1 : ℕ) : ℝ)

theorem hasDerivAt_negLogMonomialPrimitive
    (k : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (negLogMonomialPrimitive k)
      (x ^ k * (-Real.log x)) x := by
  have hn : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hpow : HasDerivAt (fun y : ℝ ↦ y ^ (k + 1))
      (((k + 1 : ℕ) : ℝ) * x ^ k) x := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel] using!
      (hasDerivAt_pow (k + 1) x)
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx
  unfold negLogMonomialPrimitive
  convert! (hpow.div_const (((k + 1 : ℕ) : ℝ) ^ 2)).sub
      ((hpow.mul hlog).div_const (((k + 1 : ℕ) : ℝ))) using 1
  field_simp [hn, hx]
  rw [pow_succ]
  ring

theorem intervalIntegrable_negLogMonomial (k : ℕ) :
    IntervalIntegrable (fun x : ℝ ↦ x ^ k * (-Real.log x))
      volume 0 1 := by
  have hlog : IntervalIntegrable (fun x : ℝ ↦ -Real.log x)
      volume 0 1 := intervalIntegral.intervalIntegrable_log'.neg
  have hmul := hlog.continuousOn_mul (continuousOn_id.pow k)
  apply hmul.congr
  intro x _hx
  simp only [Pi.pow_apply, id_eq]

theorem tendsto_negLogMonomialPrimitive_zero (k : ℕ) :
    Tendsto (negLogMonomialPrimitive k) (𝓝[>] 0) (𝓝 0) := by
  have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hpow : Tendsto (fun x : ℝ ↦ x ^ (k + 1)) (𝓝[>] 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun x : ℝ ↦ x ^ (k + 1)) 0 :=
      continuousAt_id.pow (k + 1)
    simpa using! (hcont.tendsto.mono_left inf_le_left)
  have hpowLog : Tendsto
      (fun x : ℝ ↦ x ^ (k + 1) * Real.log x)
      (𝓝[>] 0) (𝓝 0) := by
    have hrpowLog := tendsto_log_mul_rpow_nhdsGT_zero hkpos
    apply hrpowLog.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Real.rpow_natCast x (k + 1)]
    ring
  unfold negLogMonomialPrimitive
  simpa using!
    (hpow.div_const (((k + 1 : ℕ) : ℝ) ^ 2)).sub
      (hpowLog.div_const (((k + 1 : ℕ) : ℝ)))

theorem tendsto_negLogMonomialPrimitive_one (k : ℕ) :
    Tendsto (negLogMonomialPrimitive k) (𝓝[<] 1)
      (𝓝 (1 / (((k + 1 : ℕ) : ℝ) ^ 2))) := by
  have hcont : ContinuousAt (negLogMonomialPrimitive k) 1 := by
    unfold negLogMonomialPrimitive
    exact ((continuousAt_id.pow (k + 1)).div_const _).sub
      (((continuousAt_id.pow (k + 1)).mul
        (Real.continuousAt_log one_ne_zero)).div_const _)
  convert! hcont.tendsto.mono_left inf_le_left using 1
  simp [negLogMonomialPrimitive]

/-- Exact monomial-log integral, with both endpoint limits explicit. -/
theorem integral_zero_one_pow_mul_neg_log (k : ℕ) :
    (∫ x : ℝ in 0..1, x ^ k * (-Real.log x)) =
      1 / (((k + 1 : ℕ) : ℝ) ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := negLogMonomialPrimitive k)
    (fa := 0) (fb := 1 / (((k + 1 : ℕ) : ℝ) ^ 2))]
  · ring
  · norm_num
  · intro x hx
    exact hasDerivAt_negLogMonomialPrimitive k hx.1.ne'
  · exact intervalIntegrable_negLogMonomial k
  · exact tendsto_negLogMonomialPrimitive_zero k
  · exact tendsto_negLogMonomialPrimitive_one k

/-- The alternating monomial-log summands used to expand `(1+x)⁻¹`. -/
def alternatingNegLogMonomial (k : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ k * (x ^ k * (-Real.log x))

theorem integrable_alternatingNegLogMonomial_restrict (k : ℕ) :
    Integrable (alternatingNegLogMonomial k)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hbase : IntegrableOn (fun x : ℝ ↦ x ^ k * (-Real.log x))
      (Ioc 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
      (intervalIntegrable_negLogMonomial k)
  exact hbase.const_mul ((-1 : ℝ) ^ k)

theorem integral_norm_alternatingNegLogMonomial_restrict (k : ℕ) :
    (∫ x : ℝ, ‖alternatingNegLogMonomial k x‖
        ∂volume.restrict (Ioc (0 : ℝ) 1)) =
      1 / (((k + 1 : ℕ) : ℝ) ^ 2) := by
  have hnorm :
      (fun x : ℝ ↦ ‖alternatingNegLogMonomial k x‖) =ᵐ[
        volume.restrict (Ioc (0 : ℝ) 1)]
      (fun x : ℝ ↦ x ^ k * (-Real.log x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [alternatingNegLogMonomial, Real.norm_eq_abs, abs_mul,
      abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_mul,
      abs_pow, abs_of_pos hx.1, abs_neg,
      abs_of_nonpos (Real.log_nonpos hx.1.le hx.2)]
  rw [integral_congr_ae hnorm,
    ← intervalIntegral.integral_of_le (μ := volume) (by norm_num)]
  exact integral_zero_one_pow_mul_neg_log k

theorem summable_integral_norm_alternatingNegLogMonomial :
    Summable (fun k : ℕ ↦
      ∫ x : ℝ, ‖alternatingNegLogMonomial k x‖
        ∂volume.restrict (Ioc (0 : ℝ) 1)) := by
  rw [show (fun k : ℕ ↦
      ∫ x : ℝ, ‖alternatingNegLogMonomial k x‖
        ∂volume.restrict (Ioc (0 : ℝ) 1)) =
      (fun k : ℕ ↦ 1 / (((k + 1 : ℕ) : ℝ) ^ 2)) by
    funext k
    exact integral_norm_alternatingNegLogMonomial_restrict k]
  exact hasSum_zeta_two.summable.comp_injective
    Nat.succ_injective

/-- Pointwise geometric evaluation on the half-open unit interval. -/
theorem tsum_alternatingNegLogMonomial
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∑' k : ℕ, alternatingNegLogMonomial k x) =
      (-Real.log x) / (1 + x) := by
  have hnorm : ‖-x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos hx.1]
    exact hx.2
  have hgeo := (hasSum_geometric_of_norm_lt_one hnorm).mul_right (-Real.log x)
  calc
    (∑' k : ℕ, alternatingNegLogMonomial k x) =
        ∑' k : ℕ, (-x) ^ k * (-Real.log x) := by
      apply tsum_congr
      intro k
      unfold alternatingNegLogMonomial
      rw [neg_pow]
      ring
    _ = (1 - (-x))⁻¹ * (-Real.log x) := hgeo.tsum_eq
    _ = (-Real.log x) / (1 + x) := by
      have hxdenPos : 0 < 1 + x := by linarith [hx.1]
      field_simp [ne_of_gt hxdenPos]
      ring

/-- Exchange of the alternating geometric series and the logarithmic
integral.  Absolute summability is proved from the monomial formula above. -/
theorem integral_neg_log_div_one_add_eq_tsum :
    (∫ x : ℝ in Ioc (0 : ℝ) 1, (-Real.log x) / (1 + x)) =
      ∑' k : ℕ, (-1 : ℝ) ^ k /
        (((k + 1 : ℕ) : ℝ) ^ 2) := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hexchange := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := μ) (F := alternatingNegLogMonomial)
    integrable_alternatingNegLogMonomial_restrict
    summable_integral_norm_alternatingNegLogMonomial
  have hpoint :
      (fun x : ℝ ↦ ∑' k : ℕ, alternatingNegLogMonomial k x) =ᵐ[μ]
        (fun x : ℝ ↦ (-Real.log x) / (1 + x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with x hx hxne
    exact tsum_alternatingNegLogMonomial
      ⟨hx.1, lt_of_le_of_ne hx.2 hxne⟩
  rw [integral_congr_ae hpoint] at hexchange
  rw [← hexchange]
  apply tsum_congr
  intro k
  calc
    (∫ x : ℝ, alternatingNegLogMonomial k x ∂μ) =
        (-1 : ℝ) ^ k *
          ∫ x : ℝ, x ^ k * (-Real.log x) ∂μ := by
      unfold alternatingNegLogMonomial
      rw [MeasureTheory.integral_const_mul]
    _ = (-1 : ℝ) ^ k *
          (∫ x : ℝ in 0..1, x ^ k * (-Real.log x)) := by
      rw [intervalIntegral.integral_of_le (μ := volume) (by norm_num)]
    _ = (-1 : ℝ) ^ k / (((k + 1 : ℕ) : ℝ) ^ 2) := by
      rw [integral_zero_one_pow_mul_neg_log]
      ring

/-- Shifted reciprocal squares, indexed from denominator one. -/
def roofShiftedInverseSquare (n : ℕ) : ℝ :=
  1 / (((n + 1 : ℕ) : ℝ) ^ 2)

/-- Alternating shifted reciprocal squares. -/
def roofAlternatingInverseSquare (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * roofShiftedInverseSquare n

theorem summable_roofShiftedInverseSquare :
    Summable roofShiftedInverseSquare := by
  exact hasSum_zeta_two.summable.comp_injective Nat.succ_injective

theorem tsum_roofShiftedInverseSquare :
    (∑' n : ℕ, roofShiftedInverseSquare n) = Real.pi ^ 2 / 6 := by
  have hsplit := hasSum_zeta_two.summable.tsum_eq_zero_add
  rw [hasSum_zeta_two.tsum_eq] at hsplit
  simpa [roofShiftedInverseSquare] using! hsplit.symm

theorem tsum_roofShiftedInverseSquare_odd :
    (∑' n : ℕ, roofShiftedInverseSquare (2 * n + 1)) =
      Real.pi ^ 2 / 24 := by
  calc
    (∑' n : ℕ, roofShiftedInverseSquare (2 * n + 1)) =
        ∑' n : ℕ, (1 / 4 : ℝ) * roofShiftedInverseSquare n := by
      apply tsum_congr
      intro n
      unfold roofShiftedInverseSquare
      push_cast
      have hn : (0 : ℝ) < n + 1 := by positivity
      have htwo : (0 : ℝ) < 2 * n + 2 := by positivity
      field_simp [ne_of_gt hn, ne_of_gt htwo]
      ring
    _ = (1 / 4 : ℝ) * ∑' n : ℕ, roofShiftedInverseSquare n := by
      rw [tsum_mul_left]
    _ = (1 / 4 : ℝ) * (Real.pi ^ 2 / 6) := by
      rw [tsum_roofShiftedInverseSquare]
    _ = Real.pi ^ 2 / 24 := by ring

theorem tsum_roofShiftedInverseSquare_even :
    (∑' n : ℕ, roofShiftedInverseSquare (2 * n)) =
      Real.pi ^ 2 / 8 := by
  have heven : Summable (fun n : ℕ ↦ roofShiftedInverseSquare (2 * n)) :=
    summable_roofShiftedInverseSquare.comp_injective
      (fun a b h ↦ by omega)
  have hodd : Summable (fun n : ℕ ↦ roofShiftedInverseSquare (2 * n + 1)) :=
    summable_roofShiftedInverseSquare.comp_injective
      (fun a b h ↦ by omega)
  have hsplit := tsum_even_add_odd heven hodd
  rw [tsum_roofShiftedInverseSquare,
    tsum_roofShiftedInverseSquare_odd] at hsplit
  linarith

theorem summable_roofAlternatingInverseSquare :
    Summable roofAlternatingInverseSquare := by
  apply Summable.of_norm
  have heq : (fun n : ℕ ↦ ‖roofAlternatingInverseSquare n‖) =
      roofShiftedInverseSquare := by
    funext n
    unfold roofAlternatingInverseSquare
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, abs_of_nonneg]
    unfold roofShiftedInverseSquare
    positivity
  rw [heq]
  exact summable_roofShiftedInverseSquare

/-- The alternating zeta value needed by the Gauss roof mean. -/
theorem tsum_roofAlternatingInverseSquare :
    (∑' n : ℕ, roofAlternatingInverseSquare n) =
      Real.pi ^ 2 / 12 := by
  have hevenBase : Summable
      (fun n : ℕ ↦ roofShiftedInverseSquare (2 * n)) :=
    summable_roofShiftedInverseSquare.comp_injective
      (fun a b h ↦ by omega)
  have hoddBase : Summable
      (fun n : ℕ ↦ roofShiftedInverseSquare (2 * n + 1)) :=
    summable_roofShiftedInverseSquare.comp_injective
      (fun a b h ↦ by omega)
  have heven : Summable
      (fun n : ℕ ↦ roofAlternatingInverseSquare (2 * n)) := by
    simpa [roofAlternatingInverseSquare] using! hevenBase
  have hodd : Summable
      (fun n : ℕ ↦ roofAlternatingInverseSquare (2 * n + 1)) := by
    apply hoddBase.neg.congr
    intro n
    unfold roofAlternatingInverseSquare
    rw [Odd.neg_one_pow (by simp : Odd (2 * n + 1))]
    simp
  have hsplit := tsum_even_add_odd heven hodd
  have hevenValue :
      (∑' n : ℕ, roofAlternatingInverseSquare (2 * n)) =
        Real.pi ^ 2 / 8 := by
    calc
      (∑' n : ℕ, roofAlternatingInverseSquare (2 * n)) =
          ∑' n : ℕ, roofShiftedInverseSquare (2 * n) := by
        apply tsum_congr
        intro n
        unfold roofAlternatingInverseSquare
        rw [Even.neg_one_pow (by simp : Even (2 * n))]
        simp
      _ = Real.pi ^ 2 / 8 := tsum_roofShiftedInverseSquare_even
  have hoddValue :
      (∑' n : ℕ, roofAlternatingInverseSquare (2 * n + 1)) =
        -(Real.pi ^ 2 / 24) := by
    calc
      (∑' n : ℕ, roofAlternatingInverseSquare (2 * n + 1)) =
          ∑' n : ℕ, -roofShiftedInverseSquare (2 * n + 1) := by
        apply tsum_congr
        intro n
        unfold roofAlternatingInverseSquare
        rw [Odd.neg_one_pow (by simp : Odd (2 * n + 1))]
        simp
      _ = -(∑' n : ℕ, roofShiftedInverseSquare (2 * n + 1)) :=
        tsum_neg
      _ = -(Real.pi ^ 2 / 24) := by
        rw [tsum_roofShiftedInverseSquare_odd]
  rw [hevenValue, hoddValue] at hsplit
  linarith

theorem integral_neg_log_div_one_add :
    (∫ x : ℝ in Ioc (0 : ℝ) 1, (-Real.log x) / (1 + x)) =
      Real.pi ^ 2 / 12 := by
  rw [integral_neg_log_div_one_add_eq_tsum]
  calc
    (∑' k : ℕ, (-1 : ℝ) ^ k / (((k + 1 : ℕ) : ℝ) ^ 2)) =
        ∑' k : ℕ, roofAlternatingInverseSquare k := by
      apply tsum_congr
      intro k
      unfold roofAlternatingInverseSquare roofShiftedInverseSquare
      ring
    _ = Real.pi ^ 2 / 12 := tsum_roofAlternatingInverseSquare

/-- The exact Lévy constant: the mean of the Gauss roof `x ↦ -log x`
under the invariant Gauss probability is `π² / (12 log 2)`.  The proof
keeps the support indicator and the Radon--Nikodym density explicit. -/
theorem gaussRoofMean_eq_pi_sq_div_log_two :
    gaussRoofMean = Real.pi ^ 2 / (12 * Real.log 2) := by
  unfold gaussRoofMean
  rw [gaussMeasure_eq_volume_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      measurable_gaussDensity
      (Eventually.of_forall (fun x ↦ by
        by_cases hx : x ∈ Ioc (0 : ℝ) 1
        · rw [gaussDensity_eq_ofReal_on_unit hx]
          exact ENNReal.ofReal_lt_top
        · simp [gaussDensity, hx]))]
  have hsupported :
      (fun x : ℝ ↦ (gaussDensity x).toReal • (-Real.log x)) =
        (Ioc (0 : ℝ) 1).indicator
          (fun x : ℝ ↦ gaussDensityReal x * (-Real.log x)) := by
    funext x
    rw [congrFun gaussDensity_toReal_eq_indicator x]
    by_cases hx : x ∈ Ioc (0 : ℝ) 1 <;>
      simp [hx, smul_eq_mul]
  rw [hsupported, integral_indicator measurableSet_Ioc]
  calc
    (∫ x : ℝ in Ioc (0 : ℝ) 1,
        gaussDensityReal x * (-Real.log x)) =
        (1 / Real.log 2) *
          ∫ x : ℝ in Ioc (0 : ℝ) 1,
            (-Real.log x) / (1 + x) := by
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      unfold gaussDensityReal
      have hlog : Real.log 2 ≠ 0 :=
        ne_of_gt (Real.log_pos (by norm_num))
      have hxden : 1 + x ≠ 0 := by linarith [hx.1]
      field_simp [hlog, hxden]
    _ = (1 / Real.log 2) * (Real.pi ^ 2 / 12) := by
      rw [integral_neg_log_div_one_add]
    _ = Real.pi ^ 2 / (12 * Real.log 2) := by
      have hlog : Real.log 2 ≠ 0 :=
        ne_of_gt (Real.log_pos (by norm_num))
      field_simp [hlog]

end

end Erdos1002
