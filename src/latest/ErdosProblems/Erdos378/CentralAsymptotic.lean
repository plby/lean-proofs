/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.CentralChebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Asymptotics for the adaptive central estimate

The finite estimate in `CentralChebyshev` is useful only after its adaptive
correlation envelope is shown to be little-oh of its interval length.  This
file verifies that fact for the deliberately generous logarithmic safety
power chosen in `AdaptiveShifts`.
-/

open Filter
open scoped Topology

namespace Erdos378
namespace CentralAsymptotic

open AdaptiveShifts
open CentralCorrelation

noncomputable section

lemma lt_baseShift_succ_pow_sixteen (M : ℕ) :
    M < (baseShift M + 1) ^ 16 := by
  let a := Nat.sqrt M
  let b := Nat.sqrt a
  let c := Nat.sqrt b
  let q := Nat.sqrt c
  have hM : M < (a + 1) ^ 2 := by
    simpa only [a, pow_two] using Nat.lt_succ_sqrt M
  have ha : a < (b + 1) ^ 2 := by
    simpa only [b, pow_two] using Nat.lt_succ_sqrt a
  have hb : b < (c + 1) ^ 2 := by
    simpa only [c, pow_two] using Nat.lt_succ_sqrt b
  have hc : c < (q + 1) ^ 2 := by
    simpa only [q, pow_two] using Nat.lt_succ_sqrt c
  have hc1 : c + 1 ≤ (q + 1) ^ 2 := by omega
  have hb4 : b < (q + 1) ^ 4 := by
    calc
      b < (c + 1) ^ 2 := hb
      _ ≤ ((q + 1) ^ 2) ^ 2 := by gcongr
      _ = (q + 1) ^ 4 := by ring
  have hb1 : b + 1 ≤ (q + 1) ^ 4 := by omega
  have ha8 : a < (q + 1) ^ 8 := by
    calc
      a < (b + 1) ^ 2 := ha
      _ ≤ ((q + 1) ^ 4) ^ 2 := by gcongr
      _ = (q + 1) ^ 8 := by ring
  have ha1 : a + 1 ≤ (q + 1) ^ 8 := by omega
  calc
    M < (a + 1) ^ 2 := hM
    _ ≤ ((q + 1) ^ 8) ^ 2 := by gcongr
    _ = (q + 1) ^ 16 := by ring
    _ = (baseShift M + 1) ^ 16 := by rfl

theorem tendsto_baseShift_atTop : Tendsto baseShift atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro B
  refine ⟨(B + 1) ^ 16, ?_⟩
  intro M hM
  by_contra hq
  have hqB : baseShift M + 1 ≤ B := by omega
  have hp := lt_baseShift_succ_pow_sixteen M
  have hpow : (baseShift M + 1) ^ 16 ≤ B ^ 16 := by gcongr
  have hstrict : B ^ 16 < (B + 1) ^ 16 := by
    exact pow_lt_pow_left₀ (by omega) (by omega) (by norm_num)
  omega

theorem tendsto_log_add_two_pow_div_id (n : ℕ) :
    Tendsto (fun x : ℝ ↦ (Real.log x + 2) ^ n / x) atTop (nhds 0) := by
  have hbase : Tendsto (fun x : ℝ ↦ Real.log x ^ n / x) atTop (nhds 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have hupper : Tendsto (fun x : ℝ ↦ (2 : ℝ) ^ n *
      (Real.log x ^ n / x)) atTop (nhds 0) := by
    simpa using hbase.const_mul ((2 : ℝ) ^ n)
  have hlogTop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  have hnonneg : ∀ᶠ x : ℝ in atTop,
      0 ≤ (Real.log x + 2) ^ n / x := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (pow_nonneg (by
      have := Real.log_nonneg hx
      linarith) n) (by positivity)
  have hbound : ∀ᶠ x : ℝ in atTop,
      (Real.log x + 2) ^ n / x ≤
        (2 : ℝ) ^ n * (Real.log x ^ n / x) := by
    filter_upwards [hlogTop.eventually (eventually_ge_atTop 2),
      eventually_ge_atTop (1 : ℝ)] with x hlog hx
    have hsum : Real.log x + 2 ≤ 2 * Real.log x := by linarith
    have hpow : (Real.log x + 2) ^ n ≤ (2 * Real.log x) ^ n := by
      gcongr
    calc
      _ ≤ (2 * Real.log x) ^ n / x :=
        div_le_div_of_nonneg_right hpow (by positivity)
      _ = (2 : ℝ) ^ n * (Real.log x ^ n / x) := by ring
  exact squeeze_zero' hnonneg hbound hupper

theorem tendsto_logarithmicSafety_atTop :
    Tendsto (fun M : ℕ ↦ logarithmicSafety M) atTop atTop := by
  unfold logarithmicSafety
  have hlog : Tendsto (fun M : ℕ ↦ Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hplus : Tendsto (fun M : ℕ ↦ Real.log (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 hlog
  exact tendsto_atTop_mono' atTop
    ((hplus.eventually_ge_atTop 1).mono fun M hM ↦
      le_self_pow₀ hM (by norm_num : 100 ≠ 0)) hplus

theorem tendsto_safety_pow_forty_div_baseShift :
    Tendsto (fun M : ℕ ↦
      logarithmicSafety M ^ 64 / (baseShift M : ℝ)) atTop (nhds 0) := by
  let q : ℕ → ℕ := baseShift
  let t : ℕ → ℕ := fun M ↦ q M + 1
  have hqTop : Tendsto q atTop atTop := tendsto_baseShift_atTop
  have htTop : Tendsto t atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hqTop
  have hmodelR := tendsto_log_add_two_pow_div_id (100 * 64)
  have hmodel : Tendsto (fun M : ℕ ↦
      (Real.log (t M : ℝ) + 2) ^ (100 * 64) / (t M : ℝ)) atTop (nhds 0) :=
    hmodelR.comp (tendsto_natCast_atTop_atTop.comp htTop)
  have hE : Tendsto (fun M : ℕ ↦
      (2 * 16 ^ (100 * 64) : ℝ) *
        ((Real.log (t M : ℝ) + 2) ^ (100 * 64) / (t M : ℝ)))
      atTop (nhds 0) := by
    simpa using hmodel.const_mul (2 * 16 ^ (100 * 64) : ℝ)
  have hqpos : ∀ᶠ M : ℕ in atTop, 1 ≤ q M :=
    hqTop.eventually (eventually_ge_atTop 1)
  have hMpos : ∀ᶠ M : ℕ in atTop, 1 ≤ M := eventually_ge_atTop 1
  have hnonneg : ∀ᶠ M : ℕ in atTop,
      0 ≤ logarithmicSafety M ^ 64 / (q M : ℝ) := by
    filter_upwards [hqpos, hMpos] with M hq hM
    exact div_nonneg (pow_nonneg (logarithmicSafety_pos hM).le 64) (by positivity)
  have hbound : ∀ᶠ M : ℕ in atTop,
      logarithmicSafety M ^ 64 / (q M : ℝ) ≤
        (2 * 16 ^ (100 * 64) : ℝ) *
          ((Real.log (t M : ℝ) + 2) ^ (100 * 64) / (t M : ℝ)) := by
    filter_upwards [hqpos, hMpos] with M hq hM
    have hMlt := lt_baseShift_succ_pow_sixteen M
    have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
    have htpos : (0 : ℝ) < t M := by positivity
    have hlogM : Real.log (M : ℝ) ≤ 16 * Real.log (t M : ℝ) := by
      have hcast : (M : ℝ) ≤ (((t M) ^ 16 : ℕ) : ℝ) := by
        exact_mod_cast hMlt.le
      have hlog := Real.log_le_log hMreal hcast
      rw [Nat.cast_pow, Real.log_pow] at hlog
      norm_num at hlog
      exact hlog
    have htOne : (1 : ℝ) ≤ t M := by
      exact_mod_cast (show 1 ≤ t M by dsimp only [t]; omega)
    have hlogt0 : 0 ≤ Real.log (t M : ℝ) := Real.log_nonneg htOne
    have hsafety : logarithmicSafety M ^ 64 ≤
        (16 : ℝ) ^ (100 * 64) *
          (Real.log (t M : ℝ) + 2) ^ (100 * 64) := by
      unfold logarithmicSafety
      rw [← pow_mul]
      have hadd : Real.log (M : ℝ) + 2 ≤
          16 * (Real.log (t M : ℝ) + 2) := by linarith
      calc
        (Real.log (M : ℝ) + 2) ^ (100 * 64) ≤
            (16 * (Real.log (t M : ℝ) + 2)) ^ (100 * 64) := by gcongr
        _ = (16 : ℝ) ^ (100 * 64) *
            (Real.log (t M : ℝ) + 2) ^ (100 * 64) := by
          rw [mul_pow]
    have htq : (t M : ℝ) / (q M : ℝ) ≤ 2 := by
      dsimp only [t]
      push_cast
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < q M)]
      norm_num
      exact_mod_cast (show q M + 1 ≤ 2 * q M by omega)
    calc
      logarithmicSafety M ^ 64 / (q M : ℝ) ≤
          ((16 : ℝ) ^ (100 * 64) *
            (Real.log (t M : ℝ) + 2) ^ (100 * 64)) /
            (q M : ℝ) := div_le_div_of_nonneg_right hsafety (by positivity)
      _ = (16 : ℝ) ^ (100 * 64) *
          ((Real.log (t M : ℝ) + 2) ^ (100 * 64) / (t M : ℝ)) *
            ((t M : ℝ) / (q M : ℝ)) := by
        field_simp [show (q M : ℝ) ≠ 0 by positivity,
          show (t M : ℝ) ≠ 0 by positivity]
      _ ≤ (16 : ℝ) ^ (100 * 64) *
          ((Real.log (t M : ℝ) + 2) ^ (100 * 64) / (t M : ℝ)) * 2 := by
        gcongr
      _ = (2 * 16 ^ (100 * 64) : ℝ) *
          ((Real.log (t M : ℝ) + 2) ^ (100 * 64) / (t M : ℝ)) := by
        ac_rfl
  exact squeeze_zero' hnonneg hbound hE

theorem tendsto_adaptiveMomentEnvelope_zero :
    Tendsto adaptiveMomentEnvelope atTop (nhds 0) := by
  have hqTop : Tendsto (fun M : ℕ ↦ (baseShift M : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_baseShift_atTop
  have hinv : Tendsto (fun M : ℕ ↦ ((baseShift M : ℝ))⁻¹)
      atTop (nhds 0) := hqTop.inv_tendsto_atTop
  have hfirst : Tendsto (fun M : ℕ ↦ 32 / (baseShift M : ℝ))
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul 32
  have hsecond : Tendsto (fun M : ℕ ↦ 1 / (256 * (baseShift M : ℝ)))
      atTop (nhds 0) := by
    convert hinv.const_mul (1 / 256 : ℝ) using 1
    · funext M
      field_simp
    · ring_nf
  have hthird : Tendsto (fun M : ℕ ↦
      terminalSafetyConstant * logarithmicSafety M ^ 64 /
        (32 * (baseShift M : ℝ))) atTop (nhds 0) := by
    convert tendsto_safety_pow_forty_div_baseShift.const_mul
      (terminalSafetyConstant / 32) using 1
    · funext M
      ring
    · ring_nf
  unfold adaptiveMomentEnvelope
  simpa only [zero_add, mul_zero] using
    (hfirst.add hsecond |>.add hthird).const_mul
      (HigherDerivative.vdcMomentConstant 32)

theorem tendsto_adaptiveCorrelationEnvelope_div :
    Tendsto (fun M : ℕ ↦ adaptiveCorrelationEnvelope M / (M : ℝ))
      atTop (nhds 0) := by
  have hS : Tendsto (fun M : ℕ ↦ (logarithmicSafety M)⁻¹)
      atTop (nhds 0) := tendsto_logarithmicSafety_atTop.inv_tendsto_atTop
  have hfirst : Tendsto (fun M : ℕ ↦ 34 / logarithmicSafety M)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hS.const_mul 34
  have hrpow : Tendsto (fun M : ℕ ↦
      adaptiveMomentEnvelope M ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹)
      atTop (nhds 0) := by
    exact tendsto_adaptiveMomentEnvelope_zero.rpow_const_nhds_zero (by positivity)
  have hsecond : Tendsto (fun M : ℕ ↦
      8 * adaptiveMomentEnvelope M ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹)
      atTop (nhds 0) := by simpa using hrpow.const_mul 8
  have heq : (fun M : ℕ ↦
      34 / logarithmicSafety M +
        8 * adaptiveMomentEnvelope M ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹) =ᶠ[atTop]
      (fun M : ℕ ↦ adaptiveCorrelationEnvelope M / (M : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with M hM
    unfold adaptiveCorrelationEnvelope
    have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
  have hsum : Tendsto (fun M : ℕ ↦
      34 / logarithmicSafety M +
        8 * adaptiveMomentEnvelope M ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹)
      atTop (nhds 0) := by
    convert hfirst.add hsecond using 1 <;> norm_num
  exact hsum.congr' heq

theorem eventually_centralCorrelationSizeCondition :
    ∀ᶠ M : ℕ in atTop, centralCorrelationSizeCondition M := by
  have hratioR := tendsto_log_add_two_pow_div_id 3200
  have hratio : Tendsto (fun M : ℕ ↦
      (Real.log (M : ℝ) + 2) ^ 3200 / (M : ℝ)) atTop (nhds 0) :=
    hratioR.comp tendsto_natCast_atTop_atTop
  let C : ℝ := 2 * centralFrequencyConstant * ((33).factorial : ℝ)
  have hscaled : Tendsto (fun M : ℕ ↦
      C * ((Real.log (M : ℝ) + 2) ^ 3200 / (M : ℝ)))
      atTop (nhds 0) := by simpa using hratio.const_mul C
  have hle : ∀ᶠ M : ℕ in atTop,
      C * ((Real.log (M : ℝ) + 2) ^ 3200 / (M : ℝ)) ≤ 1 :=
    hscaled.eventually (Iic_mem_nhds (by norm_num))
  filter_upwards [hle, eventually_gt_atTop 0] with M hle hM
  unfold centralCorrelationSizeCondition logarithmicSafety
  rw [← pow_mul]
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hdiv :
      (C * (Real.log (M : ℝ) + 2) ^ (100 * 32)) / (M : ℝ) ≤ 1 := by
    calc
      _ = C * ((Real.log (M : ℝ) + 2) ^ (100 * 32) / (M : ℝ)) :=
        mul_div_assoc C _ _
      _ = C * ((Real.log (M : ℝ) + 2) ^ 3200 / (M : ℝ)) := by norm_num
      _ ≤ 1 := hle
  have hmul := (div_le_iff₀ hMR).mp hdiv
  simpa only [C, one_mul] using hmul

theorem eventually_adaptiveCorrelationEnvelope_le_mul {delta : ℝ}
    (hdelta : 0 < delta) :
    ∀ᶠ M : ℕ in atTop,
      adaptiveCorrelationEnvelope M ≤ delta * M := by
  have hle := tendsto_adaptiveCorrelationEnvelope_div.eventually
    (Iic_mem_nhds hdelta)
  filter_upwards [hle, eventually_gt_atTop 0] with M hM hMpos
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  exact (div_le_iff₀ hMR).mp hM

end

end CentralAsymptotic
end Erdos378
