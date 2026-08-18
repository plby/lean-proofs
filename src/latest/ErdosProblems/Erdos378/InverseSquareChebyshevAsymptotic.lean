/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.InverseSquareChebyshev
import ErdosProblems.Erdos378.ReciprocalChebyshevAsymptotic

/-!
# Uniform asymptotics for inverse-square Chebyshev sums

The application has an ambient inverse-square frequency which is a fixed
positive power larger than the prime scale.  The Vaughan cutoff is
polylogarithmic, the correlation cap is a much larger polylogarithm, and the
separation length is the sixteenth-root scale `baseShift y`.
-/

open Filter
open scoped Topology

namespace Erdos378
namespace InverseSquareChebyshevAsymptotic

open AdaptiveShifts
open CentralAsymptotic
open InverseSquareCorrelation
open InverseSquareAdaptiveShifts
open InverseSquareHybridAsymptotic
open InverseSquareProductInterval
open InverseSquareVaughanHybrid
open InverseSquareChebyshev
open ReciprocalChebyshevAsymptotic
open BoundedGaps.Maynard

noncomputable section

noncomputable def inverseSquareCorrelationCap (y : ℕ) : ℕ :=
  Nat.floor ((Real.log (y : ℝ)) ^ 1000) + 1

lemma inverseSquareCorrelationCap_pos (y : ℕ) :
    0 < inverseSquareCorrelationCap y := by
  unfold inverseSquareCorrelationCap
  omega

lemma inverseSquareCorrelationCap_real_bounds {y : ℕ} (hy : 4 ≤ y) :
    (Real.log (y : ℝ)) ^ 1000 < (inverseSquareCorrelationCap y : ℝ) ∧
      (inverseSquareCorrelationCap y : ℝ) ≤
        2 * (Real.log (y : ℝ)) ^ 1000 := by
  have hlog := one_le_log_natCast hy
  constructor
  · simpa only [inverseSquareCorrelationCap, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one ((Real.log (y : ℝ)) ^ 1000)
  · unfold inverseSquareCorrelationCap
    push_cast
    have hfloor := Nat.floor_le (show 0 ≤ (Real.log (y : ℝ)) ^ 1000 by positivity)
    have hone : (1 : ℝ) ≤ (Real.log (y : ℝ)) ^ 1000 := one_le_pow₀ hlog
    linarith

lemma monotone_baseShift : Monotone baseShift := by
  intro a b hab
  unfold baseShift
  exact Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt
    (Nat.sqrt_le_sqrt hab)))

lemma logarithmicSafety_mono {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    logarithmicSafety a ≤ logarithmicSafety b := by
  unfold logarithmicSafety
  have hlog : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < a by omega)) (by exact_mod_cast hab)
  have hnonneg : 0 ≤ Real.log (a : ℝ) + 2 := by
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have := Real.log_nonneg haR
    linarith
  exact pow_le_pow_left₀ hnonneg (by linarith) 100

/-- Every fixed power of the logarithmic safety factor is negligible beside
the iterated-square-root scale.  `CentralAsymptotic` proves the instance
needed by the reciprocal phase; the inverse-square uniformization needs
larger, but still fixed, powers. -/
theorem tendsto_logarithmicSafety_pow_div_baseShift (A : ℕ) :
    Tendsto (fun M : ℕ ↦
      logarithmicSafety M ^ A / (baseShift M : ℝ)) atTop (nhds 0) := by
  let q : ℕ → ℕ := baseShift
  let t : ℕ → ℕ := fun M ↦ q M + 1
  have hqTop : Tendsto q atTop atTop := CentralAsymptotic.tendsto_baseShift_atTop
  have htTop : Tendsto t atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hqTop
  have hmodelR := CentralAsymptotic.tendsto_log_add_two_pow_div_id (100 * A)
  have hmodel : Tendsto (fun M : ℕ ↦
      (Real.log (t M : ℝ) + 2) ^ (100 * A) / (t M : ℝ)) atTop (nhds 0) :=
    hmodelR.comp (tendsto_natCast_atTop_atTop.comp htTop)
  have hE : Tendsto (fun M : ℕ ↦
      (2 * 16 ^ (100 * A) : ℝ) *
        ((Real.log (t M : ℝ) + 2) ^ (100 * A) / (t M : ℝ)))
      atTop (nhds 0) := by
    simpa using hmodel.const_mul (2 * 16 ^ (100 * A) : ℝ)
  have hqpos : ∀ᶠ M : ℕ in atTop, 1 ≤ q M :=
    hqTop.eventually (eventually_ge_atTop 1)
  have hMpos : ∀ᶠ M : ℕ in atTop, 1 ≤ M := eventually_ge_atTop 1
  have hnonneg : ∀ᶠ M : ℕ in atTop,
      0 ≤ logarithmicSafety M ^ A / (q M : ℝ) := by
    filter_upwards [hqpos, hMpos] with M hq hM
    exact div_nonneg (pow_nonneg (logarithmicSafety_pos hM).le A) (by positivity)
  have hbound : ∀ᶠ M : ℕ in atTop,
      logarithmicSafety M ^ A / (q M : ℝ) ≤
        (2 * 16 ^ (100 * A) : ℝ) *
          ((Real.log (t M : ℝ) + 2) ^ (100 * A) / (t M : ℝ)) := by
    filter_upwards [hqpos, hMpos] with M hq hM
    have hMlt := CentralAsymptotic.lt_baseShift_succ_pow_sixteen M
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
    have hsafety : logarithmicSafety M ^ A ≤
        (16 : ℝ) ^ (100 * A) *
          (Real.log (t M : ℝ) + 2) ^ (100 * A) := by
      unfold logarithmicSafety
      rw [← pow_mul]
      have hadd : Real.log (M : ℝ) + 2 ≤
          16 * (Real.log (t M : ℝ) + 2) := by linarith
      calc
        (Real.log (M : ℝ) + 2) ^ (100 * A) ≤
            (16 * (Real.log (t M : ℝ) + 2)) ^ (100 * A) := by gcongr
        _ = (16 : ℝ) ^ (100 * A) *
            (Real.log (t M : ℝ) + 2) ^ (100 * A) := by rw [mul_pow]
    have htq : (t M : ℝ) / (q M : ℝ) ≤ 2 := by
      dsimp only [t]
      push_cast
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < q M)]
      norm_num
      exact_mod_cast (show q M + 1 ≤ 2 * q M by omega)
    calc
      logarithmicSafety M ^ A / (q M : ℝ) ≤
          ((16 : ℝ) ^ (100 * A) *
            (Real.log (t M : ℝ) + 2) ^ (100 * A)) /
            (q M : ℝ) := div_le_div_of_nonneg_right hsafety (by positivity)
      _ = (16 : ℝ) ^ (100 * A) *
          ((Real.log (t M : ℝ) + 2) ^ (100 * A) / (t M : ℝ)) *
            ((t M : ℝ) / (q M : ℝ)) := by
        field_simp [show (q M : ℝ) ≠ 0 by positivity,
          show (t M : ℝ) ≠ 0 by positivity]
      _ ≤ (16 : ℝ) ^ (100 * A) *
          ((Real.log (t M : ℝ) + 2) ^ (100 * A) / (t M : ℝ)) * 2 := by
        gcongr
      _ = (2 * 16 ^ (100 * A) : ℝ) *
          ((Real.log (t M : ℝ) + 2) ^ (100 * A) / (t M : ℝ)) := by
        ac_rfl
  exact squeeze_zero' hnonneg hbound hE

def inverseSquareUniformScale (y : ℕ) : ℕ := baseShift y + 1

theorem tendsto_inverseSquareUniformScale_atTop :
    Tendsto inverseSquareUniformScale atTop atTop := by
  unfold inverseSquareUniformScale
  exact (tendsto_add_atTop_nat 1).comp CentralAsymptotic.tendsto_baseShift_atTop

theorem tendsto_inverseSquareCorrelationCap_atTop :
    Tendsto inverseSquareCorrelationCap atTop atTop := by
  have hlog : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpow : Tendsto (fun y : ℕ ↦ (Real.log (y : ℝ)) ^ 1000)
      atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by norm_num : 1000 ≠ 0)).comp hlog
  rw [tendsto_atTop_atTop]
  intro B
  have hlarge : ∀ᶠ y : ℕ in atTop, (B : ℝ) ≤ Real.log (y : ℝ) ^ 1000 :=
    hpow (eventually_ge_atTop (B : ℝ))
  have hevent : ∀ᶠ y : ℕ in atTop, B ≤ inverseSquareCorrelationCap y := by
    filter_upwards [eventually_ge_atTop 4, hlarge] with y hy4 hy
    have hlt := (inverseSquareCorrelationCap_real_bounds (y := y) hy4).1
    exact_mod_cast (show (B : ℝ) < inverseSquareCorrelationCap y from
      hy.trans_lt hlt).le
  exact hevent.exists_forall_of_atTop

lemma logarithmicSafety_le_uniformScale {y : ℕ} (hy : 1 ≤ y) :
    logarithmicSafety y ≤
      (16 : ℝ) ^ 100 * logarithmicSafety (inverseSquareUniformScale y) := by
  let Z := inverseSquareUniformScale y
  have hyZ := CentralAsymptotic.lt_baseShift_succ_pow_sixteen y
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hZR : (0 : ℝ) < Z := by dsimp only [Z, inverseSquareUniformScale]; positivity
  have hcast : (y : ℝ) ≤ ((Z ^ 16 : ℕ) : ℝ) := by
    exact_mod_cast hyZ.le
  have hlog : Real.log (y : ℝ) ≤ 16 * Real.log (Z : ℝ) := by
    have := Real.log_le_log hyR hcast
    rw [Nat.cast_pow, Real.log_pow] at this
    norm_num at this
    exact this
  have hlogZ0 : 0 ≤ Real.log (Z : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ Z by
      dsimp only [Z, inverseSquareUniformScale]; omega))
  unfold logarithmicSafety
  have hadd : Real.log (y : ℝ) + 2 ≤
      16 * (Real.log (Z : ℝ) + 2) := by linarith
  calc
    (Real.log (y : ℝ) + 2) ^ 100 ≤
        (16 * (Real.log (Z : ℝ) + 2)) ^ 100 := by gcongr
    _ = (16 : ℝ) ^ 100 * (Real.log (Z : ℝ) + 2) ^ 100 := by rw [mul_pow]

lemma inverseSquareCorrelationCap_le_safety {y : ℕ} (hy : 4 ≤ y) :
    (inverseSquareCorrelationCap y : ℝ) ≤
      2 * logarithmicSafety y ^ 10 := by
  have hcap := (inverseSquareCorrelationCap_real_bounds hy).2
  have hlog0 : 0 ≤ Real.log (y : ℝ) := Real.log_natCast_nonneg y
  have hadd : Real.log (y : ℝ) ≤ Real.log (y : ℝ) + 2 := by linarith
  have hp : Real.log (y : ℝ) ^ 1000 ≤
      (Real.log (y : ℝ) + 2) ^ 1000 := by gcongr
  calc
    _ ≤ 2 * Real.log (y : ℝ) ^ 1000 := hcap
    _ ≤ 2 * (Real.log (y : ℝ) + 2) ^ 1000 := by gcongr
    _ = 2 * logarithmicSafety y ^ 10 := by
      unfold logarithmicSafety
      rw [← pow_mul]

lemma inverseSquareCorrelationCap_pow_mul_safety_le {y : ℕ} (hy : 4 ≤ y) :
    (inverseSquareCorrelationCap y : ℝ) ^ 33 * logarithmicSafety y ^ 32 ≤
      (2 : ℝ) ^ 33 * logarithmicSafety y ^ 362 := by
  have hS : 0 ≤ logarithmicSafety y := (logarithmicSafety_pos (by omega)).le
  have hcap := inverseSquareCorrelationCap_le_safety hy
  calc
    _ ≤ (2 * logarithmicSafety y ^ 10) ^ 33 * logarithmicSafety y ^ 32 := by
      gcongr
    _ = (2 : ℝ) ^ 33 * logarithmicSafety y ^ 362 := by ring

/-- A single moment bound which dominates every dyadic scale between `Z` and
`y`.  It is deliberately redundant so that all later uses are monotone. -/
def inverseSquareUniformMoment (y Z C : ℕ) : ℝ :=
  HigherDerivative.vdcMomentConstant 32 *
    (32 / (baseShift Z : ℝ) + 1 / (256 * (baseShift Z : ℝ)) +
      inverseSquareTerminalConstant * logarithmicSafety y ^ 64 /
          (32 * (baseShift Z : ℝ)) +
        (12 * 2 ^ 35 * (2 * (C : ℝ)) ^ 33) *
          (logarithmicSafety y ^ 32 / (Z : ℝ)))

private def uniformSafetyFactor : ℝ := (16 : ℝ) ^ 100

private def uniformActiveFactor : ℝ :=
  12 * (2 : ℝ) ^ 68 * (2 : ℝ) ^ 33

private theorem tendsto_uniform_base_inv_zero :
    Tendsto (fun y : ℕ ↦
      ((baseShift (inverseSquareUniformScale y) : ℝ))⁻¹)
      atTop (nhds 0) := by
  have hnat : Tendsto (fun y : ℕ ↦ baseShift (inverseSquareUniformScale y))
      atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro B
    rcases (tendsto_atTop_atTop.mp
      CentralAsymptotic.tendsto_baseShift_atTop B) with ⟨A, hA⟩
    rcases (tendsto_atTop_atTop.mp
      tendsto_inverseSquareUniformScale_atTop A) with ⟨Y, hY⟩
    exact ⟨Y, fun y hy ↦ hA _ (hY _ hy)⟩
  have hbTop : Tendsto (fun y : ℕ ↦
      (baseShift (inverseSquareUniformScale y) : ℝ)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro B
    obtain ⟨b, hb⟩ := exists_nat_ge B
    rcases (tendsto_atTop_atTop.mp hnat b) with ⟨Y, hY⟩
    refine ⟨Y, fun y hy ↦ hb.trans ?_⟩
    exact_mod_cast hY y hy
  exact hbTop.inv_tendsto_atTop

private theorem tendsto_inverseSquareUniformMoment_first_zero :
    Tendsto (fun y : ℕ ↦
      32 / (baseShift (inverseSquareUniformScale y) : ℝ))
      atTop (nhds 0) := by
  simpa only [div_eq_mul_inv, mul_zero] using
    tendsto_uniform_base_inv_zero.const_mul 32

private theorem tendsto_inverseSquareUniformMoment_second_zero :
    Tendsto (fun y : ℕ ↦
      1 / (256 * (baseShift (inverseSquareUniformScale y) : ℝ)))
      atTop (nhds 0) := by
  have h := tendsto_uniform_base_inv_zero.const_mul (1 / 256 : ℝ)
  convert h using 1
  · funext y
    simp only [one_div, mul_inv_rev]
    ring
  · ring

private theorem inverseSquare_terminal_le_of_safety
    {A B F b : ℝ} (hA : 0 ≤ A) (hsafe : A ≤ F * B) (hb : 0 ≤ b) :
    inverseSquareTerminalConstant * A ^ 64 / (32 * b) ≤
      (inverseSquareTerminalConstant * F ^ 64 / 32) * (B ^ 64 / b) := by
  have hpow : A ^ 64 ≤ F ^ 64 * B ^ 64 := by
    calc
      _ ≤ (F * B) ^ 64 := pow_le_pow_left₀ hA hsafe 64
      _ = _ := by rw [mul_pow]
  have hnum : inverseSquareTerminalConstant * A ^ 64 ≤
      inverseSquareTerminalConstant * (F ^ 64 * B ^ 64) :=
    mul_le_mul_of_nonneg_left hpow inverseSquareTerminalConstant_pos.le
  have hden : 0 ≤ 32 * b := mul_nonneg (by norm_num) hb
  calc
    _ ≤ inverseSquareTerminalConstant *
        (F ^ 64 * B ^ 64) / (32 * b) :=
      div_le_div_of_nonneg_right hnum hden
    _ = (inverseSquareTerminalConstant * F ^ 64 / 32) * (B ^ 64 / b) := by ring

private theorem tendsto_inverseSquareUniformMoment_terminal_zero :
    Tendsto (fun y : ℕ ↦
      inverseSquareTerminalConstant * logarithmicSafety y ^ 64 /
        (32 * (baseShift (inverseSquareUniformScale y) : ℝ)))
      atTop (nhds 0) := by
  let Z : ℕ → ℕ := inverseSquareUniformScale
  have hZTop : Tendsto Z atTop atTop := tendsto_inverseSquareUniformScale_atTop
  have hmodel64 : Tendsto (fun y : ℕ ↦
      logarithmicSafety (Z y) ^ 64 / (baseShift (Z y) : ℝ))
      atTop (nhds 0) :=
    (tendsto_logarithmicSafety_pow_div_baseShift 64).comp hZTop
  let K : ℝ := inverseSquareTerminalConstant * uniformSafetyFactor ^ 64 / 32
  have hthirdUpper : Tendsto (fun y : ℕ ↦
      K *
        (logarithmicSafety (Z y) ^ 64 / (baseShift (Z y) : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hmodel64.const_mul K
  have hthirdNonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ inverseSquareTerminalConstant * logarithmicSafety y ^ 64 /
        (32 * (baseShift (Z y) : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1,
      hZTop.eventually (eventually_ge_atTop 1)] with y hy hZ
    exact div_nonneg
      (mul_nonneg inverseSquareTerminalConstant_pos.le
        (pow_nonneg (logarithmicSafety_pos hy).le 64))
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hthirdBound : ∀ᶠ y : ℕ in atTop,
      inverseSquareTerminalConstant * logarithmicSafety y ^ 64 /
          (32 * (baseShift (Z y) : ℝ)) ≤
        K *
          (logarithmicSafety (Z y) ^ 64 / (baseShift (Z y) : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    have hsafe := logarithmicSafety_le_uniformScale hy
    change _ ≤ (inverseSquareTerminalConstant * uniformSafetyFactor ^ 64 / 32) * _
    exact inverseSquare_terminal_le_of_safety
      (logarithmicSafety_pos hy).le hsafe (by positivity)
  exact squeeze_zero' hthirdNonneg hthirdBound hthirdUpper

private theorem tendsto_inverseSquareUniformMoment_active_zero :
    Tendsto (fun y : ℕ ↦
      (12 * 2 ^ 35 * (2 * (inverseSquareCorrelationCap y : ℝ)) ^ 33) *
        (logarithmicSafety y ^ 32 / (inverseSquareUniformScale y : ℝ)))
      atTop (nhds 0) := by
  let Z : ℕ → ℕ := inverseSquareUniformScale
  have hmodel362 := tendsto_logarithmicSafety_pow_div_baseShift 362
  have hfourthUpper : Tendsto (fun y : ℕ ↦
      uniformActiveFactor *
        (logarithmicSafety y ^ 362 / (baseShift y : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hmodel362.const_mul uniformActiveFactor
  have hfourthNonneg : ∀ᶠ y : ℕ in atTop,
      0 ≤ (12 * 2 ^ 35 * (2 * (inverseSquareCorrelationCap y : ℝ)) ^ 33) *
        (logarithmicSafety y ^ 32 / (Z y : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by norm_num) (pow_nonneg (by norm_num) 35)
      · exact pow_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) 33
    · exact div_nonneg (pow_nonneg (logarithmicSafety_pos hy).le 32)
        (Nat.cast_nonneg _)
  have hfourthBound : ∀ᶠ y : ℕ in atTop,
      (12 * 2 ^ 35 * (2 * (inverseSquareCorrelationCap y : ℝ)) ^ 33) *
          (logarithmicSafety y ^ 32 / (Z y : ℝ)) ≤
        uniformActiveFactor *
          (logarithmicSafety y ^ 362 / (baseShift y : ℝ)) := by
    filter_upwards [eventually_ge_atTop 4,
      CentralAsymptotic.tendsto_baseShift_atTop.eventually
        (eventually_ge_atTop 1)] with y hy hb
    have hcap := inverseSquareCorrelationCap_pow_mul_safety_le hy
    have hS : 0 ≤ logarithmicSafety y := (logarithmicSafety_pos (by omega)).le
    have hbaseR : (0 : ℝ) < baseShift y := by exact_mod_cast hb
    have hZbase : (baseShift y : ℝ) ≤ Z y := by
      dsimp only [Z, inverseSquareUniformScale]
      push_cast
      linarith
    have hfrac : logarithmicSafety y ^ 362 / (Z y : ℝ) ≤
        logarithmicSafety y ^ 362 / (baseShift y : ℝ) :=
      div_le_div_of_nonneg_left (pow_nonneg hS 362) hbaseR hZbase
    calc
      _ = (12 * (2 : ℝ) ^ 68) *
          (((inverseSquareCorrelationCap y : ℝ) ^ 33 *
            logarithmicSafety y ^ 32) / (Z y : ℝ)) := by ring
      _ ≤ (12 * (2 : ℝ) ^ 68) *
          (((2 : ℝ) ^ 33 * logarithmicSafety y ^ 362) / (Z y : ℝ)) := by
        gcongr
      _ = uniformActiveFactor *
          (logarithmicSafety y ^ 362 / (Z y : ℝ)) := by
        unfold uniformActiveFactor
        ring
      _ ≤ uniformActiveFactor *
          (logarithmicSafety y ^ 362 / (baseShift y : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hfrac (by
          unfold uniformActiveFactor
          positivity)
  exact squeeze_zero' hfourthNonneg hfourthBound hfourthUpper

theorem tendsto_inverseSquareUniformMoment_zero :
    Tendsto (fun y : ℕ ↦ inverseSquareUniformMoment y
      (inverseSquareUniformScale y) (inverseSquareCorrelationCap y))
      atTop (nhds 0) := by
  have hfirst := tendsto_inverseSquareUniformMoment_first_zero
  have hsecond := tendsto_inverseSquareUniformMoment_second_zero
  have hthird := tendsto_inverseSquareUniformMoment_terminal_zero
  have hfourth := tendsto_inverseSquareUniformMoment_active_zero
  unfold inverseSquareUniformMoment
  simpa only [zero_add, mul_zero] using
    (hfirst.add hsecond |>.add hthird |>.add hfourth).const_mul
      (HigherDerivative.vdcMomentConstant 32)

def inverseSquareUniformDelta (y Z C : ℕ) : ℝ :=
  34 / (C : ℝ) + 34 / (Z : ℝ) +
    8 * (inverseSquareUniformMoment y Z C) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹

lemma inverseSquareUniformMoment_nonneg {y Z C : ℕ} (hZ : 1 ≤ Z) :
    0 ≤ inverseSquareUniformMoment y Z C := by
  unfold inverseSquareUniformMoment
  have hb : 0 < baseShift Z := baseShift_pos (Nat.zero_lt_of_lt hZ)
  have hS : 0 ≤ logarithmicSafety y := by
    unfold logarithmicSafety
    positivity [Real.log_natCast_nonneg y]
  have hT : 0 < inverseSquareTerminalConstant := inverseSquareTerminalConstant_pos
  have hV : 0 < HigherDerivative.vdcMomentConstant 32 :=
    HigherDerivative.vdcMomentConstant_pos 32
  apply mul_nonneg hV.le
  apply add_nonneg
  · apply add_nonneg
    · apply add_nonneg <;> positivity
    · exact div_nonneg (mul_nonneg hT.le (pow_nonneg hS 64)) (by positivity)
  · have hc : 0 ≤ 12 * (2 : ℝ) ^ 35 * (2 * (C : ℝ)) ^ 33 := by positivity
    exact mul_nonneg hc (div_nonneg (pow_nonneg hS 32) (by positivity))

lemma inverseSquareUniformDelta_nonneg {y Z C : ℕ}
    (hZ : 1 ≤ Z) (hC : 1 ≤ C) :
    0 ≤ inverseSquareUniformDelta y Z C := by
  unfold inverseSquareUniformDelta
  have hM : 0 ≤ inverseSquareUniformMoment y Z C :=
    inverseSquareUniformMoment_nonneg (y := y) (C := C) hZ
  positivity

theorem tendsto_inverseSquareUniformDelta_zero :
    Tendsto (fun y : ℕ ↦ inverseSquareUniformDelta y
      (inverseSquareUniformScale y) (inverseSquareCorrelationCap y))
      atTop (nhds 0) := by
  have hCinv : Tendsto (fun y : ℕ ↦
      ((inverseSquareCorrelationCap y : ℝ))⁻¹) atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop.comp
      tendsto_inverseSquareCorrelationCap_atTop).inv_tendsto_atTop
  have hfirst : Tendsto (fun y : ℕ ↦
      34 / (inverseSquareCorrelationCap y : ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hCinv.const_mul 34
  have hZinv : Tendsto (fun y : ℕ ↦
      ((inverseSquareUniformScale y : ℝ))⁻¹) atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop.comp
      tendsto_inverseSquareUniformScale_atTop).inv_tendsto_atTop
  have hsecond : Tendsto (fun y : ℕ ↦
      34 / (inverseSquareUniformScale y : ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hZinv.const_mul 34
  have hrpow : Tendsto (fun y : ℕ ↦
      (inverseSquareUniformMoment y (inverseSquareUniformScale y)
        (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹)
      atTop (nhds 0) :=
    tendsto_inverseSquareUniformMoment_zero.rpow_const_nhds_zero (by positivity)
  have hthird : Tendsto (fun y : ℕ ↦
      8 * (inverseSquareUniformMoment y (inverseSquareUniformScale y)
        (inverseSquareCorrelationCap y)) ^ ((2 ^ 32 : ℕ) : ℝ)⁻¹)
      atTop (nhds 0) := by
    simpa only [mul_zero] using hrpow.const_mul 8
  unfold inverseSquareUniformDelta
  simpa only [zero_add] using hfirst.add hsecond |>.add hthird

lemma largeFrequencyMomentBound_le_uniform
    {M y Z C : ℕ} (hZ : 1 ≤ Z) (hZM : Z ≤ M) (hMy : M ≤ y) :
    largeFrequencyMomentBound M C ≤ inverseSquareUniformMoment y Z C := by
  have hM : 1 ≤ M := hZ.trans hZM
  have hbZ : 0 < baseShift Z := baseShift_pos (Nat.zero_lt_of_lt hZ)
  have hbM : 0 < baseShift M := baseShift_pos (Nat.zero_lt_of_lt hM)
  have hb : baseShift Z ≤ baseShift M := monotone_baseShift hZM
  have hS : logarithmicSafety M ≤ logarithmicSafety y :=
    logarithmicSafety_mono hM hMy
  have hSM0 : 0 ≤ logarithmicSafety M := (logarithmicSafety_pos hM).le
  have hSY0 : 0 ≤ logarithmicSafety y :=
    (logarithmicSafety_pos (hM.trans hMy)).le
  have h₁ : 32 / (baseShift M : ℝ) ≤ 32 / (baseShift Z : ℝ) := by
    exact div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hbZ)
      (by exact_mod_cast hb)
  have h₂ : 1 / (256 * (baseShift M : ℝ)) ≤
      1 / (256 * (baseShift Z : ℝ)) := by
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by exact_mod_cast Nat.mul_le_mul_left 256 hb)
  have h₃ : inverseSquareTerminalConstant * logarithmicSafety M ^ 64 /
        (32 * (baseShift M : ℝ)) ≤
      inverseSquareTerminalConstant * logarithmicSafety y ^ 64 /
        (32 * (baseShift Z : ℝ)) := by
    have hn0 : 0 ≤ inverseSquareTerminalConstant * logarithmicSafety M ^ 64 :=
      mul_nonneg inverseSquareTerminalConstant_pos.le (pow_nonneg hSM0 64)
    have hn : inverseSquareTerminalConstant * logarithmicSafety M ^ 64 ≤
        inverseSquareTerminalConstant * logarithmicSafety y ^ 64 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hSM0 hS 64)
        inverseSquareTerminalConstant_pos.le
    have hd0 : 0 < 32 * (baseShift Z : ℝ) := by positivity
    have hd : 32 * (baseShift Z : ℝ) ≤ 32 * (baseShift M : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_left 32 hb
    calc
      _ ≤ inverseSquareTerminalConstant * logarithmicSafety M ^ 64 /
          (32 * (baseShift Z : ℝ)) :=
        div_le_div_of_nonneg_left hn0 hd0 hd
      _ ≤ _ := div_le_div_of_nonneg_right hn hd0.le
  have h₄ : (12 * 2 ^ 35 * (2 * (C : ℝ)) ^ 33) *
        (logarithmicSafety M ^ 32 / (M : ℝ)) ≤
      (12 * 2 ^ 35 * (2 * (C : ℝ)) ^ 33) *
        (logarithmicSafety y ^ 32 / (Z : ℝ)) := by
    have hcoeff : 0 ≤ 12 * 2 ^ 35 * (2 * (C : ℝ)) ^ 33 := by positivity
    apply mul_le_mul_of_nonneg_left _ hcoeff
    have hZR : (0 : ℝ) < Z := by exact_mod_cast hZ
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    calc
      logarithmicSafety M ^ 32 / (M : ℝ) ≤
          logarithmicSafety M ^ 32 / (Z : ℝ) :=
        div_le_div_of_nonneg_left (pow_nonneg hSM0 32) hZR (by exact_mod_cast hZM)
      _ ≤ _ := div_le_div_of_nonneg_right (pow_le_pow_left₀ hSM0 hS 32) hZR.le
  unfold largeFrequencyMomentBound largeFrequencyTerminalBound
  unfold inverseSquareUniformMoment
  apply mul_le_mul_of_nonneg_left _ (HigherDerivative.vdcMomentConstant_pos 32).le
  linarith

lemma cappedInverseSquareCorrelationEnvelope_le_uniform
    {Q : ℝ} (hQ : 0 < Q) {M y Z C : ℕ}
    (hZ : 1 ≤ Z) (hZM : Z ≤ M) (hMy : M ≤ y) (hC : 2 ≤ C)
    (hsize : inverseSquareCorrelationSizeCondition M)
    (hcap : baseShift M ≤ M / C)
    (hlarge : (M : ℝ) ^ 3 ≤ 4 * Q)
    (hQupper : Q ≤ inverseSquareFrequencyConstant * (M : ℝ) ^ 31) :
    cappedInverseSquareCorrelationEnvelope Q M C ≤
      inverseSquareUniformDelta y Z C * M := by
  have hM : 1 ≤ M := hZ.trans hZM
  have hbase := baseShift_inverseSquarePredicate_of_frequency_upper
    hQ.le hM hQupper hsize
  have hmoment := cappedInverseSquareMomentEnvelope_le_largeFrequencyMomentBound
    hQ hM hC hbase hcap hlarge
  have hmoment' := hmoment.trans
    (largeFrequencyMomentBound_le_uniform hZ hZM hMy)
  have hq : 1 ≤ cappedInverseSquareShift Q M C :=
    (baseShift_pos (Nat.zero_lt_of_lt hM)).trans_le
      (baseShift_le_cappedInverseSquareShift hbase hcap)
  have hmoment0 := cappedInverseSquareMomentEnvelope_nonneg hQ hq
  have hrpow := Real.rpow_le_rpow hmoment0 hmoment' (by positivity)
  have hMR : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hCR : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hZR : (0 : ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
  apply (div_le_iff₀ hMR).mp
  calc
    cappedInverseSquareCorrelationEnvelope Q M C / (M : ℝ) =
        34 * ((M / C : ℕ) : ℝ) / (M : ℝ) + 34 / (M : ℝ) +
          8 * (cappedInverseSquareMomentEnvelope Q M C) ^
            ((2 ^ 32 : ℕ) : ℝ)⁻¹ := by
      unfold cappedInverseSquareCorrelationEnvelope
      field_simp
    _ ≤ 34 / (C : ℝ) + 34 / (Z : ℝ) +
          8 * (inverseSquareUniformMoment y Z C) ^
            ((2 ^ 32 : ℕ) : ℝ)⁻¹ := by
      have hdivC : 34 * ((M / C : ℕ) : ℝ) / (M : ℝ) ≤
          34 / (C : ℝ) := by
        calc
          _ ≤ 34 * ((M : ℝ) / (C : ℝ)) / (M : ℝ) := by
            gcongr
            exact Nat.cast_div_le
          _ = _ := by field_simp
      have hdivZ : 34 / (M : ℝ) ≤ 34 / (Z : ℝ) := by
        exact div_le_div_of_nonneg_left (by norm_num) hZR (by exact_mod_cast hZM)
      gcongr
    _ = inverseSquareUniformDelta y Z C := rfl

end

end InverseSquareChebyshevAsymptotic
end Erdos378
