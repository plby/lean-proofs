/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.InverseSquareChebyshevLimit

/-!
# Uniform application of the inverse-square Chebyshev estimate
-/

open Filter
open scoped Topology

namespace Erdos378
namespace InverseSquareChebyshevApplication

open AdaptiveShifts
open CentralAsymptotic
open PrimeReciprocal
open ReciprocalChebyshevAsymptotic
open InverseSquareCorrelation
open InverseSquareAdaptiveShifts
open InverseSquareCentralCorrelation
open InverseSquareHybridAsymptotic
open InverseSquareProductInterval
open InverseSquareChebyshev
open InverseSquareChebyshevAsymptotic
open InverseSquareChebyshevRate
open InverseSquareChebyshevLimit

noncomputable section

lemma baseShift_le_natSqrt (y : ℕ) : baseShift y ≤ Nat.sqrt y := by
  unfold baseShift
  exact (Nat.sqrt_le_self _).trans
    ((Nat.sqrt_le_self _).trans (Nat.sqrt_le_self _))

lemma uniformScale_le_reciprocalDifferencingLength (y : ℕ) :
    inverseSquareUniformScale y ≤ reciprocalDifferencingLength y := by
  have hcastSqrt : (Nat.sqrt y : ℝ) ≤ Real.sqrt (y : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast (show Nat.sqrt y ^ 2 ≤ y by
      simpa [pow_two] using Nat.sqrt_le y)
  have hupper := (reciprocalDifferencingLength_real_bounds
    (show 1 ≤ max y 1 by omega)).1
  have hupper' : Real.sqrt (y : ℝ) <
      (reciprocalDifferencingLength y : ℝ) := by
    by_cases hy : y = 0
    · simp [hy, reciprocalDifferencingLength]
    · simpa only [max_eq_left (show 1 ≤ y by omega)] using hupper
  have hnat : Nat.sqrt y < reciprocalDifferencingLength y := by
    exact_mod_cast hcastSqrt.trans_lt hupper'
  unfold inverseSquareUniformScale
  calc
    baseShift y + 1 ≤ Nat.sqrt y + 1 :=
      Nat.add_le_add_right (baseShift_le_natSqrt y) 1
    _ ≤ reciprocalDifferencingLength y := by omega

theorem eventually_inverseSquare_basic_parameters :
    ∀ᶠ y : ℕ in atTop,
      2 * reciprocalVaughanCutoff y ^ 4 ≤ y ∧
      2 * reciprocalVaughanCutoff y ^ 2 * inverseSquareUniformScale y ≤ y ∧
      8 * inverseSquareUniformScale y ^ 2 ≤ y := by
  have hrecip := eventually_reciprocal_parameters_size
  have hbaseLarge : ∀ᶠ y : ℕ in atTop, 2 ≤ baseShift y :=
    CentralAsymptotic.tendsto_baseShift_atTop.eventually (eventually_ge_atTop 2)
  filter_upwards [hrecip, hbaseLarge, eventually_ge_atTop 2] with y hrecip hb hy
  let T := reciprocalVaughanCutoff y
  let L := reciprocalDifferencingLength y
  let Z := inverseSquareUniformScale y
  have hT : 1 ≤ T := reciprocalVaughanCutoff_pos y
  have hL : 1 ≤ L := reciprocalDifferencingLength_pos y
  have hZL : Z ≤ L := uniformScale_le_reciprocalDifferencingLength y
  have hTpow : T ^ 2 ≤ T ^ 4 := by
    have : 1 ≤ T ^ 2 := one_le_pow₀ hT
    nlinarith
  have hcore : 16 * L * T ^ 4 ≤ y / 2 := by
    change 16 * L * ((T ^ 2) ^ 2) ≤ y / 2 at hrecip
    simpa only [← pow_mul] using hrecip
  have hfirst : 2 * T ^ 4 ≤ y := by
    calc
      2 * T ^ 4 ≤ 16 * L * T ^ 4 := by nlinarith
      _ ≤ y / 2 := hcore
      _ ≤ y := Nat.div_le_self _ _
  have hsecond : 2 * T ^ 2 * Z ≤ y := by
    calc
      2 * T ^ 2 * Z ≤ 2 * T ^ 4 * L :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hTpow) hZL
      _ ≤ 16 * L * T ^ 4 := by
        rw [show 2 * T ^ 4 * L = 2 * (L * T ^ 4) by ring,
          show 16 * L * T ^ 4 = 16 * (L * T ^ 4) by ring]
        exact Nat.mul_le_mul_right _ (by omega)
      _ ≤ y / 2 := hcore
      _ ≤ y := Nat.div_le_self _ _
  have hqpow : (baseShift y) ^ 16 ≤ y := baseShift_pow_sixteen_le y
  have hZtwo : Z ≤ 2 * baseShift y := by
    dsimp only [Z, inverseSquareUniformScale]
    omega
  have hthird : 8 * Z ^ 2 ≤ y := by
    calc
      8 * Z ^ 2 ≤ 32 * (baseShift y) ^ 2 := by nlinarith
      _ ≤ (baseShift y) ^ 16 := by
        have hpow : 32 ≤ (baseShift y) ^ 14 := by
          calc
            32 ≤ 2 ^ 14 := by norm_num
            _ ≤ (baseShift y) ^ 14 := Nat.pow_le_pow_left hb 14
        nlinarith
      _ ≤ y := hqpow
  exact ⟨hfirst, hsecond, hthird⟩

theorem eventually_correlationCap_sq_le_uniformScale :
    ∀ᶠ y : ℕ in atTop,
      inverseSquareCorrelationCap y ^ 2 ≤ inverseSquareUniformScale y := by
  have hsafety := eventually_logarithmicSafety_pow_le_rpow 20
    (show (0 : ℝ) < 1 / 1024 by norm_num)
  have hgrowth : Tendsto (fun y : ℕ ↦ (y : ℝ) ^ (1 / 1024 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 1024)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfour : ∀ᶠ y : ℕ in atTop, (4 : ℝ) ≤ (y : ℝ) ^ (1 / 1024 : ℝ) :=
    hgrowth (eventually_ge_atTop 4)
  filter_upwards [eventually_ge_atTop 4, hsafety, hfour,
    eventually_rpow_le_uniformBase] with y hy hs hfourY hbase
  have hcap := inverseSquareCorrelationCap_le_safety hy
  have hS : 0 ≤ logarithmicSafety y := (logarithmicSafety_pos (by omega)).le
  have hcapSq : (inverseSquareCorrelationCap y : ℝ) ^ 2 ≤
      4 * logarithmicSafety y ^ 20 := by
    calc
      _ ≤ (2 * logarithmicSafety y ^ 10) ^ 2 := by gcongr
      _ = 4 * logarithmicSafety y ^ 20 := by ring
  have hreal : (inverseSquareCorrelationCap y : ℝ) ^ 2 ≤
      (inverseSquareUniformScale y : ℝ) := by
    calc
      _ ≤ 4 * logarithmicSafety y ^ 20 := hcapSq
      _ ≤ (y : ℝ) ^ (1 / 1024 : ℝ) *
          (y : ℝ) ^ (1 / 1024 : ℝ) := by
        exact mul_le_mul hfourY hs (pow_nonneg hS 20)
          (Real.rpow_nonneg (by positivity) _)
      _ = (y : ℝ) ^ (1 / 512 : ℝ) := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < y)]
        congr 2
        ring
      _ ≤ (baseShift (inverseSquareUniformScale y) : ℝ) := hbase
      _ ≤ (inverseSquareUniformScale y : ℝ) := by
        exact_mod_cast baseShift_le (inverseSquareUniformScale y)
  exact_mod_cast hreal

lemma baseShift_le_div_of_sq_le {M C : ℕ} (hC : 0 < C) (hCM : C ^ 2 ≤ M) :
    baseShift M ≤ M / C := by
  apply (Nat.le_div_iff_mul_le hC).2
  have hq := InverseSquareHybridAsymptotic.baseShift_sq_le M
  have hCsqrt : C ≤ Nat.sqrt M := Nat.le_sqrt.mpr (by
    simpa only [pow_two] using hCM)
  have hqsqrt : baseShift M ≤ Nat.sqrt M := Nat.le_sqrt.mpr (by
    simpa only [pow_two] using hq)
  calc
    baseShift M * C ≤ Nat.sqrt M * Nat.sqrt M :=
      Nat.mul_le_mul hqsqrt hCsqrt
    _ ≤ M := Nat.sqrt_le M

theorem eventually_inverseSquareChebyshev_bound :
    ∀ᶠ y : ℕ in atTop, ∀ {x : ℕ} {X : ℝ},
      x < y → y ≤ 2 * x → 0 < X →
      (y : ℝ) ^ 2 ≤ 4 * X → X ≤ (y : ℝ) ^ 16 →
      (inverseSquareCorrelationCap y : ℝ) ^ 2 * (y : ℝ) ^ 2 ≤ X →
      ‖weightedChebyshevInterval (inverseSquareWeight X) x y‖ ≤
        inverseSquareChebyshevMajorant y (reciprocalVaughanCutoff y)
          (inverseSquareCorrelationCap y) (inverseSquareTypeBound y)
          (inverseSquareAsymptoticDelta y) := by
  have hsizeEvent := eventually_inverseSquareCorrelationSizeCondition
  rcases hsizeEvent.exists_forall_of_atTop with ⟨M₀, hM₀⟩
  have hZlarge : ∀ᶠ y : ℕ in atTop, M₀ ≤ inverseSquareUniformScale y :=
    tendsto_inverseSquareUniformScale_atTop.eventually (eventually_ge_atTop M₀)
  have hCtwo : ∀ᶠ y : ℕ in atTop, 2 ≤ inverseSquareCorrelationCap y :=
    tendsto_inverseSquareCorrelationCap_atTop.eventually (eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop 4, eventually_inverseSquare_basic_parameters,
    eventually_correlationCap_sq_le_uniformScale, hZlarge, hCtwo] with
      y hy hbasic hCZ hZlargeY hCtwoY
  intro x X hxy hyx hX hXlo hXhi hXratio
  let T := reciprocalVaughanCutoff y
  let C := inverseSquareCorrelationCap y
  let Z := inverseSquareUniformScale y
  let delta := inverseSquareAsymptoticDelta y
  let B := inverseSquareTypeBound y
  have hT : 0 < T := reciprocalVaughanCutoff_pos y
  have hC : 2 ≤ C := by simpa only [C] using hCtwoY
  have hZ : 1 ≤ Z := by dsimp only [Z, inverseSquareUniformScale]; omega
  have hdelta : 0 ≤ delta := by
    simpa only [delta] using inverseSquareAsymptoticDelta_nonneg y
  have hB : 0 ≤ B := by simpa only [B] using inverseSquareTypeBound_nonneg y
  have hTy : T ≤ y := by
    have hTone : T ≤ T ^ 4 := by
      have : 1 ≤ T := hT
      nlinarith [show 1 ≤ T ^ 2 by exact one_le_pow₀ this]
    exact hTone.trans ((show T ^ 4 ≤ 2 * T ^ 4 by omega).trans hbasic.1)
  have hTx : T ^ 4 ≤ x := by
    have htwo : 2 * T ^ 4 ≤ 2 * x := hbasic.1.trans hyx
    omega
  have hsmallM : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      Z ≤ x / q + 1 ∧ x / q + 1 ≤ y := by
    intro q hq hqT
    have hcore : T ^ 2 * Z ≤ x := by
      have htwo : 2 * (T ^ 2 * Z) ≤ 2 * x := by
        simpa [mul_assoc] using hbasic.2.1.trans hyx
      omega
    have hqZ : q * Z ≤ x := (Nat.mul_le_mul_right Z hqT).trans hcore
    have hZdiv : Z ≤ x / q := (Nat.le_div_iff_mul_le (by omega)).2 (by
      simpa [Nat.mul_comm] using hqZ)
    exact ⟨hZdiv.trans (Nat.le_add_right _ _), by
      have := Nat.div_le_self x q
      omega⟩
  have hsmallSize : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      inverseSquareCorrelationSizeCondition (x / q + 1) := by
    intro q hq hqT
    have hM := (hsmallM q hq hqT).1
    exact hM₀ _ (hZlargeY.trans hM)
  have hsmallCap : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      baseShift (x / q + 1) ≤ (x / q + 1) / C := by
    intro q hq hqT
    have hM := (hsmallM q hq hqT).1
    exact baseShift_le_div_of_sq_le (by omega) (hCZ.trans hM)
  have hsmallEnvelope : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      ∀ Q : ℝ, 0 < Q → ((x / q + 1 : ℕ) : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * ((x / q + 1 : ℕ) : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q (x / q + 1) C ≤
        delta * (x / q + 1 : ℕ) := by
    intro q hq hqT Q hQ hQlo hQhi
    have hM := hsmallM q hq hqT
    apply cappedInverseSquareCorrelationEnvelope_le_uniform hQ hZ hM.1 hM.2 hC
      (hsmallSize q hq hqT) (hsmallCap q hq hqT) hQlo hQhi
  have hsmallB : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      inverseSquareOneDimensionalBound (x / q + 1) C delta ≤ B := by
    intro q hq hqT
    have hM := (hsmallM q hq hqT).2
    unfold inverseSquareOneDimensionalBound
    dsimp only [B, inverseSquareTypeBound, C, delta]
    gcongr
  have hlargeM : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y → Z ≤ L ∧ L ≤ y := by
    intro L hxL hLy
    have hfour : 4 * Z ^ 2 ≤ x := by
      have htwo : 8 * Z ^ 2 ≤ 2 * x := hbasic.2.2.trans hyx
      omega
    have hsq : Z ^ 2 < L ^ 2 := by nlinarith
    have hZL : Z ≤ L := by nlinarith
    exact ⟨hZL, hLy⟩
  have hlargeSize : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      inverseSquareCentralCorrelationSizeCondition L := by
    intro L hxL hLy
    have hM := (hlargeM L hxL hLy).1
    exact hM₀ _ (hZlargeY.trans hM)
  have hlargeCap : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      baseShift L ≤ L / C := by
    intro L hxL hLy
    exact baseShift_le_div_of_sq_le (by omega)
      (hCZ.trans (hlargeM L hxL hLy).1)
  have hlargeEnvelope : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      ∀ Q : ℝ, 0 < Q → (L : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * (L : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q L C ≤ delta * L := by
    intro L hxL hLy Q hQ hQlo hQhi
    have hM := hlargeM L hxL hLy
    apply cappedInverseSquareCorrelationEnvelope_le_uniform hQ hZ hM.1 hM.2 hC
      (hlargeSize L hxL hLy) (hlargeCap L hxL hLy) hQlo hQhi
  apply norm_weightedChebyshevInterval_inverseSquare_le hX hT (by omega) hdelta
    hTy hTx hxy hXlo hyx hXhi hXratio hC hB
    hsmallSize hsmallCap hsmallEnvelope hsmallB
    hlargeSize hlargeCap hlargeEnvelope

theorem tendsto_uniform_inverseSquareChebyshev_bound_div_zero :
    Tendsto (fun y : ℕ ↦
      inverseSquareChebyshevMajorant y (reciprocalVaughanCutoff y)
        (inverseSquareCorrelationCap y) (inverseSquareTypeBound y)
        (inverseSquareAsymptoticDelta y) / (y : ℝ)) atTop (nhds 0) :=
  tendsto_inverseSquareChebyshevMajorant_div_zero

end

end InverseSquareChebyshevApplication
end Erdos378
