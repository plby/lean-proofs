/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.InverseSquareProductInterval
import ErdosProblems.Erdos378.InverseSquareVaughanHybrid
import ErdosProblems.Erdos378.VaughanReciprocalFull

/-!
# A finite Vaughan estimate for an inverse-square phase
-/

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Erdos378
namespace InverseSquareChebyshev

open BoundedGaps.Maynard
open PrimeReciprocal
open AdaptiveShifts
open InverseSquareCorrelation
open InverseSquareAdaptiveShifts
open InverseSquareCentralCorrelation
open InverseSquareProductInterval
open InverseSquareVaughanHybrid

noncomputable section

private lemma small_factor_scale
    {x T q : ℕ} (hq : 0 < q) (hqT : q ≤ T ^ 2)
    (hTx : T ^ 4 ≤ x) :
    q ≤ x ∧ q ≤ x / q + 1 := by
  have hqSq : q ^ 2 ≤ x := by
    calc
      q ^ 2 ≤ (T ^ 2) ^ 2 := by gcongr
      _ = T ^ 4 := by ring
      _ ≤ x := hTx
  have hqx : q ≤ x := by nlinarith
  have hqdiv : q ≤ x / q := by
    exact (Nat.le_div_iff_mul_le hq).2 (by simpa [pow_two] using hqSq)
  exact ⟨hqx, hqdiv.trans (Nat.le_add_right _ _)⟩

theorem weightedVaughanIntervalOne_inverseSquare_eq_zero
    {X : ℝ} {x y T : ℕ} (hTx : (T : ℝ) ≤ x) :
    weightedVaughanIntervalOne (inverseSquareWeight X) T x y = 0 := by
  unfold weightedVaughanIntervalOne
  apply Finset.sum_eq_zero
  intro n hn
  apply mul_eq_zero_of_left
  have hxn : x < n := (Finset.mem_Ioc.mp hn).1
  have hxnR : (x : ℝ) < (n : ℝ) := by exact_mod_cast hxn
  rw [arithmeticFunctionLowCutoff_apply_of_lt (hTx.trans_lt hxnR)]
  norm_num

theorem norm_weightedVaughanIntervalTwo_inverseSquare_le
    {X delta : ℝ} {x y T H C : ℕ} {B : ℝ}
    (hX : 0 < X) (hT : 0 < T) (hH : 0 < H) (hdelta : 0 ≤ delta)
    (hTy : T ≤ y) (hTx : T ^ 4 ≤ x) (hxy : x < y)
    (hyx : y ≤ 2 * x) (hXhi : X ≤ (y : ℝ) ^ 16)
    (hXratio : (H : ℝ) ^ 2 * (y : ℝ) ^ 2 ≤ X)
    (hC : 2 ≤ C) (hB0 : 0 ≤ B)
    (hsize : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      inverseSquareCorrelationSizeCondition (x / q + 1))
    (hbaseCap : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      baseShift (x / q + 1) ≤ (x / q + 1) / C)
    (hlargeEnvelope : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      ∀ Q : ℝ, 0 < Q → ((x / q + 1 : ℕ) : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * ((x / q + 1 : ℕ) : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q (x / q + 1) C ≤
        delta * (x / q + 1 : ℕ))
    (hB : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      inverseSquareOneDimensionalBound (x / q + 1) H delta ≤ B) :
    ‖weightedVaughanIntervalTwo (inverseSquareWeight X) T x y‖ ≤
      (T : ℝ) * (2 * Real.log (y : ℝ) * B) := by
  rw [weightedVaughanIntervalTwo_eq_nested]
  calc
    _ ≤ ∑ d ∈ (Finset.Icc 1 y).filter (fun d : ℕ ↦ (d : ℝ) ≤ T),
        ‖((ArithmeticFunction.moebius d : ℝ) : ℂ) *
          ∑ h ∈ Finset.Ioc (x / d) (y / d),
            (Real.log h : ℂ) * inverseSquareWeight X (d * h)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ (Finset.Icc 1 y).filter (fun d : ℕ ↦ (d : ℝ) ≤ T),
        2 * Real.log (y : ℝ) * B := by
      apply Finset.sum_le_sum
      intro d hdmem
      rcases Finset.mem_filter.mp hdmem with ⟨hdy, hdTreal⟩
      have hdpos : 0 < d := (Finset.mem_Icc.mp hdy).1
      have hdT : d ≤ T := by exact_mod_cast hdTreal
      have hdTsq : d ≤ T ^ 2 := hdT.trans (by
        have : 1 ≤ T := hT
        nlinarith)
      rcases small_factor_scale hdpos hdTsq hTx with ⟨hdx, hdscale⟩
      rw [norm_mul]
      have hmu : ‖((ArithmeticFunction.moebius d : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hinner := norm_log_weighted_inverseSquareProductInterval_le
        hX hH hdelta hdpos hdx hdscale hxy hyx hXhi hXratio
        (hsize d hdpos hdTsq) hC (hbaseCap d hdpos hdTsq)
        (hlargeEnvelope d hdpos hdTsq)
      have hlog0 : 0 ≤ Real.log (y : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hT.trans_le hTy)
      calc
        _ ≤ 1 * (2 * Real.log (y : ℝ) *
            inverseSquareOneDimensionalBound (x / d + 1) H delta) := by
          exact mul_le_mul hmu hinner (norm_nonneg _) (by positivity)
        _ ≤ 1 * (2 * Real.log (y : ℝ) * B) := by
          gcongr
          exact hB d hdpos hdTsq
        _ = _ := by ring
    _ ≤ (T : ℝ) * (2 * Real.log (y : ℝ) * B) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.Icc 1 y).filter
          (fun d : ℕ ↦ (d : ℝ) ≤ T)).card ≤ T := by
        calc
          _ ≤ (Finset.Icc 1 T).card := Finset.card_le_card (by
            intro d hd
            rcases Finset.mem_filter.mp hd with ⟨hdy, hdTreal⟩
            exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hdy).1,
              by exact_mod_cast hdTreal⟩)
          _ = T := by simp only [Nat.card_Icc]; omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (mul_nonneg (mul_nonneg (by positivity)
          (Real.log_nonneg (by exact_mod_cast hT.trans_le hTy))) hB0)

private lemma weightedVaughanIntervalThree_eq_supported
    {X : ℝ} {x y T : ℕ} (hT : 0 < T) :
    -weightedVaughanIntervalThree (inverseSquareWeight X) T T x y =
      ∑ t ∈ (Finset.Icc 1 y).filter (fun t : ℕ ↦ t ≤ T ^ 2),
        ((vaughanThirdCoefficient T T t : ℝ) : ℂ) *
          ∑ r ∈ Finset.Ioc (x / t) (y / t), inverseSquareWeight X (t * r) := by
  rw [neg_weightedVaughanIntervalThree_eq_nested (inverseSquareWeight X)
    (by exact_mod_cast hT) (by exact_mod_cast hT)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases htT : t ≤ T ^ 2
  · rw [if_pos htT]
  · rw [if_neg htT]
    apply mul_eq_zero_of_left
    have hltNat : T ^ 2 < t := Nat.lt_of_not_ge htT
    have hltR : (T : ℝ) * (T : ℝ) < (t : ℝ) := by
      exact_mod_cast (show T * T < t by simpa [pow_two] using hltNat)
    rw [vaughanThirdCoefficient_eq_zero_of_cutoffProduct_lt
      (by exact_mod_cast hT.le) (by exact_mod_cast hT.le) hltR]
    norm_num

theorem norm_weightedVaughanIntervalThree_inverseSquare_le
    {X delta : ℝ} {x y T H C : ℕ} {B : ℝ}
    (hX : 0 < X) (hT : 0 < T) (hH : 0 < H) (hdelta : 0 ≤ delta)
    (hTy : T ≤ y) (hTx : T ^ 4 ≤ x) (hxy : x < y)
    (hyx : y ≤ 2 * x) (hXhi : X ≤ (y : ℝ) ^ 16)
    (hXratio : (H : ℝ) ^ 2 * (y : ℝ) ^ 2 ≤ X)
    (hC : 2 ≤ C) (hB0 : 0 ≤ B)
    (hsize : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      inverseSquareCorrelationSizeCondition (x / q + 1))
    (hbaseCap : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      baseShift (x / q + 1) ≤ (x / q + 1) / C)
    (hlargeEnvelope : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      ∀ Q : ℝ, 0 < Q → ((x / q + 1 : ℕ) : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * ((x / q + 1 : ℕ) : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q (x / q + 1) C ≤
        delta * (x / q + 1 : ℕ))
    (hB : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      inverseSquareOneDimensionalBound (x / q + 1) H delta ≤ B) :
    ‖weightedVaughanIntervalThree (inverseSquareWeight X) T T x y‖ ≤
      ((T ^ 2 : ℕ) : ℝ) * (Real.log (y : ℝ) * B) := by
  rw [← norm_neg, weightedVaughanIntervalThree_eq_supported hT]
  calc
    _ ≤ ∑ t ∈ (Finset.Icc 1 y).filter (fun t : ℕ ↦ t ≤ T ^ 2),
        ‖((vaughanThirdCoefficient T T t : ℝ) : ℂ) *
          ∑ r ∈ Finset.Ioc (x / t) (y / t),
            inverseSquareWeight X (t * r)‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ (Finset.Icc 1 y).filter (fun t : ℕ ↦ t ≤ T ^ 2),
        Real.log (y : ℝ) * B := by
      apply Finset.sum_le_sum
      intro t htmem
      rcases Finset.mem_filter.mp htmem with ⟨hty, htT⟩
      have htpos : 0 < t := (Finset.mem_Icc.mp hty).1
      rcases small_factor_scale htpos htT hTx with ⟨htx, htscale⟩
      have hcoeff : ‖((vaughanThirdCoefficient T T t : ℝ) : ℂ)‖ ≤
          Real.log (y : ℝ) :=
        (norm_vaughanThirdCoefficient_le_log T T t).trans
          (Real.log_le_log (by exact_mod_cast htpos)
            (by exact_mod_cast (Finset.mem_Icc.mp hty).2))
      have hinner := norm_inverseSquareProductInterval_partial_le
        hX hH hdelta htpos htx htscale hxy
        (show y / t ≤ y / t from le_rfl) hyx hXhi hXratio
        (hsize t htpos htT) hC (hbaseCap t htpos htT)
        (hlargeEnvelope t htpos htT)
      have hlog0 : 0 ≤ Real.log (y : ℝ) :=
        Real.log_nonneg (by
          exact_mod_cast (htpos.trans_le (Finset.mem_Icc.mp hty).2))
      change ‖((vaughanThirdCoefficient T T t : ℝ) : ℂ) *
          inverseSquareProductIntervalSum X t (x / t) (y / t)‖ ≤ _
      rw [norm_mul]
      calc
        _ ≤ Real.log (y : ℝ) *
            inverseSquareOneDimensionalBound (x / t + 1) H delta :=
          mul_le_mul hcoeff hinner (norm_nonneg _) hlog0
        _ ≤ Real.log (y : ℝ) * B :=
          mul_le_mul_of_nonneg_left (hB t htpos htT) hlog0
    _ ≤ ((T ^ 2 : ℕ) : ℝ) * (Real.log (y : ℝ) * B) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.Icc 1 y).filter
          (fun t : ℕ ↦ t ≤ T ^ 2)).card ≤ T ^ 2 := by
        calc
          _ ≤ (Finset.Icc 1 (T ^ 2)).card := Finset.card_le_card (by
            intro t ht
            rcases Finset.mem_filter.mp ht with ⟨hty, htT⟩
            exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hty).1, htT⟩)
          _ = T ^ 2 := by simp only [Nat.card_Icc]; omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (mul_nonneg (Real.log_nonneg (by exact_mod_cast hT.trans_le hTy)) hB0)

def inverseSquareChebyshevMajorant
    (y T H : ℕ) (B delta : ℝ) : ℝ :=
  (T : ℝ) * (2 * Real.log (y : ℝ) * B) +
    ((T ^ 2 : ℕ) : ℝ) * (Real.log (y : ℝ) * B) +
      ((dyadicExponentRange y).card : ℝ) ^ 2 *
        Real.sqrt (inverseSquareFourthUniformMajorant y T H delta)

/-- All four exact Vaughan terms combined. -/
theorem norm_weightedChebyshevInterval_inverseSquare_le
    {X delta : ℝ} {x y T H C : ℕ} {B : ℝ}
    (hX : 0 < X) (hT : 0 < T) (hH : 0 < H) (hdelta : 0 ≤ delta)
    (hTy : T ≤ y) (hTx : T ^ 4 ≤ x) (hxy : x < y)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hyx : y ≤ 2 * x) (hXhi : X ≤ (y : ℝ) ^ 16)
    (hXratio : (H : ℝ) ^ 2 * (y : ℝ) ^ 2 ≤ X)
    (hC : 2 ≤ C) (hB0 : 0 ≤ B)
    (hsmallSize : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      inverseSquareCorrelationSizeCondition (x / q + 1))
    (hsmallCap : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      baseShift (x / q + 1) ≤ (x / q + 1) / C)
    (hsmallEnvelope : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      ∀ Q : ℝ, 0 < Q → ((x / q + 1 : ℕ) : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * ((x / q + 1 : ℕ) : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q (x / q + 1) C ≤
        delta * (x / q + 1 : ℕ))
    (hsmallB : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      inverseSquareOneDimensionalBound (x / q + 1) H delta ≤ B)
    (hlargeSize : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      inverseSquareCentralCorrelationSizeCondition L)
    (hlargeCap : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y → baseShift L ≤ L / C)
    (hlargeEnvelope : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      ∀ Q : ℝ, 0 < Q → (L : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * (L : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q L C ≤ delta * L) :
    ‖weightedChebyshevInterval (inverseSquareWeight X) x y‖ ≤
      inverseSquareChebyshevMajorant y T H B delta := by
  have hTone : 1 ≤ T := hT
  have hTfour : T ≤ T ^ 4 := by nlinarith [pow_pos hT 2, pow_pos hT 3]
  have hTlex : T ≤ x := hTfour.trans hTx
  rw [weightedChebyshevInterval_eq_vaughan,
    weightedVaughanIntervalOne_inverseSquare_eq_zero (by exact_mod_cast hTlex),
    zero_add]
  have hTwo := norm_weightedVaughanIntervalTwo_inverseSquare_le
    hX hT hH hdelta hTy hTx hxy hyx hXhi hXratio hC hB0
    hsmallSize hsmallCap hsmallEnvelope hsmallB
  have hThree := norm_weightedVaughanIntervalThree_inverseSquare_le
    hX hT hH hdelta hTy hTx hxy hyx hXhi hXratio hC hB0
    hsmallSize hsmallCap hsmallEnvelope hsmallB
  have hFour := norm_weightedVaughanIntervalFour_inverseSquare_le
    hX hT hH hdelta hC hlargeSize hlargeCap hlargeEnvelope
    hXlo hXhi hyx hXratio
  unfold inverseSquareChebyshevMajorant
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hTwo hThree)) hFour)

end

end InverseSquareChebyshev
end Erdos378
