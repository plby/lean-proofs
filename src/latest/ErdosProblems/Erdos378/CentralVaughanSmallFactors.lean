/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.CentralProductInterval
import ErdosProblems.Erdos378.VaughanReciprocalFull

/-!
# Vaughan's small-factor terms in the central reciprocal range

The cutoff is allowed to grow.  A single parameter `B` uniformly bounds the
adaptive interval envelope for every extracted factor up to `T²`.  The
finite estimates below retain the exact `T` and `T²` support sizes.
-/

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Erdos378
namespace CentralVaughanSmallFactors

open BoundedGaps.Maynard
open PrimeReciprocal
open AdaptiveShifts
open CentralCorrelation
open CentralProductInterval
open VaughanReciprocalFull

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

theorem norm_weightedVaughanIntervalTwo_central_le
    {X : ℝ} (hX : 0 < X) {x y T : ℕ} {B : ℝ}
    (hT : 0 < T) (hTy : T ≤ y) (hTx : T ^ 4 ≤ x)
    (hxy : x < y) (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hB0 : 0 ≤ B)
    (hsize : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      centralCorrelationSizeCondition (x / q + 1))
    (hB : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      1 + adaptiveCorrelationEnvelope (x / q + 1) ≤ B) :
    ‖weightedVaughanIntervalTwo (reciprocalWeight X) T x y‖ ≤
      (T : ℝ) * (2 * Real.log (y : ℝ) * B) := by
  rw [weightedVaughanIntervalTwo_eq_nested]
  calc
    _ ≤ ∑ d ∈ (Finset.Icc 1 y).filter (fun d : ℕ ↦ (d : ℝ) ≤ T),
        ‖((ArithmeticFunction.moebius d : ℝ) : ℂ) *
          ∑ h ∈ Finset.Ioc (x / d) (y / d),
            (Real.log h : ℂ) * reciprocalWeight X (d * h)‖ := norm_sum_le _ _
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
      have hinner := norm_log_weighted_centralProductInterval_le
        hX hdpos hdx hdscale hxy hXlo hXhi hyx
          (hsize d hdpos hdTsq)
      have hlog0 : 0 ≤ Real.log (y : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hT.trans_le hTy)
      calc
        _ ≤ 1 * (2 * Real.log (y : ℝ) *
            (1 + adaptiveCorrelationEnvelope (x / d + 1))) := by
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
            exact Finset.mem_Icc.mpr ⟨( Finset.mem_Icc.mp hdy).1,
              by exact_mod_cast hdTreal⟩)
          _ = T := by simp only [Nat.card_Icc]; omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
        (mul_nonneg (mul_nonneg (by positivity)
          (Real.log_nonneg (by exact_mod_cast hT.trans_le hTy))) hB0)

private lemma weightedVaughanIntervalThree_eq_supported
    {X : ℝ} {x y T : ℕ} (hT : 0 < T) :
    -weightedVaughanIntervalThree (reciprocalWeight X) T T x y =
      ∑ t ∈ (Finset.Icc 1 y).filter (fun t : ℕ ↦ t ≤ T ^ 2),
        ((vaughanThirdCoefficient T T t : ℝ) : ℂ) *
          ∑ r ∈ Finset.Ioc (x / t) (y / t), reciprocalWeight X (t * r) := by
  rw [neg_weightedVaughanIntervalThree_eq_nested (reciprocalWeight X)
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

theorem norm_weightedVaughanIntervalThree_central_le
    {X : ℝ} (hX : 0 < X) {x y T : ℕ} {B : ℝ}
    (hT : 0 < T) (hTy : T ≤ y) (hTx : T ^ 4 ≤ x)
    (hxy : x < y) (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hB0 : 0 ≤ B)
    (hsize : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      centralCorrelationSizeCondition (x / q + 1))
    (hB : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      1 + adaptiveCorrelationEnvelope (x / q + 1) ≤ B) :
    ‖weightedVaughanIntervalThree (reciprocalWeight X) T T x y‖ ≤
      ((T ^ 2 : ℕ) : ℝ) * (Real.log (y : ℝ) * B) := by
  rw [← norm_neg, weightedVaughanIntervalThree_eq_supported hT]
  calc
    _ ≤ ∑ t ∈ (Finset.Icc 1 y).filter (fun t : ℕ ↦ t ≤ T ^ 2),
        ‖((vaughanThirdCoefficient T T t : ℝ) : ℂ) *
          ∑ r ∈ Finset.Ioc (x / t) (y / t),
            reciprocalWeight X (t * r)‖ := norm_sum_le _ _
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
      have hinner := norm_central_reciprocalProductInterval_partial_le
        hX htpos htx htscale hxy (show y / t ≤ y / t from le_rfl)
          hXlo hXhi hyx (hsize t htpos htT)
      have hlog0 : 0 ≤ Real.log (y : ℝ) :=
        Real.log_nonneg (by
          exact_mod_cast (htpos.trans_le (Finset.mem_Icc.mp hty).2))
      change ‖((vaughanThirdCoefficient T T t : ℝ) : ℂ) *
          reciprocalProductIntervalSum X t (x / t) (y / t)‖ ≤ _
      rw [norm_mul]
      calc
        _ ≤ Real.log (y : ℝ) *
            (1 + adaptiveCorrelationEnvelope (x / t + 1)) :=
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

end

end CentralVaughanSmallFactors
end Erdos378
