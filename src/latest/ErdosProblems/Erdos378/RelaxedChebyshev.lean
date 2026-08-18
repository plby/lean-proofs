/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.RelaxedReciprocal
import ErdosProblems.Erdos378.HighIndexChebyshev

/-!
# Vaughan's identity in the logarithmically relaxed reciprocal range
-/

open Filter
open scoped Topology BigOperators ArithmeticFunction.vonMangoldt

namespace Erdos378
namespace RelaxedChebyshev

open BoundedGaps.Maynard
open PrimeReciprocal
open BilinearReciprocal
open VaughanReciprocalFull
open VaughanReciprocalBlocks
open VaughanReciprocalEstimate
open AdaptiveShifts
open CentralCorrelation
open CentralAsymptotic
open CentralVaughan
open CentralVaughanFourth
open CentralChebyshevApplication
open RelaxedReciprocal
open HighIndexCutoffs
open HighIndexChebyshev
open InverseSquareChebyshevAsymptotic
open ReciprocalChebyshevAsymptotic
open PrimeWeightedInterval

noncomputable section

private lemma small_factor_scale
    {x T q : ℕ} (hq : 0 < q) (hqT : q ≤ T ^ 2)
    (hTx : T ^ 4 ≤ x) : q ≤ x ∧ q ≤ x / q + 1 := by
  have hqSq : q ^ 2 ≤ x := by
    calc
      q ^ 2 ≤ (T ^ 2) ^ 2 := by gcongr
      _ = T ^ 4 := by ring
      _ ≤ x := hTx
  constructor
  · nlinarith
  · exact (Nat.le_div_iff_mul_le hq).2 (by
      simpa [pow_two] using hqSq) |>.trans (Nat.le_add_right _ _)

theorem norm_weightedVaughanIntervalTwo_relaxed_le
    {X : ℝ} (hX : 0 < X) {H x y T : ℕ} {B : ℝ}
    (hH : 1 ≤ H) (hT : 0 < T) (hTy : T ≤ y) (hTx : T ^ 4 ≤ x)
    (hxy : x < y) (hXlo : (y : ℝ) ^ 2 ≤ 4 * (H : ℝ) ^ 2 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x) (hB0 : 0 ≤ B)
    (hsize : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      centralCorrelationSizeCondition (x / q + 1))
    (hB : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      1 + relaxedCorrelationEnvelope H (x / q + 1) ≤ B) :
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
      have hdTsq : d ≤ T ^ 2 := hdT.trans (by nlinarith [hT])
      rcases small_factor_scale hdpos hdTsq hTx with ⟨hdx, hdscale⟩
      rw [norm_mul]
      have hmu : ‖((ArithmeticFunction.moebius d : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hinner := norm_log_weighted_relaxedProductInterval_le
        hX hH hdpos hdx hdscale hxy hXlo hXhi hyx (hsize d hdpos hdTsq)
      calc
        _ ≤ 1 * (2 * Real.log (y : ℝ) *
            (1 + relaxedCorrelationEnvelope H (x / d + 1))) := by
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
            exact Finset.mem_Icc.mpr
              ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1,
                by exact_mod_cast (Finset.mem_filter.mp hd).2⟩)
          _ = T := by simp
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

private lemma weightedVaughanIntervalThree_eq_supported
    {X : ℝ} {x y T : ℕ} (hT : 0 < T) :
    -weightedVaughanIntervalThree (reciprocalWeight X) T T x y =
      ∑ t ∈ (Finset.Icc 1 y).filter (fun t : ℕ ↦ t ≤ T ^ 2),
        ((vaughanThirdCoefficient T T t : ℝ) : ℂ) *
          ∑ r ∈ Finset.Ioc (x / t) (y / t), reciprocalWeight X (t * r) := by
  rw [neg_weightedVaughanIntervalThree_eq_nested (reciprocalWeight X)
    (by exact_mod_cast hT) (by exact_mod_cast hT), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases htT : t ≤ T ^ 2
  · rw [if_pos htT]
  · rw [if_neg htT]
    apply mul_eq_zero_of_left
    have hltR : (T : ℝ) * T < (t : ℝ) := by
      exact_mod_cast (show T * T < t by
        simpa [pow_two] using Nat.lt_of_not_ge htT)
    rw [vaughanThirdCoefficient_eq_zero_of_cutoffProduct_lt
      (by exact_mod_cast hT.le) (by exact_mod_cast hT.le) hltR]
    norm_num

theorem norm_weightedVaughanIntervalThree_relaxed_le
    {X : ℝ} (hX : 0 < X) {H x y T : ℕ} {B : ℝ}
    (hH : 1 ≤ H) (hT : 0 < T) (hTy : T ≤ y) (hTx : T ^ 4 ≤ x)
    (hxy : x < y) (hXlo : (y : ℝ) ^ 2 ≤ 4 * (H : ℝ) ^ 2 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x) (hB0 : 0 ≤ B)
    (hsize : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      centralCorrelationSizeCondition (x / q + 1))
    (hB : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      1 + relaxedCorrelationEnvelope H (x / q + 1) ≤ B) :
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
      have hinner := norm_relaxed_reciprocalProductInterval_partial_le
        hX hH htpos htx htscale hxy le_rfl hXlo hXhi hyx
          (hsize t htpos htT)
      change ‖((vaughanThirdCoefficient T T t : ℝ) : ℂ) *
          reciprocalProductIntervalSum X t (x / t) (y / t)‖ ≤ _
      rw [norm_mul]
      calc
        _ ≤ Real.log (y : ℝ) *
            (1 + relaxedCorrelationEnvelope H (x / t + 1)) :=
          mul_le_mul hcoeff hinner (norm_nonneg _) (by positivity)
        _ ≤ Real.log (y : ℝ) * B := by gcongr; exact hB t htpos htT
    _ ≤ ((T ^ 2 : ℕ) : ℝ) * (Real.log (y : ℝ) * B) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((Finset.Icc 1 y).filter
          (fun t : ℕ ↦ t ≤ T ^ 2)).card ≤ T ^ 2 := by
        calc
          _ ≤ (Finset.Icc 1 (T ^ 2)).card := Finset.card_le_card (by
            intro t ht
            exact Finset.mem_Icc.mpr
              ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp ht).1).1,
                (Finset.mem_filter.mp ht).2⟩)
          _ = T ^ 2 := by simp
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

def relaxedVaughanBlockMajorant (H : ℕ) (V : ℝ) (M K : ℕ) : ℝ :=
  (8 / 3 : ℝ) * (M : ℝ) * (K : ℝ) *
    (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
      ((max M K : ℕ) +
        relaxedCorrelationEnvelope H (max M K) * (min M K : ℕ))

lemma relaxedVaughanBlockMajorant_nonneg
    {H M K : ℕ} {V : ℝ} (hmax : 1 ≤ max M K) :
    0 ≤ relaxedVaughanBlockMajorant H V M K := by
  unfold relaxedVaughanBlockMajorant
  have hE := relaxedCorrelationEnvelope_nonneg H hmax
  positivity

theorem norm_relaxed_reciprocalVaughanBlock_sq_le
    {X U V : ℝ} {H x y M K : ℕ}
    (hH : 1 ≤ H) (hV : 1 ≤ V) (hM : 0 < M) (hK : 0 < K)
    (hsize : centralCorrelationSizeCondition (max M K))
    (hXlo : (y : ℝ) ^ 2 ≤ 4 * (H : ℝ) ^ 2 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x) :
    ‖reciprocalBilinearBlock X x y M (2 * M) K (2 * K)
        (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V)‖ ^ 2 ≤
      relaxedVaughanBlockMajorant H V M K := by
  rcases le_total K M with hKM | hMK
  · have hmax : max M K = M := max_eq_left hKM
    have hbase := norm_relaxed_reciprocalBilinearBlock_sq_le_energy
      (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V)
      hH (show 1 ≤ M by omega) hK hKM hXlo hXhi hyx
        (by simpa [hmax] using hsize)
    let EA := (M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2
    let EB := (8 / 3 : ℝ) * (K : ℝ) * (Real.log V + 3) ^ 2
    let B := relaxedCorrelationEnvelope H M
    have hEA : (∑ m ∈ Finset.Ioc M (2 * M),
        ‖cutoffMangoldtCoefficient U m‖ ^ 2) ≤ EA :=
      sum_norm_sq_cutoffMangoldtCoefficient_Ioc_le U M
    have hEB : (∑ k ∈ Finset.Ioc K (2 * K),
        ‖cutoffFourthCoefficient V k‖ ^ 2) ≤ EB :=
      sum_norm_sq_cutoffFourthCoefficient_Ioc_le hV K
    have hL1 : (∑ k ∈ Finset.Ioc K (2 * K),
        ‖cutoffFourthCoefficient V k‖) ^ 2 ≤ (K : ℝ) * EB :=
      sum_norm_cutoffFourthCoefficient_Ioc_sq_le hV
    have hB : 0 ≤ B := relaxedCorrelationEnvelope_nonneg H (by omega)
    have hinner :
        (M : ℝ) * (∑ k ∈ Finset.Ioc K (2 * K),
            ‖cutoffFourthCoefficient V k‖ ^ 2) +
          B * (∑ k ∈ Finset.Ioc K (2 * K),
            ‖cutoffFourthCoefficient V k‖) ^ 2 ≤
        EB * ((M : ℝ) + B * (K : ℝ)) := by
      calc
        _ ≤ (M : ℝ) * EB + B * ((K : ℝ) * EB) :=
          add_le_add (mul_le_mul_of_nonneg_left hEB (by positivity))
            (mul_le_mul_of_nonneg_left hL1 hB)
        _ = _ := by ring
    calc
      _ ≤ (∑ m ∈ Finset.Ioc M (2 * M),
          ‖cutoffMangoldtCoefficient U m‖ ^ 2) *
          ((M : ℝ) * (∑ k ∈ Finset.Ioc K (2 * K),
            ‖cutoffFourthCoefficient V k‖ ^ 2) +
          B * (∑ k ∈ Finset.Ioc K (2 * K),
            ‖cutoffFourthCoefficient V k‖) ^ 2) := hbase
      _ ≤ EA * (EB * ((M : ℝ) + B * (K : ℝ))) := by
        exact mul_le_mul hEA hinner (by positivity) (by positivity)
      _ = _ := by
        simp only [EA, EB, B, relaxedVaughanBlockMajorant, hmax,
          min_eq_right hKM]
        push_cast
        ring
  · have hmax : max M K = K := max_eq_right hMK
    have hbase := norm_relaxed_reciprocalBilinearBlock_sq_le_energy
      (cutoffFourthCoefficient V) (cutoffMangoldtCoefficient U)
      hH (show 1 ≤ K by omega) hM hMK hXlo hXhi hyx
        (by simpa [hmax] using hsize)
    let EA := (M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2
    let EB := (8 / 3 : ℝ) * (K : ℝ) * (Real.log V + 3) ^ 2
    let B := relaxedCorrelationEnvelope H K
    have hEA : (∑ m ∈ Finset.Ioc M (2 * M),
        ‖cutoffMangoldtCoefficient U m‖ ^ 2) ≤ EA :=
      sum_norm_sq_cutoffMangoldtCoefficient_Ioc_le U M
    have hEB : (∑ k ∈ Finset.Ioc K (2 * K),
        ‖cutoffFourthCoefficient V k‖ ^ 2) ≤ EB :=
      sum_norm_sq_cutoffFourthCoefficient_Ioc_le hV K
    have hL1 : (∑ m ∈ Finset.Ioc M (2 * M),
        ‖cutoffMangoldtCoefficient U m‖) ^ 2 ≤ (M : ℝ) * EA :=
      sum_norm_cutoffMangoldtCoefficient_Ioc_sq_le
    have hB : 0 ≤ B := relaxedCorrelationEnvelope_nonneg H (by omega)
    have hinner :
        (K : ℝ) * (∑ m ∈ Finset.Ioc M (2 * M),
            ‖cutoffMangoldtCoefficient U m‖ ^ 2) +
          B * (∑ m ∈ Finset.Ioc M (2 * M),
            ‖cutoffMangoldtCoefficient U m‖) ^ 2 ≤
        EA * ((K : ℝ) + B * (M : ℝ)) := by
      calc
        _ ≤ (K : ℝ) * EA + B * ((M : ℝ) * EA) :=
          add_le_add (mul_le_mul_of_nonneg_left hEA (by positivity))
            (mul_le_mul_of_nonneg_left hL1 hB)
        _ = _ := by ring
    rw [reciprocalBilinearBlock_comm]
    calc
      _ ≤ (∑ k ∈ Finset.Ioc K (2 * K),
          ‖cutoffFourthCoefficient V k‖ ^ 2) *
          ((K : ℝ) * (∑ m ∈ Finset.Ioc M (2 * M),
            ‖cutoffMangoldtCoefficient U m‖ ^ 2) +
          B * (∑ m ∈ Finset.Ioc M (2 * M),
            ‖cutoffMangoldtCoefficient U m‖) ^ 2) := hbase
      _ ≤ EB * (EA * ((K : ℝ) + B * (M : ℝ))) := by
        exact mul_le_mul hEB hinner (by positivity) (by positivity)
      _ = _ := by
        simp only [EA, EB, B, relaxedVaughanBlockMajorant, hmax,
          min_eq_left hMK]
        push_cast
        ring

lemma relaxedVaughanBlockMajorant_le_uniform
    {H y T M K : ℕ} {delta : ℝ}
    (hT : 0 < T) (hM : 0 < M) (hK : 0 < K)
    (hprod : M * K ≤ y) (hTM : T < 2 * M) (hTK : T < 2 * K)
    (hdelta : 0 ≤ delta)
    (henv : relaxedCorrelationEnvelope H (max M K) ≤
      delta * (max M K : ℕ)) :
    relaxedVaughanBlockMajorant H T M K ≤
      centralFourthUniformMajorant y T delta := by
  have hprodR : (M : ℝ) * K ≤ y := by exact_mod_cast hprod
  rcases le_total K M with hKM | hMK
  · have hmax : max M K = M := max_eq_left hKM
    have hMy : M ≤ y := by nlinarith
    have hlog : Real.log (2 * (M : ℝ)) ≤ Real.log (2 * (y : ℝ)) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2 hMy)
    have hlong : (M : ℝ) ≤ (M : ℝ) * K * (2 / (T : ℝ)) := by
      have hTR : (0 : ℝ) < T := by exact_mod_cast hT
      have hone : (1 : ℝ) ≤ (K : ℝ) * (2 / (T : ℝ)) := by
        rw [show (K : ℝ) * (2 / (T : ℝ)) = (2 * K) / T by ring,
          le_div_iff₀ hTR]
        norm_num
        exact_mod_cast hTK.le
      nlinarith
    have hoff : relaxedCorrelationEnvelope H M * (K : ℝ) ≤
        ((M : ℝ) * K) * delta := by
      calc
        _ ≤ (delta * (M : ℝ)) * K := by
          gcongr
          simpa [hmax] using henv
        _ = _ := by ring
    have hbracket0 : 0 ≤ (M : ℝ) +
        relaxedCorrelationEnvelope H M * (K : ℝ) := by
      exact add_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (relaxedCorrelationEnvelope_nonneg H (by omega))
          (Nat.cast_nonneg _))
    have hlogM0 : 0 ≤ Real.log (2 * (M : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * M by omega))
    have hbracket : (M : ℝ) + relaxedCorrelationEnvelope H M * K ≤
        ((M : ℝ) * K) * (2 / (T : ℝ) + delta) := by
      linarith
    unfold relaxedVaughanBlockMajorant centralFourthUniformMajorant
    simp only [hmax, min_eq_right hKM]
    calc
      _ = (8 / 3 : ℝ) * ((M : ℝ) * K) *
          (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log (T : ℝ) + 3) ^ 2 *
          ((M : ℝ) + relaxedCorrelationEnvelope H M * K) := by ring
      _ ≤ (8 / 3 : ℝ) * ((M : ℝ) * K) *
          (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log (T : ℝ) + 3) ^ 2 *
          (((M : ℝ) * K) * (2 / (T : ℝ) + delta)) := by
        gcongr
      _ ≤ (8 / 3 : ℝ) * (y : ℝ) *
          (Real.log (2 * (y : ℝ))) ^ 2 * (Real.log (T : ℝ) + 3) ^ 2 *
          ((y : ℝ) * (2 / (T : ℝ) + delta)) := by gcongr
      _ = _ := by ring
  · have hmax : max M K = K := max_eq_right hMK
    have hMy : M ≤ y := by nlinarith
    have hlog : Real.log (2 * (M : ℝ)) ≤ Real.log (2 * (y : ℝ)) :=
      Real.log_le_log (by positivity) (by exact_mod_cast Nat.mul_le_mul_left 2 hMy)
    have hlong : (K : ℝ) ≤ (M : ℝ) * K * (2 / (T : ℝ)) := by
      have hTR : (0 : ℝ) < T := by exact_mod_cast hT
      have hone : (1 : ℝ) ≤ (M : ℝ) * (2 / (T : ℝ)) := by
        rw [show (M : ℝ) * (2 / (T : ℝ)) = (2 * M) / T by ring,
          le_div_iff₀ hTR]
        norm_num
        exact_mod_cast hTM.le
      nlinarith
    have hoff : relaxedCorrelationEnvelope H K * (M : ℝ) ≤
        ((M : ℝ) * K) * delta := by
      calc
        _ ≤ (delta * (K : ℝ)) * M := by
          gcongr
          simpa [hmax] using henv
        _ = _ := by ring
    have hbracket0 : 0 ≤ (K : ℝ) +
        relaxedCorrelationEnvelope H K * (M : ℝ) := by
      exact add_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (relaxedCorrelationEnvelope_nonneg H (by omega))
          (Nat.cast_nonneg _))
    have hlogM0 : 0 ≤ Real.log (2 * (M : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * M by omega))
    have hbracket : (K : ℝ) + relaxedCorrelationEnvelope H K * M ≤
        ((M : ℝ) * K) * (2 / (T : ℝ) + delta) := by
      linarith
    unfold relaxedVaughanBlockMajorant centralFourthUniformMajorant
    simp only [hmax, min_eq_left hMK]
    calc
      _ = (8 / 3 : ℝ) * ((M : ℝ) * K) *
          (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log (T : ℝ) + 3) ^ 2 *
          ((K : ℝ) + relaxedCorrelationEnvelope H K * M) := by ring
      _ ≤ (8 / 3 : ℝ) * ((M : ℝ) * K) *
          (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log (T : ℝ) + 3) ^ 2 *
          (((M : ℝ) * K) * (2 / (T : ℝ) + delta)) := by
        gcongr
      _ ≤ (8 / 3 : ℝ) * (y : ℝ) *
          (Real.log (2 * (y : ℝ))) ^ 2 * (Real.log (T : ℝ) + 3) ^ 2 *
          ((y : ℝ) * (2 / (T : ℝ) + delta)) := by gcongr
      _ = _ := by ring

theorem norm_weightedVaughanIntervalFour_relaxed_le
    {X : ℝ} {H x y T : ℕ} {delta : ℝ}
    (hH : 1 ≤ H) (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hsize : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      centralCorrelationSizeCondition L)
    (henv : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      relaxedCorrelationEnvelope H L ≤ delta * L)
    (hXlo : (y : ℝ) ^ 2 ≤ 4 * (H : ℝ) ^ 2 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x) :
    ‖weightedVaughanIntervalFour (reciprocalWeight X) T T x y‖ ≤
      ((dyadicExponentRange y).card : ℝ) ^ 2 *
        Real.sqrt (centralFourthUniformMajorant y T delta) := by
  let A := centralFourthUniformMajorant y T delta
  have hA : 0 ≤ A := centralFourthUniformMajorant_nonneg hT hdelta
  have hblock (alpha beta : ℕ) :
      ‖reciprocalVaughanFourthDyadicBlock X T T x y alpha beta‖ ≤
        Real.sqrt A := by
    apply (Real.le_sqrt (norm_nonneg _) hA).2
    let M := 2 ^ alpha
    let K := 2 ^ beta
    rw [reciprocalVaughanFourthDyadicBlock_eq_full]
    simp only [reciprocalVaughanFourthFullDyadicBlock, pow_succ, Nat.mul_comm]
    change ‖reciprocalBilinearBlock X x y M (2 * M) K (2 * K)
      (cutoffMangoldtCoefficient T) (cutoffFourthCoefficient T)‖ ^ 2 ≤ A
    by_cases hyprod : y < M * K
    · rw [reciprocalVaughanBlock_eq_zero_of_product_above
        X T T x y M K hyprod, norm_zero, zero_pow (by norm_num)]
      exact hA
    have hprod : M * K ≤ y := Nat.le_of_not_gt hyprod
    by_cases hxprod : 4 * M * K ≤ x
    · rw [reciprocalVaughanBlock_eq_zero_of_product_below
        X T T x y M K hxprod, norm_zero, zero_pow (by norm_num)]
      exact hA
    by_cases hTM : 2 * M ≤ T
    · rw [reciprocalVaughanBlock_eq_zero_of_mangoldt_cutoff
        X T T x y M K (by exact_mod_cast hTM), norm_zero, zero_pow (by norm_num)]
      exact hA
    by_cases hTK : 2 * K ≤ T
    · rw [reciprocalVaughanBlock_eq_zero_of_fourth_cutoff
        X T T x y M K (by exact_mod_cast hTK), norm_zero, zero_pow (by norm_num)]
      exact hA
    let L := max M K
    have hprodL : M * K ≤ L ^ 2 := by
      rcases le_total K M with hKM | hMK
      · simp only [L, max_eq_left hKM]; nlinarith
      · simp only [L, max_eq_right hMK]; nlinarith
    have hxL : x < 4 * L ^ 2 := (Nat.lt_of_not_ge hxprod).trans_le (by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 4 hprodL)
    have hLy : L ≤ y := max_le (by nlinarith) (by nlinarith)
    exact (norm_relaxed_reciprocalVaughanBlock_sq_le hH
      (by exact_mod_cast hT) (by positivity) (by positivity)
      (hsize L hxL hLy) hXlo hXhi hyx).trans
        (relaxedVaughanBlockMajorant_le_uniform hT (by positivity) (by positivity)
          hprod (Nat.lt_of_not_ge hTM) (Nat.lt_of_not_ge hTK) hdelta
            (henv L hxL hLy))
  rw [weightedVaughanIntervalFour_reciprocal_eq_neg_sum_dyadicBlocks
    X (by exact_mod_cast hT) (by exact_mod_cast hT) x y, norm_neg]
  calc
    _ ≤ ∑ alpha ∈ dyadicExponentRange y,
        ∑ beta ∈ dyadicExponentRange y,
          ‖reciprocalVaughanFourthDyadicBlock X T T x y alpha beta‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun alpha ha ↦ norm_sum_le _ _)
    _ ≤ ∑ _alpha ∈ dyadicExponentRange y,
        ∑ _beta ∈ dyadicExponentRange y, Real.sqrt A := by
      exact Finset.sum_le_sum fun alpha ha ↦
        Finset.sum_le_sum fun beta hb ↦ hblock alpha beta
    _ = ((dyadicExponentRange y).card : ℝ) ^ 2 * Real.sqrt A := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring

def relaxedChebyshevMajorant (y T H : ℕ) (B delta : ℝ) : ℝ :=
  (T : ℝ) * (2 * Real.log (y : ℝ) * B) +
    ((T ^ 2 : ℕ) : ℝ) * (Real.log (y : ℝ) * B) +
      ((dyadicExponentRange y).card : ℝ) ^ 2 *
        Real.sqrt (centralFourthUniformMajorant y T delta)

theorem norm_weightedChebyshevInterval_relaxed_le
    {X : ℝ} (hX : 0 < X) {H x y T : ℕ} {B delta : ℝ}
    (hH : 1 ≤ H) (hT : 0 < T) (hTy : T ≤ y) (hTx : T ^ 4 ≤ x)
    (hxy : x < y) (hXlo : (y : ℝ) ^ 2 ≤ 4 * (H : ℝ) ^ 2 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hB0 : 0 ≤ B) (hdelta : 0 ≤ delta)
    (hsmallSize : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      centralCorrelationSizeCondition (x / q + 1))
    (hsmallB : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      1 + relaxedCorrelationEnvelope H (x / q + 1) ≤ B)
    (hlargeSize : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      centralCorrelationSizeCondition L)
    (hlargeEnvelope : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      relaxedCorrelationEnvelope H L ≤ delta * L) :
    ‖weightedChebyshevInterval (reciprocalWeight X) x y‖ ≤
      relaxedChebyshevMajorant y T H B delta := by
  have hTone : 1 ≤ T := hT
  have hTlex : T ≤ x := by
    exact (show T ≤ T ^ 4 by nlinarith [pow_pos hT 2, pow_pos hT 3]).trans hTx
  rw [weightedChebyshevInterval_eq_vaughan,
    weightedVaughanIntervalOne_reciprocal_eq_zero (by exact_mod_cast hTlex),
    zero_add]
  have hTwo := norm_weightedVaughanIntervalTwo_relaxed_le
    hX hH hT hTy hTx hxy hXlo hXhi hyx hB0 hsmallSize hsmallB
  have hThree := norm_weightedVaughanIntervalThree_relaxed_le
    hX hH hT hTy hTx hxy hXlo hXhi hyx hB0 hsmallSize hsmallB
  have hFour := norm_weightedVaughanIntervalFour_relaxed_le
    hH hT hdelta hlargeSize hlargeEnvelope hXlo hXhi hyx
  unfold relaxedChebyshevMajorant
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hTwo hThree)) hFour)

/-! ## The relaxed near-central majorant -/

/-- The type-I/II envelope after allowing the reciprocal frequency to lose
the square of the logarithmic separation parameter. -/
def relaxedNearTypeBound (y : ℕ) : ℝ :=
  HighIndexChebyshev.nearTypeBound y +
    firstDerivativeEnvelope (farSeparation y)

/-- The relative correlation error used for the type-IV term. -/
def relaxedNearDelta (y : ℕ) : ℝ :=
  centralUniformDelta y +
    firstDerivativeEnvelope (farSeparation y) /
      (inverseSquareUniformScale y : ℝ)

def relaxedNearFourthError (y : ℕ) : ℝ :=
  2 / (nearVaughanCutoff y : ℝ) + relaxedNearDelta y

def relaxedNearChebyshevMajorant (y : ℕ) : ℝ :=
  relaxedChebyshevMajorant y (nearVaughanCutoff y) (farSeparation y)
    (relaxedNearTypeBound y) (relaxedNearDelta y)

def relaxedNearPrimeMajorant (y : ℕ) : ℝ :=
  relaxedNearChebyshevMajorant y +
    (Chebyshev.psi (y : ℝ) - Chebyshev.theta (y : ℝ))

lemma relaxedNearTypeBound_nonneg (y : ℕ) :
    0 ≤ relaxedNearTypeBound y := by
  unfold relaxedNearTypeBound
  exact add_nonneg (HighIndexChebyshev.nearTypeBound_nonneg y)
    (firstDerivativeEnvelope_nonneg _)

lemma relaxedNearDelta_nonneg (y : ℕ) : 0 ≤ relaxedNearDelta y := by
  unfold relaxedNearDelta
  exact add_nonneg (centralUniformDelta_nonneg y)
    (div_nonneg (firstDerivativeEnvelope_nonneg _) (Nat.cast_nonneg _))

lemma relaxedNearFourthError_nonneg (y : ℕ) :
    0 ≤ relaxedNearFourthError y := by
  unfold relaxedNearFourthError
  exact add_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _))
    (relaxedNearDelta_nonneg y)

lemma relaxedNearChebyshevMajorant_nonneg (y : ℕ) :
    0 ≤ relaxedNearChebyshevMajorant y := by
  unfold relaxedNearChebyshevMajorant relaxedChebyshevMajorant
  exact add_nonneg (add_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
      (mul_nonneg (by norm_num) (Real.log_natCast_nonneg y))
      (relaxedNearTypeBound_nonneg y)))
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
      (Real.log_natCast_nonneg y) (relaxedNearTypeBound_nonneg y))))
    (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))

lemma relaxedNearPrimeMajorant_nonneg (y : ℕ) :
    0 ≤ relaxedNearPrimeMajorant y := by
  unfold relaxedNearPrimeMajorant
  exact add_nonneg (relaxedNearChebyshevMajorant_nonneg y)
    (sub_nonneg.mpr (Chebyshev.theta_le_psi _))

theorem tendsto_log_39_mul_firstDerivativeEnvelope_div_uniformScale_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 39 *
      (firstDerivativeEnvelope (farSeparation y) /
        (inverseSquareUniformScale y : ℝ))) atTop (nhds 0) := by
  have hmodel := tendsto_logarithmicSafety_pow_div_baseShift 1
  have hupper : Tendsto (fun y : ℕ ↦
      1700000 * (logarithmicSafety y / (baseShift y : ℝ)))
      atTop (nhds 0) := by
    simpa only [pow_one, mul_zero] using hmodel.const_mul 1700000
  have hn : ∀ᶠ y : ℕ in atTop,
      0 ≤ Real.log (y : ℝ) ^ 39 *
        (firstDerivativeEnvelope (farSeparation y) /
          (inverseSquareUniformScale y : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 39)
      (div_nonneg (firstDerivativeEnvelope_nonneg _) (Nat.cast_nonneg _))
  have hb : ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ^ 39 *
          (firstDerivativeEnvelope (farSeparation y) /
            (inverseSquareUniformScale y : ℝ)) ≤
        1700000 * (logarithmicSafety y / (baseShift y : ℝ)) := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    let G : ℝ := Real.log (y : ℝ)
    let H : ℝ := farSeparation y
    let q : ℝ := baseShift y
    let Z : ℝ := inverseSquareUniformScale y
    have hG : 1 ≤ G := by simpa only [G] using
      BoundedGaps.Maynard.one_le_log_natCast hy
    have hH : H ≤ 2 * G ^ 8 := by
      simpa only [H, G, farSeparation] using
        logPowerCutoff_le_two_log_pow (e := 8) hy
    have hq : 0 < q := by
      dsimp only [q]
      exact_mod_cast baseShift_pos (show 0 < y by omega)
    have hqZ : q ≤ Z := by
      dsimp only [q, Z, inverseSquareUniformScale]
      exact_mod_cast Nat.le_add_right (baseShift y) 1
    have hH0 : 0 ≤ H := by dsimp only [H]; positivity
    have hFD : firstDerivativeEnvelope (farSeparation y) ≤
        1700000 * G ^ 32 := by
      unfold firstDerivativeEnvelope
      change 100000 * (H ^ 4 + 1) ≤ 1700000 * G ^ 32
      calc
        _ ≤ 100000 * ((2 * G ^ 8) ^ 4 + G ^ 32) := by
          gcongr
          exact one_le_pow₀ hG
        _ = 1700000 * G ^ 32 := by ring
    have hp : G ^ 71 ≤ logarithmicSafety y := by
      unfold logarithmicSafety
      calc
        G ^ 71 ≤ G ^ 100 := pow_le_pow_right₀ hG (by omega)
        _ ≤ (G + 2) ^ 100 := by
          gcongr
          linarith
    change G ^ 39 *
        (firstDerivativeEnvelope (farSeparation y) / Z) ≤
      1700000 * (logarithmicSafety y / q)
    calc
      _ = G ^ 39 * firstDerivativeEnvelope (farSeparation y) / Z := by ring
      _ ≤ G ^ 39 * (1700000 * G ^ 32) / q := by gcongr
      _ = 1700000 * (G ^ 71 / q) := by ring
      _ ≤ 1700000 * (logarithmicSafety y / q) := by gcongr
  exact squeeze_zero' hn hb hupper

theorem tendsto_log_97_mul_firstDerivativeEnvelope_div_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 97 *
      (firstDerivativeEnvelope (farSeparation y) / (y : ℝ)))
      atTop (nhds 0) := by
  have hmodel := tendsto_log_natCast_rpow_div_rpow (129 : ℝ) 1 (by norm_num)
  have hmodel' : Tendsto (fun y : ℕ ↦
      Real.log (y : ℝ) ^ 129 / (y : ℝ)) atTop (nhds 0) := by
    apply hmodel.congr'
    filter_upwards with y
    rw [Real.rpow_one]
    congr 1
    exact Real.rpow_natCast _ 129
  have hupper : Tendsto (fun y : ℕ ↦
      1700000 * (Real.log (y : ℝ) ^ 129 / (y : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hmodel'.const_mul 1700000
  have hn : ∀ᶠ y : ℕ in atTop,
      0 ≤ Real.log (y : ℝ) ^ 97 *
        (firstDerivativeEnvelope (farSeparation y) / (y : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with y hy
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 97)
      (div_nonneg (firstDerivativeEnvelope_nonneg _) (Nat.cast_nonneg _))
  have hb : ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ^ 97 *
          (firstDerivativeEnvelope (farSeparation y) / (y : ℝ)) ≤
        1700000 * (Real.log (y : ℝ) ^ 129 / (y : ℝ)) := by
    filter_upwards [eventually_ge_atTop 4] with y hy
    let G : ℝ := Real.log (y : ℝ)
    let H : ℝ := farSeparation y
    have hG : 1 ≤ G := by simpa only [G] using
      BoundedGaps.Maynard.one_le_log_natCast hy
    have hH : H ≤ 2 * G ^ 8 := by
      simpa only [H, G, farSeparation] using
        logPowerCutoff_le_two_log_pow (e := 8) hy
    have hFD : firstDerivativeEnvelope (farSeparation y) ≤
        1700000 * G ^ 32 := by
      unfold firstDerivativeEnvelope
      change 100000 * (H ^ 4 + 1) ≤ 1700000 * G ^ 32
      calc
        _ ≤ 100000 * ((2 * G ^ 8) ^ 4 + G ^ 32) := by
          gcongr
          exact one_le_pow₀ hG
        _ = 1700000 * G ^ 32 := by ring
    change G ^ 97 * (firstDerivativeEnvelope (farSeparation y) / (y : ℝ)) ≤
      1700000 * (G ^ 129 / (y : ℝ))
    calc
      _ = G ^ 97 * firstDerivativeEnvelope (farSeparation y) / (y : ℝ) := by
        ring
      _ ≤ G ^ 97 * (1700000 * G ^ 32) / (y : ℝ) := by gcongr
      _ = 1700000 * (G ^ 129 / (y : ℝ)) := by ring
  exact squeeze_zero' hn hb hupper

theorem tendsto_log_39_mul_relaxedNearFourthError_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 39 *
      relaxedNearFourthError y) atTop (nhds 0) := by
  have h := HighIndexChebyshev.tendsto_log_39_mul_nearFourthError_zero.add
    tendsto_log_39_mul_firstDerivativeEnvelope_div_uniformScale_zero
  convert h using 1
  · funext y
    unfold relaxedNearFourthError relaxedNearDelta
      HighIndexChebyshev.nearFourthError
    ring
  · norm_num

theorem tendsto_log_97_mul_relaxedNearTypeBound_div_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 97 *
      (relaxedNearTypeBound y / (y : ℝ))) atTop (nhds 0) := by
  have h := HighIndexChebyshev.tendsto_log_97_mul_nearTypeBound_div_zero.add
    tendsto_log_97_mul_firstDerivativeEnvelope_div_zero
  convert h using 1
  · funext y
    by_cases hy : y = 0
    · simp [hy, relaxedNearTypeBound]
    unfold relaxedNearTypeBound
    field_simp
  · norm_num

lemma relaxed_near_fourth_term_scaled_le {y : ℕ} (hy : 4 ≤ y)
    (hlogT : Real.log (nearVaughanCutoff y : ℝ) + 3 ≤
      Real.sqrt (Real.log (y : ℝ))) :
    Real.log (y : ℝ) ^ 16 *
        (((dyadicExponentRange y).card : ℝ) ^ 2 *
          Real.sqrt (centralFourthUniformMajorant y
            (nearVaughanCutoff y) (relaxedNearDelta y)) / (y : ℝ)) ≤
      nearFourthLimitConstant *
        Real.sqrt (Real.log (y : ℝ) ^ 39 * relaxedNearFourthError y) := by
  let Y : ℝ := y
  let G : ℝ := Real.log Y
  let T : ℝ := nearVaughanCutoff y
  let E : ℝ := relaxedNearFourthError y
  let D : ℝ := Real.sqrt 20
  have hY : 0 < Y := by positivity
  have hG : 1 ≤ G := by
    simpa only [G, Y] using BoundedGaps.Maynard.one_le_log_natCast hy
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hT : 0 < T := by
    change (0 : ℝ) < nearVaughanCutoff y
    exact_mod_cast logPowerCutoff_pos 40 y
  have hE : 0 ≤ E := by
    simpa only [E] using relaxedNearFourthError_nonneg y
  have hlogTwo : Real.log (2 * Y) ≤ 2 * G := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hY.ne']
    have hlog2 : Real.log 2 ≤ G :=
      Real.log_le_log (by norm_num) (by
        change (2 : ℝ) ≤ (y : ℝ)
        exact_mod_cast (show 2 ≤ y by omega))
    linarith
  have hlogTwo0 : 0 ≤ Real.log (2 * Y) :=
    Real.log_nonneg (by
      change (1 : ℝ) ≤ 2 * (y : ℝ)
      exact_mod_cast (show 1 ≤ 2 * y by omega))
  have hlogT0 : 0 ≤ Real.log T + 3 := by
    have hTone : (1 : ℝ) ≤ T := by
      change (1 : ℝ) ≤ (nearVaughanCutoff y : ℝ)
      exact_mod_cast (show 1 ≤ logPowerCutoff 40 y by
        exact logPowerCutoff_pos 40 y)
    linarith [Real.log_nonneg hTone]
  have hsqrtG0 : 0 ≤ Real.sqrt G := Real.sqrt_nonneg _
  have hA : centralFourthUniformMajorant y (nearVaughanCutoff y)
      (relaxedNearDelta y) ≤ 20 * Y ^ 2 * G ^ 3 * E := by
    unfold centralFourthUniformMajorant
    change (8 / 3 : ℝ) * Y ^ 2 * Real.log (2 * Y) ^ 2 *
      (Real.log T + 3) ^ 2 * E ≤ _
    calc
      _ ≤ (8 / 3 : ℝ) * Y ^ 2 * (2 * G) ^ 2 *
          (Real.sqrt G) ^ 2 * E := by gcongr
      _ = (32 / 3 : ℝ) * Y ^ 2 * G ^ 3 * E := by
        rw [Real.sq_sqrt hG0]
        ring
      _ ≤ 20 * Y ^ 2 * G ^ 3 * E := by
        have hrest : 0 ≤ Y ^ 2 * G ^ 3 * E := by positivity
        nlinarith
  have hDsq : D ^ 2 = 20 := by
    dsimp only [D]
    rw [Real.sq_sqrt]
    norm_num
  have hsqrtA : Real.sqrt (centralFourthUniformMajorant y
      (nearVaughanCutoff y) (relaxedNearDelta y)) ≤
      D * Y * Real.sqrt (G ^ 3 * E) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    calc
      _ ≤ 20 * Y ^ 2 * G ^ 3 * E := hA
      _ = (D * Y * Real.sqrt (G ^ 3 * E)) ^ 2 := by
        rw [mul_pow, mul_pow, hDsq, Real.sq_sqrt (mul_nonneg
          (pow_nonneg hG0 3) hE)]
        ring
  have hcard := card_dyadicExponentRange_le_four_log hy
  change ((dyadicExponentRange y).card : ℝ) ≤ 4 * G at hcard
  have hcardSq : ((dyadicExponentRange y).card : ℝ) ^ 2 ≤ 16 * G ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ (dyadicExponentRange y).card by positivity]
  have hsqrt36 : Real.sqrt (G ^ 36) = G ^ 18 := by
    rw [show G ^ 36 = (G ^ 18) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hG0 18)]
  have hsqrtSplit : Real.sqrt (G ^ 39 * E) =
      G ^ 18 * Real.sqrt (G ^ 3 * E) := by
    rw [show G ^ 39 * E = G ^ 36 * (G ^ 3 * E) by ring,
      Real.sqrt_mul (pow_nonneg hG0 36), hsqrt36]
  change G ^ 16 * (((dyadicExponentRange y).card : ℝ) ^ 2 *
      Real.sqrt (centralFourthUniformMajorant y
        (nearVaughanCutoff y) (relaxedNearDelta y)) / Y) ≤
    16 * D * Real.sqrt (G ^ 39 * E)
  calc
    _ ≤ G ^ 16 * ((16 * G ^ 2) *
        (D * Y * Real.sqrt (G ^ 3 * E)) / Y) := by gcongr
    _ = 16 * D * (G ^ 18 * Real.sqrt (G ^ 3 * E)) := by
      field_simp
    _ = 16 * D * Real.sqrt (G ^ 39 * E) := by rw [hsqrtSplit]

theorem tendsto_relaxedNearChebyshevMajorant_scaled_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 16 *
      (relaxedNearChebyshevMajorant y / (y : ℝ))) atTop (nhds 0) := by
  let A : ℕ → ℝ := fun y ↦ Real.log (y : ℝ) ^ 97 *
    (relaxedNearTypeBound y / (y : ℝ))
  let B : ℕ → ℝ := fun y ↦ nearFourthLimitConstant *
    Real.sqrt (Real.log (y : ℝ) ^ 39 * relaxedNearFourthError y)
  have hA : Tendsto A atTop (nhds 0) :=
    tendsto_log_97_mul_relaxedNearTypeBound_div_zero
  have hB : Tendsto B atTop (nhds 0) := by
    have hs := tendsto_log_39_mul_relaxedNearFourthError_zero.sqrt
    simpa only [B, Real.sqrt_zero, mul_zero] using
      hs.const_mul nearFourthLimitConstant
  have hlogQuarter := eventually_log_logPowerCutoff_add_three_le 40
  have hnonneg : ∀ y : ℕ, 0 ≤ Real.log (y : ℝ) ^ 16 *
      (relaxedNearChebyshevMajorant y / (y : ℝ)) := by
    intro y
    exact mul_nonneg (pow_nonneg (Real.log_natCast_nonneg y) 16)
      (div_nonneg (relaxedNearChebyshevMajorant_nonneg y) (Nat.cast_nonneg _))
  have hbound : ∀ᶠ y : ℕ in atTop,
      Real.log (y : ℝ) ^ 16 *
          (relaxedNearChebyshevMajorant y / (y : ℝ)) ≤
        8 * A y + B y := by
    filter_upwards [eventually_ge_atTop 4, hlogQuarter] with y hy hquarter
    let G : ℝ := Real.log (y : ℝ)
    let T : ℝ := nearVaughanCutoff y
    let U : ℝ := relaxedNearTypeBound y / (y : ℝ)
    have hG : 1 ≤ G := by
      simpa only [G] using BoundedGaps.Maynard.one_le_log_natCast hy
    have hT : T ≤ 2 * G ^ 40 := by
      simpa only [T, G, nearVaughanCutoff] using
        logPowerCutoff_le_two_log_pow (e := 40) hy
    have hU : 0 ≤ U :=
      div_nonneg (relaxedNearTypeBound_nonneg y) (Nat.cast_nonneg _)
    have hsmall : G ^ 16 *
        ((T * (2 * G * relaxedNearTypeBound y) +
          T ^ 2 * (G * relaxedNearTypeBound y)) / (y : ℝ)) ≤ 8 * A y := by
      have hy0 : (y : ℝ) ≠ 0 := by exact_mod_cast (show y ≠ 0 by omega)
      rw [add_div]
      rw [show T * (2 * G * relaxedNearTypeBound y) / (y : ℝ) =
          T * (2 * G) * U by dsimp only [U]; field_simp,
        show T ^ 2 * (G * relaxedNearTypeBound y) / (y : ℝ) =
          T ^ 2 * G * U by dsimp only [U]; field_simp]
      change G ^ 16 * (T * (2 * G) * U + T ^ 2 * G * U) ≤
        8 * (G ^ 97 * U)
      have hfirst : G ^ 16 * (T * (2 * G) * U) ≤
          4 * G ^ 57 * U := by
        calc
          _ ≤ G ^ 16 * ((2 * G ^ 40) * (2 * G) * U) := by gcongr
          _ = 4 * G ^ 57 * U := by ring
      have hsecond : G ^ 16 * (T ^ 2 * G * U) ≤
          4 * G ^ 97 * U := by
        calc
          _ ≤ G ^ 16 * ((2 * G ^ 40) ^ 2 * G * U) := by gcongr
          _ = 4 * G ^ 97 * U := by ring
      have hp : G ^ 57 ≤ G ^ 97 := pow_le_pow_right₀ hG (by omega)
      calc
        _ = G ^ 16 * (T * (2 * G) * U) +
            G ^ 16 * (T ^ 2 * G * U) := by ring
        _ ≤ 4 * G ^ 57 * U + 4 * G ^ 97 * U := add_le_add hfirst hsecond
        _ ≤ 4 * G ^ 97 * U + 4 * G ^ 97 * U := by gcongr
        _ = 8 * (G ^ 97 * U) := by ring
    have hquarterSqrt : G ^ (1 / 4 : ℝ) ≤ Real.sqrt G := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hG (by norm_num)
    have hfourth := relaxed_near_fourth_term_scaled_le hy
      (hquarter.trans hquarterSqrt)
    unfold relaxedNearChebyshevMajorant relaxedChebyshevMajorant
    norm_num only [Nat.cast_pow]
    change G ^ 16 * ((T * (2 * G * relaxedNearTypeBound y) +
        T ^ 2 * (G * relaxedNearTypeBound y) +
        ((dyadicExponentRange y).card : ℝ) ^ 2 *
          Real.sqrt (centralFourthUniformMajorant y
            (nearVaughanCutoff y) (relaxedNearDelta y))) / (y : ℝ)) ≤ _
    rw [add_div]
    rw [mul_add]
    simpa only [G, B] using add_le_add hsmall hfourth
  have hupper : Tendsto (fun y : ℕ ↦ 8 * A y + B y) atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using hA.const_mul 8 |>.add hB
  exact squeeze_zero' (Eventually.of_forall hnonneg) hbound hupper

theorem tendsto_relaxedNearPrimeMajorant_scaled_zero :
    Tendsto (fun y : ℕ ↦ Real.log (y : ℝ) ^ 16 *
      (relaxedNearPrimeMajorant y / (y : ℝ))) atTop (nhds 0) := by
  unfold relaxedNearPrimeMajorant
  have h := tendsto_relaxedNearChebyshevMajorant_scaled_zero.add
    HighIndexChebyshev.tendsto_primePowerCorrection_scaled_zero
  convert h using 1
  · funext y
    by_cases hy : y = 0
    · simp [hy]
    rw [add_div, mul_add]
  · norm_num

theorem eventually_relaxedNearChebyshev_bound :
    ∀ᶠ y : ℕ in atTop, ∀ {x : ℕ} {X : ℝ},
      x < y → y ≤ 2 * x → 0 < X →
      (y : ℝ) ^ 2 ≤ 4 * (farSeparation y : ℝ) ^ 2 * X →
      X ≤ (y : ℝ) ^ 16 →
      ‖weightedChebyshevInterval (reciprocalWeight X) x y‖ ≤
        relaxedNearChebyshevMajorant y := by
  have hsizeEvent := eventually_centralCorrelationSizeCondition
  rcases hsizeEvent.exists_forall_of_atTop with ⟨M₀, hM₀⟩
  have hZlarge : ∀ᶠ y : ℕ in atTop, M₀ ≤ inverseSquareUniformScale y :=
    tendsto_inverseSquareUniformScale_atTop.eventually (eventually_ge_atTop M₀)
  filter_upwards [eventually_ge_atTop 4,
    HighIndexChebyshev.eventually_near_basic_parameters,
    hZlarge] with y hy hbasic hZlargeY
  intro x X hxy hyx hX hXlo hXhi
  let T := nearVaughanCutoff y
  let H := farSeparation y
  let Z := inverseSquareUniformScale y
  let delta := relaxedNearDelta y
  let B := relaxedNearTypeBound y
  have hT : 0 < T := by exact logPowerCutoff_pos 40 y
  have hH : 1 ≤ H := by
    dsimp only [H, farSeparation]
    exact logPowerCutoff_pos 8 y
  have hZ : 1 ≤ Z := by dsimp only [Z, inverseSquareUniformScale]; omega
  have hdelta : 0 ≤ delta := by
    simpa only [delta] using relaxedNearDelta_nonneg y
  have hB : 0 ≤ B := by
    simpa only [B] using relaxedNearTypeBound_nonneg y
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
      centralCorrelationSizeCondition (x / q + 1) := by
    intro q hq hqT
    exact hM₀ _ (hZlargeY.trans (hsmallM q hq hqT).1)
  have hsmallB : ∀ q : ℕ, 1 ≤ q → q ≤ T ^ 2 →
      1 + relaxedCorrelationEnvelope H (x / q + 1) ≤ B := by
    intro q hq hqT
    have hM := hsmallM q hq hqT
    have henv := adaptiveCorrelationEnvelope_le_uniform hM.1 hM.2
    dsimp only [B, relaxedNearTypeBound,
      HighIndexChebyshev.nearTypeBound, H]
    unfold relaxedCorrelationEnvelope
    calc
      1 + (adaptiveCorrelationEnvelope (x / q + 1) +
          firstDerivativeEnvelope (farSeparation y)) ≤
        1 + (centralUniformDelta y * (y : ℝ) +
          firstDerivativeEnvelope (farSeparation y)) := by
            gcongr
            exact henv.trans (mul_le_mul_of_nonneg_left
              (by exact_mod_cast hM.2) (centralUniformDelta_nonneg y))
      _ = 1 + centralUniformDelta y * (y : ℝ) +
          firstDerivativeEnvelope (farSeparation y) := by ring
  have hlargeM : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      Z ≤ L ∧ L ≤ y := by
    intro L hxL hLy
    have hfour : 4 * Z ^ 2 ≤ x := by
      have htwo : 8 * Z ^ 2 ≤ 2 * x := hbasic.2.2.trans hyx
      omega
    have hsq : Z ^ 2 < L ^ 2 := by nlinarith
    have hZL : Z ≤ L := by nlinarith
    exact ⟨hZL, hLy⟩
  have hlargeSize : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      centralCorrelationSizeCondition L := by
    intro L hxL hLy
    exact hM₀ _ (hZlargeY.trans (hlargeM L hxL hLy).1)
  have hlargeEnvelope : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      relaxedCorrelationEnvelope H L ≤ delta * L := by
    intro L hxL hLy
    have hM := hlargeM L hxL hLy
    have hadaptive := adaptiveCorrelationEnvelope_le_uniform hM.1 hM.2
    have hZpos : (0 : ℝ) < Z := by exact_mod_cast hZ
    have hZL : (Z : ℝ) ≤ L := by exact_mod_cast hM.1
    have hcancel : firstDerivativeEnvelope H =
        (firstDerivativeEnvelope H / (Z : ℝ)) * Z := by
      field_simp [ne_of_gt hZpos]
    have hFD : firstDerivativeEnvelope H ≤
        (firstDerivativeEnvelope H / (Z : ℝ)) * L := by
      calc
        firstDerivativeEnvelope H =
            (firstDerivativeEnvelope H / (Z : ℝ)) * Z := hcancel
        _ ≤ (firstDerivativeEnvelope H / (Z : ℝ)) * L :=
          mul_le_mul_of_nonneg_left hZL
            (div_nonneg (firstDerivativeEnvelope_nonneg H) hZpos.le)
    dsimp only [delta, relaxedNearDelta]
    unfold relaxedCorrelationEnvelope
    calc
      adaptiveCorrelationEnvelope L + firstDerivativeEnvelope H ≤
          centralUniformDelta y * L +
            (firstDerivativeEnvelope H / (Z : ℝ)) * L :=
        add_le_add hadaptive hFD
      _ = (centralUniformDelta y +
          firstDerivativeEnvelope H / (Z : ℝ)) * L := by ring
  apply norm_weightedChebyshevInterval_relaxed_le hX hH hT hTy hTx hxy
    hXlo hXhi hyx hB hdelta hsmallSize hsmallB hlargeSize hlargeEnvelope

theorem eventually_relaxedNearPrime_bound :
    ∀ᶠ y : ℕ in atTop, ∀ {x : ℕ} {X : ℝ},
      x < y → y ≤ 2 * x → 0 < X →
      (y : ℝ) ^ 2 ≤ 4 * (farSeparation y : ℝ) ^ 2 * X →
      X ≤ (y : ℝ) ^ 16 →
      ‖primeWeightedInterval (reciprocalWeight X) x y‖ ≤
        relaxedNearPrimeMajorant y := by
  filter_upwards [eventually_relaxedNearChebyshev_bound] with y hy
  intro x X hxy hyx hX hXlo hXhi
  apply norm_primeWeightedInterval_le
  · intro n
    simp
  · exact hy hxy hyx hX hXlo hXhi

end

end RelaxedChebyshev
end Erdos378
