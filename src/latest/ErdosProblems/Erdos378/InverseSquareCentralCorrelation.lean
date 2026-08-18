/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.InverseSquareAdaptiveShifts
import ErdosProblems.Erdos378.InverseSquareVaughanBlocks

/-!
# Uniform correlations in theinverseSquareCentral range

Here the original inverseSquare frequency may be as large as the sixteenth power of
the prime-window scale.  The product structure of an off-diagonal Vaughan
correlation reduces it to a frequency between a quadratic lower bound and a
thirty-first-power upper bound in the longer dyadic variable.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos378
namespace InverseSquareCentralCorrelation

open InverseSquareCorrelation
open InverseSquareBilinear
open InverseSquareVaughanBlocks
open InverseSquareAdaptiveShifts
open AdaptiveShifts

noncomputable section

abbrev inverseSquareCentralFrequencyConstant : ℝ :=
  inverseSquareFrequencyConstant

abbrev inverseSquareCentralCorrelationSizeCondition (M : ℕ) : Prop :=
  inverseSquareCorrelationSizeCondition M

lemma baseShift_predicate_of_frequency_upper
    {Q : ℝ} (hQ : 0 ≤ Q) {M : ℕ} (hM : 1 ≤ M)
    (hQupper : Q ≤ inverseSquareCentralFrequencyConstant * (M : ℝ) ^ 31)
    (hsize : inverseSquareCentralCorrelationSizeCondition M) :
    inverseSquareShiftPredicate Q M (baseShift M) := by
  exact baseShift_inverseSquarePredicate_of_frequency_upper
    hQ hM hQupper hsize

def inverseSquareCentralCorrelationLower (x M r s : ℕ) : ℕ :=
  max M (max (x / r) (x / s))

def inverseSquareCentralCorrelationUpper (y M r s : ℕ) : ℕ :=
  min (2 * M) (min (y / r) (y / s))

def inverseSquareCentralCorrelationLength (x y M r s : ℕ) : ℕ :=
  inverseSquareCentralCorrelationUpper y M r s -
    inverseSquareCentralCorrelationLower x M r s

def inverseSquareCentralCorrelationFrequency (X : ℝ) (r s : ℕ) : ℝ :=
  X * (((s : ℕ) ^ 2 - r ^ 2 : ℕ) : ℝ) /
    (((r * s : ℕ) : ℝ) ^ 2)

/-- Scale bounds for a nonempty off-diagonal correlation. -/
lemma inverseSquareCentralCorrelation_scale_bounds
    {X : ℝ} {x y M K r s : ℕ}
    (hM : 1 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hr : r ∈ Finset.Ioc K (2 * K))
    (hs : s ∈ Finset.Ioc K (2 * K)) (hrs : r < s)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hNpos : 0 < inverseSquareCentralCorrelationLength x y M r s) :
    let a := inverseSquareCentralCorrelationLower x M r s
    let b := inverseSquareCentralCorrelationUpper y M r s
    let Q := inverseSquareCentralCorrelationFrequency X r s
    a < b ∧ M ≤ a ∧ b ≤ 2 * M ∧ 0 < Q ∧
      (M : ℝ) ≤ 32 * Q ∧
      Q ≤ inverseSquareCentralFrequencyConstant * (M : ℝ) ^ 31 := by
  let a := inverseSquareCentralCorrelationLower x M r s
  let b := inverseSquareCentralCorrelationUpper y M r s
  let d := s - r
  let Q := inverseSquareCentralCorrelationFrequency X r s
  have hrBounds := Finset.mem_Ioc.mp hr
  have hsBounds := Finset.mem_Ioc.mp hs
  have hrPos : 0 < r := hK.trans hrBounds.1
  have hsPos : 0 < s := hK.trans hsBounds.1
  have hdPos : 0 < d := by dsimp only [d]; omega
  have hdK : d ≤ K := by dsimp only [d]; omega
  have haM : M ≤ a := by
    dsimp only [a,inverseSquareCentralCorrelationLower]
    exact Nat.le_max_left _ _
  have hbM : b ≤ 2 * M := by
    dsimp only [b,inverseSquareCentralCorrelationUpper]
    exact Nat.min_le_left _ _
  have hab : a < b := by
    dsimp only [inverseSquareCentralCorrelationLength] at hNpos
    omega
  have hmMem : a + 1 ∈ commonProductInterval x y M (2 * M) r s := by
    rw [commonProductInterval, Finset.mem_Ioc]
    simpa only [a, b,inverseSquareCentralCorrelationLower,inverseSquareCentralCorrelationUpper] using
      (show a < a + 1 ∧ a + 1 ≤ b by omega)
  rcases (mem_commonProductInterval_iff hrPos hsPos).mp hmMem with
    ⟨hmIoc, hmr, hms⟩
  have hmBounds := Finset.mem_Ioc.mp hmIoc
  have hMr : M * K < (a + 1) * r := by
    calc
      M * K < M * r := Nat.mul_lt_mul_of_pos_left hrBounds.1 (by omega)
      _ ≤ (a + 1) * r := Nat.mul_le_mul_right r (by omega)
  have hyLower : M * K < y := hMr.trans_le hmr.2
  have hmUpper : a + 1 ≤ 2 * M := hmBounds.2
  have hxyUpper : y < 8 * M * K := by
    calc
      y ≤ 2 * x := hyx
      _ < 2 * ((a + 1) * r) := by omega
      _ ≤ 2 * ((2 * M) * (2 * K)) := by
        exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul hmUpper hrBounds.2)
      _ = 8 * M * K := by ring
  have hXpos : 0 < X := by
    have hyPos : (0 : ℝ) < y := by
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hyLower)
    nlinarith [sq_pos_of_pos hyPos]
  have hrsPos : (0 : ℝ) < ((r * s : ℕ) : ℝ) := by positivity
  have hrsSqPos : (0 : ℝ) < (((r * s : ℕ) : ℝ) ^ 2) := by positivity
  have hdiffPos : 0 < s ^ 2 - r ^ 2 :=
    Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hrs (by norm_num))
  have hQpos : 0 < Q := by
    dsimp only [Q,inverseSquareCentralCorrelationFrequency]
    positivity
  have hKsq_le_rs : K ^ 2 ≤ r * s := by nlinarith
  have hrs_le_fourKsq : r * s ≤ 4 * K ^ 2 := by nlinarith
  have hyLowerR : (M : ℝ) * K ≤ y := by exact_mod_cast hyLower.le
  have hKsqR : (K : ℝ) ^ 2 ≤ ((r * s : ℕ) : ℝ) := by
    exact_mod_cast hKsq_le_rs
  have hrsUpperR : (((r * s : ℕ) : ℝ)) ≤ 4 * (K : ℝ) ^ 2 := by
    exact_mod_cast hrs_le_fourKsq
  have hMKsq : (M : ℝ) ^ 2 * (K : ℝ) ^ 2 ≤ 4 * X := by
    have hmul := mul_le_mul hyLowerR hyLowerR
      (by positivity) (by positivity)
    calc
      (M : ℝ) ^ 2 * (K : ℝ) ^ 2 =
          ((M : ℝ) * K) * ((M : ℝ) * K) := by ring
      _ ≤ (y : ℝ) * y := hmul
      _ = (y : ℝ) ^ 2 := by ring
      _ ≤ 4 * X := hXlo
  have hrsSqUpper : (((r * s : ℕ) : ℝ) ^ 2) ≤
      16 * (K : ℝ) ^ 4 := by
    calc
      (((r * s : ℕ) : ℝ) ^ 2) ≤ (4 * (K : ℝ) ^ 2) ^ 2 := by gcongr
      _ = 16 * (K : ℝ) ^ 4 := by ring
  have hdiffLower : 2 * (K : ℝ) ≤ ((s ^ 2 - r ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * K ≤ s ^ 2 - r ^ 2 by
      rw [Nat.sq_sub_sq]
      calc
        2 * K = (2 * K) * 1 := by omega
        _ ≤ (s + r) * (s - r) := by gcongr <;> omega)
  have hKMR : (K : ℝ) ≤ M := by exact_mod_cast hKM
  have hQlowerNumerator :
      (M : ℝ) * (((r * s : ℕ) : ℝ) ^ 2) ≤
        32 * X * ((s ^ 2 - r ^ 2 : ℕ) : ℝ) := by
    calc
      (M : ℝ) * (((r * s : ℕ) : ℝ) ^ 2) ≤
          (M : ℝ) * (16 * (K : ℝ) ^ 4) := by gcongr
      _ ≤ 16 * (M : ℝ) ^ 2 * (K : ℝ) ^ 3 := by
        have h := mul_le_mul_of_nonneg_left hKMR
          (by positivity : 0 ≤ 16 * (M : ℝ) * (K : ℝ) ^ 3)
        nlinarith
      _ ≤ 64 * X * (K : ℝ) := by
        have h := mul_le_mul_of_nonneg_right hMKsq
          (by positivity : 0 ≤ 16 * (K : ℝ))
        nlinarith
      _ ≤ 32 * X * ((s ^ 2 - r ^ 2 : ℕ) : ℝ) := by
        have h := mul_le_mul_of_nonneg_left hdiffLower
          (by positivity : 0 ≤ 32 * X)
        nlinarith
  have hQlower : (M : ℝ) ≤ 32 * Q := by
    dsimp only [Q, inverseSquareCentralCorrelationFrequency]
    rw [show 32 * (X * (((s : ℕ) ^ 2 - r ^ 2 : ℕ) : ℝ) /
        (((r * s : ℕ) : ℝ) ^ 2)) =
      (32 * X * (((s : ℕ) ^ 2 - r ^ 2 : ℕ) : ℝ)) /
        (((r * s : ℕ) : ℝ) ^ 2) by ring]
    exact (le_div_iff₀ hrsSqPos).2 hQlowerNumerator
  have hyUpperR : (y : ℝ) ≤ 8 * (M : ℝ) * K := by
    exact_mod_cast hxyUpper.le
  have hXupper : X ≤ 8 ^ 16 * (M : ℝ) ^ 16 * (K : ℝ) ^ 16 := by
    calc
      X ≤ (y : ℝ) ^ 16 := hXhi
      _ ≤ (8 * (M : ℝ) * K) ^ 16 :=
        pow_le_pow_left₀ (by positivity) hyUpperR 16
      _ = 8 ^ 16 * (M : ℝ) ^ 16 * (K : ℝ) ^ 16 := by ring
  have hdiffUpper : ((s ^ 2 - r ^ 2 : ℕ) : ℝ) ≤
      4 * (K : ℝ) ^ 2 := by
    exact_mod_cast (show s ^ 2 - r ^ 2 ≤ 4 * K ^ 2 by
      calc
        s ^ 2 - r ^ 2 ≤ s ^ 2 := Nat.sub_le _ _
        _ ≤ (2 * K) ^ 2 := by
          exact Nat.pow_le_pow_left hsBounds.2 2
        _ = 4 * K ^ 2 := by ring)
  have hdenLower : (K : ℝ) ^ 4 ≤ (((r * s : ℕ) : ℝ) ^ 2) := by
    calc
      (K : ℝ) ^ 4 = ((K : ℝ) ^ 2) ^ 2 := by ring
      _ ≤ (((r * s : ℕ) : ℝ)) ^ 2 := by gcongr
  have hupperNumerator : X * ((s ^ 2 - r ^ 2 : ℕ) : ℝ) ≤
      inverseSquareCentralFrequencyConstant * (M : ℝ) ^ 31 *
        (((r * s : ℕ) : ℝ) ^ 2) := by
    calc
      X * ((s ^ 2 - r ^ 2 : ℕ) : ℝ) ≤
          (8 ^ 16 * (M : ℝ) ^ 16 * (K : ℝ) ^ 16) *
            (4 * (K : ℝ) ^ 2) := by gcongr
      _ = (4 * 8 ^ 16) * (M : ℝ) ^ 16 * (K : ℝ) ^ 14 *
          (K : ℝ) ^ 4 := by ring
      _ ≤ (4 * 8 ^ 16) * (M : ℝ) ^ 16 * (M : ℝ) ^ 15 *
          (K : ℝ) ^ 4 := by
        have hp : (K : ℝ) ^ 14 ≤ (M : ℝ) ^ 15 := by
          calc
            (K : ℝ) ^ 14 ≤ (M : ℝ) ^ 14 := by gcongr
            _ ≤ (M : ℝ) ^ 15 :=
              pow_le_pow_right₀ (by exact_mod_cast hM) (by omega)
        gcongr
      _ = inverseSquareCentralFrequencyConstant * (M : ℝ) ^ 31 *
          (K : ℝ) ^ 4 := by
        unfold inverseSquareCentralFrequencyConstant inverseSquareFrequencyConstant
        ring
      _ ≤ inverseSquareCentralFrequencyConstant * (M : ℝ) ^ 31 *
          (((r * s : ℕ) : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hdenLower (by
          unfold inverseSquareCentralFrequencyConstant inverseSquareFrequencyConstant
          positivity)
  have hQupper : Q ≤ inverseSquareCentralFrequencyConstant * (M : ℝ) ^ 31 := by
    dsimp only [Q, inverseSquareCentralCorrelationFrequency]
    exact (div_le_iff₀ hrsSqPos).2 (by simpa [mul_assoc] using hupperNumerator)
  exact ⟨hab, haM, hbM, hQpos, hQlower, hQupper⟩

/-- UniforminverseSquareCentral-range off-diagonal correlation estimate. -/
theorem norm_inverseSquareCentral_cutoff_correlation_le
    {X : ℝ} {x y M K r s C : ℕ}
    (hX : 0 < X)
    (hM : 1 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hr : r ∈ Finset.Ioc K (2 * K))
    (hs : s ∈ Finset.Ioc K (2 * K)) (hrs : r < s)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hsize : inverseSquareCentralCorrelationSizeCondition M)
    (hC : 2 ≤ C) (hbaseCap : baseShift M ≤ M / C) :
    ‖∑ m ∈ Finset.Ioc M (2 * M),
      inverseSquareCutoffWeight X x y m s *
          conj (inverseSquareCutoffWeight X x y m r)‖ ≤
      cappedInverseSquareCorrelationEnvelope
        (inverseSquareCentralCorrelationFrequency X r s) M C := by
  let a := inverseSquareCentralCorrelationLower x M r s
  let b := inverseSquareCentralCorrelationUpper y M r s
  let N := inverseSquareCentralCorrelationLength x y M r s
  let Q := inverseSquareCentralCorrelationFrequency X r s
  have hQpos : 0 < Q := by
    dsimp only [Q, inverseSquareCentralCorrelationFrequency]
    have hdiff : 0 < s ^ 2 - r ^ 2 :=
      Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hrs (by norm_num))
    have hrpos : 0 < r := hK.trans (Finset.mem_Ioc.mp hr).1
    have hspos : 0 < s := hK.trans (Finset.mem_Ioc.mp hs).1
    have hden : (0 : ℝ) < (((r * s : ℕ) : ℝ) ^ 2) := by
      exact_mod_cast pow_pos (Nat.mul_pos hrpos hspos) 2
    exact div_pos (mul_pos hX (by exact_mod_cast hdiff)) hden
  by_cases hN : N = 0
  · have hba : b ≤ a := by
      dsimp only [N,inverseSquareCentralCorrelationLength] at hN
      omega
    rw [norm_sum_inverseSquareCutoffWeight_correlation_comm X x y M (2 * M) s r]
    rw [sum_inverseSquareCutoffWeight_correlation_eq_common X
      (hK.trans (Finset.mem_Ioc.mp hr).1)
      (hK.trans (Finset.mem_Ioc.mp hs).1)]
    unfold commonProductInterval
    have hempty : Finset.Ioc a b = ∅ := Finset.Ioc_eq_empty (by omega)
    change ‖∑ m ∈ Finset.Ioc a b,
      inverseSquareWeight X (m * r) * conj (inverseSquareWeight X (m * s))‖ ≤ _
    rw [hempty]
    simp only [Finset.sum_empty, norm_zero]
    change 0 ≤ cappedInverseSquareCorrelationEnvelope Q M C
    have hterm : 0 ≤ cappedTerminalMajorant Q M C :=
      cappedTerminalMajorant_nonneg hQpos
    have hmoment : 0 ≤ cappedInverseSquareMomentEnvelope Q M C := by
      unfold cappedInverseSquareMomentEnvelope
      apply mul_nonneg (HigherDerivative.vdcMomentConstant_pos 32).le
      exact add_nonneg (add_nonneg (by positivity) (by positivity)) hterm
    unfold cappedInverseSquareCorrelationEnvelope
    exact add_nonneg (by positivity)
      (mul_nonneg (by positivity) (Real.rpow_nonneg hmoment _))
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hscale := inverseSquareCentralCorrelation_scale_bounds hM hK hKM hr hs hrs
      hXlo hXhi hyx hNpos
    rcases hscale with ⟨hab, hMa, hbM, _hQpos, _hQlo, hQhi⟩
    have hbase := baseShift_predicate_of_frequency_upper
      hQpos.le hM hQhi hsize
    rw [norm_sum_inverseSquareCutoffWeight_correlation_comm X x y M (2 * M) s r]
    rw [sum_inverseSquareCutoffWeight_correlation_eq_phase X
      (hK.trans (Finset.mem_Ioc.mp hr).1)
      (hK.trans (Finset.mem_Ioc.mp hs).1) hrs.le]
    change ‖inverseSquareProductIntervalSum Q 1 a b‖ ≤
      cappedInverseSquareCorrelationEnvelope Q M C
    exact norm_inverseSquareProductIntervalSum_le_capped
      hQpos hC hM hbase hbaseCap hab hMa hbM

/-- Cauchy--Schwarz energy estimate with theinverseSquareCentral-range correlation
envelope. -/
theorem norm_inverseSquareCentral_inverseSquareBilinearBlock_sq_le_energy
    {X : ℝ} {x y M K C : ℕ} (a b : ℕ → ℂ)
    (hX : 0 < X)
    (hM : 1 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hsize : inverseSquareCentralCorrelationSizeCondition M)
    (hC : 2 ≤ C) (hbaseCap : baseShift M ≤ M / C) (B : ℝ) (hB : 0 ≤ B)
    (hcorr : ∀ r ∈ Finset.Ioc K (2 * K), ∀ s ∈ Finset.Ioc K (2 * K),
      r < s →
        cappedInverseSquareCorrelationEnvelope
          (inverseSquareCentralCorrelationFrequency X r s) M C ≤ B) :
    ‖inverseSquareBilinearBlock X x y M (2 * M) K (2 * K) a b‖ ^ 2 ≤
      (∑ m ∈ Finset.Ioc M (2 * M), ‖a m‖ ^ 2) *
        ((M : ℝ) * (∑ k ∈ Finset.Ioc K (2 * K), ‖b k‖ ^ 2) +
          B *
            (∑ k ∈ Finset.Ioc K (2 * K), ‖b k‖) ^ 2) := by
  let t := Finset.Ioc K (2 * K)
  have hbase := norm_inverseSquareBilinearBlock_sq_le_correlation
    X x y M (2 * M) K (2 * K) a b
  have hpair :
      (∑ r ∈ t, ∑ s ∈ t,
        ‖b r‖ * ‖b s‖ *
          ‖∑ m ∈ Finset.Ioc M (2 * M),
          inverseSquareCutoffWeight X x y m s *
              conj (inverseSquareCutoffWeight X x y m r)‖) ≤
        (M : ℝ) * (∑ k ∈ t, ‖b k‖ ^ 2) +
          B * (∑ k ∈ t, ‖b k‖) ^ 2 := by
    calc
      (∑ r ∈ t, ∑ s ∈ t,
        ‖b r‖ * ‖b s‖ *
          ‖∑ m ∈ Finset.Ioc M (2 * M),
          inverseSquareCutoffWeight X x y m s *
              conj (inverseSquareCutoffWeight X x y m r)‖) ≤
        ∑ r ∈ t, ∑ s ∈ t,
          ((if r = s then ‖b r‖ ^ 2 * (M : ℝ) else 0) +
            ‖b r‖ * ‖b s‖ * B) := by
          apply Finset.sum_le_sum
          intro r hr
          apply Finset.sum_le_sum
          intro s hs
          by_cases hrs : r = s
          · subst s
            have hdiag := norm_sum_inverseSquareCutoffWeight_diagonal_le
              X x y M (2 * M) r
            have hdiag' :
                ‖∑ m ∈ Finset.Ioc M (2 * M),
                inverseSquareCutoffWeight X x y m r *
                    conj (inverseSquareCutoffWeight X x y m r)‖ ≤ (M : ℝ) := by
              convert hdiag using 1 <;> norm_num
              omega
            simp only [if_pos rfl]
            have hmain : ‖b r‖ * ‖b r‖ *
                ‖∑ m ∈ Finset.Ioc M (2 * M),
                inverseSquareCutoffWeight X x y m r *
                    conj (inverseSquareCutoffWeight X x y m r)‖ ≤
                ‖b r‖ ^ 2 * (M : ℝ) := by
              calc
                _ ≤ ‖b r‖ * ‖b r‖ * (M : ℝ) := by gcongr
                _ = ‖b r‖ ^ 2 * (M : ℝ) := by ring
            exact hmain.trans (le_add_of_nonneg_right (by positivity))
          · simp only [if_neg hrs, zero_add]
            rcases lt_or_gt_of_ne hrs with hrslt | hsrlt
            · have hoff := norm_inverseSquareCentral_cutoff_correlation_le hX hM hK hKM
                hr hs hrslt hXlo hXhi hyx hsize hC hbaseCap
              exact mul_le_mul_of_nonneg_left
                (hoff.trans (hcorr r hr s hs hrslt)) (by positivity)
            · rw [norm_sum_inverseSquareCutoffWeight_correlation_comm
                X x y M (2 * M) s r]
              have hoff := norm_inverseSquareCentral_cutoff_correlation_le hX hM hK hKM
                hs hr hsrlt hXlo hXhi hyx hsize hC hbaseCap
              exact mul_le_mul_of_nonneg_left
                (hoff.trans (hcorr s hs r hr hsrlt)) (by positivity)
      _ = (M : ℝ) * (∑ k ∈ t, ‖b k‖ ^ 2) +
          B * (∑ k ∈ t, ‖b k‖) ^ 2 := by
        simp_rw [Finset.sum_add_distrib]
        have hdiag : (∑ r ∈ t, ∑ s ∈ t,
            if r = s then ‖b r‖ ^ 2 * (M : ℝ) else 0) =
            (M : ℝ) * (∑ k ∈ t, ‖b k‖ ^ 2) := by
          calc
            _ = ∑ r ∈ t, ‖b r‖ ^ 2 * (M : ℝ) := by
              apply Finset.sum_congr rfl
              intro r hr
              simp [hr]
            _ = (M : ℝ) * (∑ k ∈ t, ‖b k‖ ^ 2) := by
              rw [← Finset.sum_mul]
              ring
        rw [hdiag]
        have hoff : (∑ r ∈ t, ∑ s ∈ t,
            ‖b r‖ * ‖b s‖ * B) =
            B * (∑ k ∈ t, ‖b k‖) ^ 2 := by
          symm
          rw [show B * (∑ k ∈ t, ‖b k‖) ^ 2 =
            (∑ k ∈ t, ‖b k‖) ^ 2 * B by ring]
          rw [pow_two, Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum, Finset.sum_mul]
        rw [hoff]
  apply hbase.trans
  exact mul_le_mul_of_nonneg_left hpair
    (Finset.sum_nonneg fun m hm ↦ sq_nonneg _)

end

end InverseSquareCentralCorrelation
end Erdos378
