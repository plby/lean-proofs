/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.AdaptiveShifts
import ErdosProblems.Erdos378.VaughanReciprocalBlocks

/-!
# Uniform correlations in the central range

Here the original reciprocal frequency may be as large as the sixteenth power of
the prime-window scale.  The product structure of an off-diagonal Vaughan
correlation reduces it to a frequency between a quadratic lower bound and a
thirty-first-power upper bound in the longer dyadic variable.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos378
namespace CentralCorrelation

open PrimeReciprocal
open BilinearReciprocal
open VaughanReciprocalBlocks
open AdaptiveShifts

noncomputable section

def centralFrequencyConstant : ℝ := 8 ^ 16

lemma centralFrequencyConstant_pos : 0 < centralFrequencyConstant := by
  unfold centralFrequencyConstant
  positivity

def centralCorrelationSizeCondition (M : ℕ) : Prop :=
  2 * centralFrequencyConstant * ((33).factorial : ℝ) *
      (logarithmicSafety M) ^ 32 ≤ M

lemma baseShift_predicate_of_frequency_upper
    {Q : ℝ} (hQ : 0 ≤ Q) {M : ℕ} (hM : 1 ≤ M)
    (hQupper : Q ≤ centralFrequencyConstant * (M : ℝ) ^ 31)
    (hsize : centralCorrelationSizeCondition M) :
    adaptiveShiftPredicate Q M (baseShift M) := by
  have hbaseNat := baseShift_pow_thirtytwo_le_sq (Nat.zero_lt_of_lt hM)
  have hbase : (baseShift M : ℝ) ^ 32 ≤ (M : ℝ) ^ 2 := by
    exact_mod_cast hbaseNat
  have hS0 : 0 ≤ logarithmicSafety M := (logarithmicSafety_pos hM).le
  have hC0 : 0 ≤ centralFrequencyConstant := centralFrequencyConstant_pos.le
  unfold adaptiveShiftPredicate
  calc
    2 * Q * ((33).factorial : ℝ) * (baseShift M : ℝ) ^ 32 *
        logarithmicSafety M ^ 32 ≤
      2 * (centralFrequencyConstant * (M : ℝ) ^ 31) *
        ((33).factorial : ℝ) * (M : ℝ) ^ 2 *
          logarithmicSafety M ^ 32 := by
      gcongr
    _ = (2 * centralFrequencyConstant * ((33).factorial : ℝ) *
          logarithmicSafety M ^ 32) * (M : ℝ) ^ 33 := by ring
    _ ≤ (M : ℝ) * (M : ℝ) ^ 33 := by
      apply mul_le_mul_of_nonneg_right hsize
      positivity
    _ = (M : ℝ) ^ 34 := by ring

def centralCorrelationLower (x M r s : ℕ) : ℕ :=
  max M (max (x / r) (x / s))

def centralCorrelationUpper (y M r s : ℕ) : ℕ :=
  min (2 * M) (min (y / r) (y / s))

def centralCorrelationLength (x y M r s : ℕ) : ℕ :=
  centralCorrelationUpper y M r s - centralCorrelationLower x M r s

def centralCorrelationFrequency (X : ℝ) (r s : ℕ) : ℝ :=
  X * ((s - r : ℕ) : ℝ) / ((r * s : ℕ) : ℝ)

/-- Scale bounds for a nonempty off-diagonal correlation. -/
lemma centralCorrelation_scale_bounds
    {X : ℝ} {x y M K r s : ℕ}
    (hM : 1 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hr : r ∈ Finset.Ioc K (2 * K))
    (hs : s ∈ Finset.Ioc K (2 * K)) (hrs : r < s)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hNpos : 0 < centralCorrelationLength x y M r s) :
    let a := centralCorrelationLower x M r s
    let b := centralCorrelationUpper y M r s
    let Q := centralCorrelationFrequency X r s
    a < b ∧ M ≤ a ∧ b ≤ 2 * M ∧ 0 < Q ∧
      (M : ℝ) ^ 2 ≤ 16 * Q ∧
      Q ≤ centralFrequencyConstant * (M : ℝ) ^ 31 := by
  let a := centralCorrelationLower x M r s
  let b := centralCorrelationUpper y M r s
  let d := s - r
  let Q := centralCorrelationFrequency X r s
  have hrBounds := Finset.mem_Ioc.mp hr
  have hsBounds := Finset.mem_Ioc.mp hs
  have hrPos : 0 < r := hK.trans hrBounds.1
  have hsPos : 0 < s := hK.trans hsBounds.1
  have hdPos : 0 < d := by dsimp only [d]; omega
  have hdK : d ≤ K := by dsimp only [d]; omega
  have hdM : d ≤ M := hdK.trans hKM
  have haM : M ≤ a := by
    dsimp only [a, centralCorrelationLower]
    exact Nat.le_max_left _ _
  have hbM : b ≤ 2 * M := by
    dsimp only [b, centralCorrelationUpper]
    exact Nat.min_le_left _ _
  have hab : a < b := by
    dsimp only [centralCorrelationLength] at hNpos
    omega
  have hmMem : a + 1 ∈ commonProductInterval x y M (2 * M) r s := by
    rw [commonProductInterval, Finset.mem_Ioc]
    simpa only [a, b, centralCorrelationLower, centralCorrelationUpper] using
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
  have hQpos : 0 < Q := by
    dsimp only [Q, centralCorrelationFrequency]
    positivity
  have hKsq_le_rs : K ^ 2 ≤ r * s := by nlinarith
  have hrs_le_fourKsq : r * s ≤ 4 * K ^ 2 := by nlinarith
  have hyLowerR : (M : ℝ) * K ≤ y := by exact_mod_cast hyLower.le
  have hKsqR : (K : ℝ) ^ 2 ≤ ((r * s : ℕ) : ℝ) := by
    exact_mod_cast hKsq_le_rs
  have hrsUpperR : (((r * s : ℕ) : ℝ)) ≤ 4 * (K : ℝ) ^ 2 := by
    exact_mod_cast hrs_le_fourKsq
  have hQlowerD : (M : ℝ) ^ 2 * d ≤ 16 * Q := by
    dsimp only [Q, centralCorrelationFrequency]
    rw [show 16 * (X * (d : ℝ) / ((r * s : ℕ) : ℝ)) =
      (16 * X * (d : ℝ)) / ((r * s : ℕ) : ℝ) by ring]
    rw [le_div_iff₀ hrsPos]
    have hbase : (M : ℝ) ^ 2 * ((r * s : ℕ) : ℝ) ≤ 16 * X := by
      have hMK : (M : ℝ) ^ 2 * (K : ℝ) ^ 2 ≤ (y : ℝ) ^ 2 := by
        have hmul := mul_le_mul hyLowerR hyLowerR
          (by positivity) (by positivity)
        calc
          (M : ℝ) ^ 2 * (K : ℝ) ^ 2 =
              ((M : ℝ) * K) * ((M : ℝ) * K) := by ring
          _ ≤ (y : ℝ) * y := hmul
          _ = (y : ℝ) ^ 2 := by ring
      calc
        (M : ℝ) ^ 2 * ((r * s : ℕ) : ℝ) ≤
            (M : ℝ) ^ 2 * (4 * (K : ℝ) ^ 2) := by gcongr
        _ ≤ 4 * (y : ℝ) ^ 2 := by nlinarith
        _ ≤ 16 * X := by nlinarith
    calc
      (M : ℝ) ^ 2 * (d : ℝ) * ((r * s : ℕ) : ℝ) =
          ((M : ℝ) ^ 2 * ((r * s : ℕ) : ℝ)) * d := by ring
      _ ≤ (16 * X) * d := by gcongr
      _ = 16 * X * (d : ℝ) := by ring
  have hQlower : (M : ℝ) ^ 2 ≤ 16 * Q := by
    have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hdPos
    exact (by
      calc
        (M : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 * d := by
          rw [le_mul_iff_one_le_right (by positivity)]
          exact hdOne
        _ ≤ 16 * Q := hQlowerD)
  have hyUpperR : (y : ℝ) ≤ 8 * (M : ℝ) * K := by
    exact_mod_cast hxyUpper.le
  have hXupper : X ≤ 8 ^ 16 * (M : ℝ) ^ 16 * (K : ℝ) ^ 16 := by
    calc
      X ≤ (y : ℝ) ^ 16 := hXhi
      _ ≤ (8 * (M : ℝ) * K) ^ 16 :=
        pow_le_pow_left₀ (by positivity) hyUpperR 16
      _ = 8 ^ 16 * (M : ℝ) ^ 16 * (K : ℝ) ^ 16 := by ring
  have hdR : (d : ℝ) ≤ K := by exact_mod_cast hdK
  have hKMR : (K : ℝ) ≤ M := by exact_mod_cast hKM
  have hupperNumerator : X * (d : ℝ) ≤
      (8 ^ 16 * (M : ℝ) ^ 31) * ((r * s : ℕ) : ℝ) := by
    calc
      X * (d : ℝ) ≤
          (8 ^ 16 * (M : ℝ) ^ 16 * (K : ℝ) ^ 16) * K := by gcongr
      _ = 8 ^ 16 * (M : ℝ) ^ 16 * (K : ℝ) ^ 15 *
          (K : ℝ) ^ 2 := by ring
      _ ≤ 8 ^ 16 * (M : ℝ) ^ 16 * (M : ℝ) ^ 15 *
          (K : ℝ) ^ 2 := by
        have hp := pow_le_pow_left₀ (by positivity) hKMR 15
        gcongr
      _ = (8 ^ 16 * (M : ℝ) ^ 31) * (K : ℝ) ^ 2 := by ring
      _ ≤ (8 ^ 16 * (M : ℝ) ^ 31) * ((r * s : ℕ) : ℝ) := by
        gcongr
  have hQupper : Q ≤ centralFrequencyConstant * (M : ℝ) ^ 31 := by
    dsimp only [Q, centralCorrelationFrequency]
    rw [div_le_iff₀ hrsPos]
    simpa only [centralFrequencyConstant] using hupperNumerator
  exact ⟨hab, haM, hbM, hQpos, hQlower, hQupper⟩

/-- Uniform central-range off-diagonal correlation estimate. -/
theorem norm_central_cutoff_correlation_le
    {X : ℝ} {x y M K r s : ℕ}
    (hM : 1 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hr : r ∈ Finset.Ioc K (2 * K))
    (hs : s ∈ Finset.Ioc K (2 * K)) (hrs : r < s)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hsize : centralCorrelationSizeCondition M) :
    ‖∑ m ∈ Finset.Ioc M (2 * M),
        reciprocalCutoffWeight X x y m s *
          conj (reciprocalCutoffWeight X x y m r)‖ ≤
      adaptiveCorrelationEnvelope M := by
  let a := centralCorrelationLower x M r s
  let b := centralCorrelationUpper y M r s
  let N := centralCorrelationLength x y M r s
  by_cases hN : N = 0
  · have hba : b ≤ a := by
      dsimp only [N, centralCorrelationLength] at hN
      omega
    rw [norm_sum_reciprocalCutoffWeight_correlation_comm X x y M (2 * M) s r]
    rw [sum_reciprocalCutoffWeight_correlation_eq_common X
      (hK.trans (Finset.mem_Ioc.mp hr).1)
      (hK.trans (Finset.mem_Ioc.mp hs).1)]
    unfold commonProductInterval
    have hempty : Finset.Ioc a b = ∅ := Finset.Ioc_eq_empty (by omega)
    change ‖∑ m ∈ Finset.Ioc a b,
      reciprocalWeight X (m * r) * conj (reciprocalWeight X (m * s))‖ ≤ _
    rw [hempty]
    simpa using adaptiveCorrelationEnvelope_nonneg hM
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    have hscale := centralCorrelation_scale_bounds hM hK hKM hr hs hrs
      hXlo hXhi hyx hNpos
    rcases hscale with ⟨hab, hMa, hbM, hQpos, hQlo, hQhi⟩
    let Q := centralCorrelationFrequency X r s
    have hbase := baseShift_predicate_of_frequency_upper
      hQpos.le hM hQhi hsize
    rw [norm_sum_reciprocalCutoffWeight_correlation_comm X x y M (2 * M) s r]
    rw [sum_reciprocalCutoffWeight_correlation_eq_phase X
      (hK.trans (Finset.mem_Ioc.mp hr).1)
      (hK.trans (Finset.mem_Ioc.mp hs).1) hrs.le]
    exact norm_reciprocalProductIntervalSum_le_adaptive
      hQpos hM hQlo hbase hab hMa hbM

/-- Cauchy--Schwarz energy estimate with the central-range correlation
envelope. -/
theorem norm_central_reciprocalBilinearBlock_sq_le_energy
    {X : ℝ} {x y M K : ℕ} (a b : ℕ → ℂ)
    (hM : 1 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hsize : centralCorrelationSizeCondition M) :
    ‖reciprocalBilinearBlock X x y M (2 * M) K (2 * K) a b‖ ^ 2 ≤
      (∑ m ∈ Finset.Ioc M (2 * M), ‖a m‖ ^ 2) *
        ((M : ℝ) * (∑ k ∈ Finset.Ioc K (2 * K), ‖b k‖ ^ 2) +
          adaptiveCorrelationEnvelope M *
            (∑ k ∈ Finset.Ioc K (2 * K), ‖b k‖) ^ 2) := by
  let t := Finset.Ioc K (2 * K)
  let B := adaptiveCorrelationEnvelope M
  have hB : 0 ≤ B := adaptiveCorrelationEnvelope_nonneg hM
  have hbase := norm_reciprocalBilinearBlock_sq_le_correlation
    X x y M (2 * M) K (2 * K) a b
  have hpair :
      (∑ r ∈ t, ∑ s ∈ t,
        ‖b r‖ * ‖b s‖ *
          ‖∑ m ∈ Finset.Ioc M (2 * M),
            reciprocalCutoffWeight X x y m s *
              conj (reciprocalCutoffWeight X x y m r)‖) ≤
        (M : ℝ) * (∑ k ∈ t, ‖b k‖ ^ 2) +
          B * (∑ k ∈ t, ‖b k‖) ^ 2 := by
    calc
      (∑ r ∈ t, ∑ s ∈ t,
        ‖b r‖ * ‖b s‖ *
          ‖∑ m ∈ Finset.Ioc M (2 * M),
            reciprocalCutoffWeight X x y m s *
              conj (reciprocalCutoffWeight X x y m r)‖) ≤
        ∑ r ∈ t, ∑ s ∈ t,
          ((if r = s then ‖b r‖ ^ 2 * (M : ℝ) else 0) +
            ‖b r‖ * ‖b s‖ * B) := by
          apply Finset.sum_le_sum
          intro r hr
          apply Finset.sum_le_sum
          intro s hs
          by_cases hrs : r = s
          · subst s
            have hdiag := norm_sum_reciprocalCutoffWeight_diagonal_le
              X x y M (2 * M) r
            have hdiag' :
                ‖∑ m ∈ Finset.Ioc M (2 * M),
                  reciprocalCutoffWeight X x y m r *
                    conj (reciprocalCutoffWeight X x y m r)‖ ≤ (M : ℝ) := by
              convert hdiag using 1 <;> norm_num
              omega
            simp only [if_pos rfl]
            have hmain : ‖b r‖ * ‖b r‖ *
                ‖∑ m ∈ Finset.Ioc M (2 * M),
                  reciprocalCutoffWeight X x y m r *
                    conj (reciprocalCutoffWeight X x y m r)‖ ≤
                ‖b r‖ ^ 2 * (M : ℝ) := by
              calc
                _ ≤ ‖b r‖ * ‖b r‖ * (M : ℝ) := by gcongr
                _ = ‖b r‖ ^ 2 * (M : ℝ) := by ring
            exact hmain.trans (le_add_of_nonneg_right (by positivity))
          · simp only [if_neg hrs, zero_add]
            rcases lt_or_gt_of_ne hrs with hrslt | hsrlt
            · have hoff := norm_central_cutoff_correlation_le hM hK hKM
                hr hs hrslt hXlo hXhi hyx hsize
              exact mul_le_mul_of_nonneg_left hoff (by positivity)
            · rw [norm_sum_reciprocalCutoffWeight_correlation_comm
                X x y M (2 * M) s r]
              have hoff := norm_central_cutoff_correlation_le hM hK hKM
                hs hr hsrlt hXlo hXhi hyx hsize
              exact mul_le_mul_of_nonneg_left hoff (by positivity)
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

end CentralCorrelation
end Erdos378
