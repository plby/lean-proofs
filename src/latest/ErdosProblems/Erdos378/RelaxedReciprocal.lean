/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.HighIndexCutoffs
import ErdosProblems.Erdos378.CentralCorrelation
import ErdosProblems.Erdos378.CentralProductInterval

/-!
# Reciprocal sums with a logarithmically relaxed lower frequency

The central estimate applies once the reciprocal frequency is quadratic in
the interval scale.  In Section 5b of Granville--Ramaré the frequency may be
smaller by a logarithmic square.  In that complementary range the elementary
first-derivative estimate is stronger; this file joins the two bounds.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos378
namespace RelaxedReciprocal

open PrimeReciprocal
open BilinearReciprocal
open VaughanReciprocalBlocks
open ReciprocalExponential
open AdaptiveShifts
open CentralCorrelation
open CentralOneDimensional

noncomputable section

/-- A deliberately generous envelope for the elementary first-derivative
range.  Its exact numerical constant is immaterial; only its fourth-power
dependence on the relaxation parameter is used later. -/
def firstDerivativeEnvelope (H : ℕ) : ℝ :=
  100000 * ((H : ℝ) ^ 4 + 1)

lemma firstDerivativeEnvelope_nonneg (H : ℕ) :
    0 ≤ firstDerivativeEnvelope H := by
  unfold firstDerivativeEnvelope
  positivity

def relaxedCorrelationEnvelope (H M : ℕ) : ℝ :=
  adaptiveCorrelationEnvelope M + firstDerivativeEnvelope H

lemma relaxedCorrelationEnvelope_nonneg (H : ℕ) {M : ℕ}
    (hM : 1 ≤ M) : 0 ≤ relaxedCorrelationEnvelope H M := by
  unfold relaxedCorrelationEnvelope
  exact add_nonneg (adaptiveCorrelationEnvelope_nonneg hM)
    (firstDerivativeEnvelope_nonneg H)

private lemma norm_reciprocalProductInterval_le_card
    (Q : ℝ) (a b : ℕ) :
    ‖reciprocalProductIntervalSum Q 1 a b‖ ≤ (b - a : ℕ) := by
  unfold reciprocalProductIntervalSum
  calc
    ‖∑ r ∈ Finset.Ioc a b, reciprocalWeight Q (1 * r)‖ ≤
        ∑ r ∈ Finset.Ioc a b, ‖reciprocalWeight Q (1 * r)‖ :=
      norm_sum_le _ _
    _ = (Finset.Ioc a b).card := by simp only [norm_reciprocalWeight]; simp
    _ = (b - a : ℕ) := by simp

/-- The elementary first-derivative estimate, normalized to the relaxed
quadratic lower bound used below. -/
lemma norm_reciprocalProductInterval_le_firstDerivativeEnvelope
    {Q : ℝ} (hQ : 0 < Q) {H M a b : ℕ}
    (hH : 1 ≤ H) (hM : 1 ≤ M) (hMa : M ≤ a) (hbM : b ≤ 2 * M)
    (hQlo : (M : ℝ) ^ 2 ≤ 16 * (H : ℝ) ^ 2 * Q)
    (hsmall : Q / ((a + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 2) :
    ‖reciprocalProductIntervalSum Q 1 a b‖ ≤
      firstDerivativeEnvelope H := by
  by_cases hN : 2 ≤ b - a
  · rw [reciprocalProductIntervalSum_eq_phase Q (by norm_num : 0 < (1 : ℕ))]
    simp only [Nat.cast_one, div_one]
    have hbase := norm_sum_e_reciprocalPhase_le Q
      hQ (show 0 < a + 1 by omega) hN hsmall
    have hMpos : (0 : ℝ) < M := by positivity
    have hHpos : (0 : ℝ) < H := by positivity
    have hQlower : (M : ℝ) ^ 2 /
        (16 * (H : ℝ) ^ 2) ≤ Q := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * (H : ℝ) ^ 2)]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hQlo
    have hbOne : (b + 1 : ℕ) ≤ 3 * M := by omega
    have hbOneR : ((b + 1 : ℕ) : ℝ) ≤ 3 * M := by exact_mod_cast hbOne
    have hratio : 1 / (4 * (Q / (((a + 1 + (b - a) : ℕ) : ℝ) ^ 2))) ≤
        36 * (H : ℝ) ^ 2 := by
      have hab : a ≤ b := by omega
      have hend : a + 1 + (b - a) = b + 1 := by omega
      rw [hend]
      have hdenpos : 0 < 4 * (Q / (((b + 1 : ℕ) : ℝ) ^ 2)) := by positivity
      rw [one_div_le hdenpos (by positivity : (0 : ℝ) < 36 * (H : ℝ) ^ 2)]
      have hbSq : (((b + 1 : ℕ) : ℝ) ^ 2) ≤ 9 * (M : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (((b + 1 : ℕ) : ℝ) - 3 * M)]
      have hQscaled : (M : ℝ) ^ 2 ≤
          16 * (H : ℝ) ^ 2 * Q := hQlo
      field_simp
      nlinarith
    have hratio0 : 0 ≤
        1 / (4 * (Q / (((a + 1 + (b - a) : ℕ) : ℝ) ^ 2))) := by positivity
    calc
      ‖∑ i ∈ Finset.range (b - a),
          ReciprocalExponential.e (reciprocalPhase Q (a + 1) i)‖ ≤
          1 + 2 * (1 / (4 * (Q /
            (((a + 1 + (b - a) : ℕ) : ℝ) ^ 2)))) +
            8 * (1 / (4 * (Q /
              (((a + 1 + (b - a) : ℕ) : ℝ) ^ 2)))) ^ 2 := hbase
      _ ≤ 1 + 2 * (36 * (H : ℝ) ^ 2) +
          8 * (36 * (H : ℝ) ^ 2) ^ 2 := by gcongr
      _ ≤ firstDerivativeEnvelope H := by
        unfold firstDerivativeEnvelope
        have hHone : (1 : ℝ) ≤ H := by exact_mod_cast hH
        nlinarith [sq_nonneg ((H : ℝ) ^ 2 - 1)]
  · have hcard : b - a ≤ 1 := by omega
    exact (norm_reciprocalProductInterval_le_card Q a b).trans <| by
      calc
        ((b - a : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hcard
        _ ≤ firstDerivativeEnvelope H := by
          unfold firstDerivativeEnvelope
          nlinarith [sq_nonneg ((H : ℝ) ^ 2)]

/-- Uniform interval cancellation when the quadratic frequency lower bound
is relaxed by `H²`. -/
theorem norm_reciprocalProductIntervalSum_le_relaxed
    {Q : ℝ} (hQ : 0 < Q) {H M a b : ℕ}
    (hH : 1 ≤ H) (hM : 1 ≤ M)
    (hQlo : (M : ℝ) ^ 2 ≤ 16 * (H : ℝ) ^ 2 * Q)
    (hQhi : Q ≤ centralFrequencyConstant * (M : ℝ) ^ 31)
    (hsize : centralCorrelationSizeCondition M)
    (hab : a < b) (hMa : M ≤ a) (hbM : b ≤ 2 * M) :
    ‖reciprocalProductIntervalSum Q 1 a b‖ ≤
      relaxedCorrelationEnvelope H M := by
  by_cases hsmall : Q / ((a + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 2
  · exact (norm_reciprocalProductInterval_le_firstDerivativeEnvelope
      hQ hH hM hMa hbM hQlo hsmall).trans
        (le_add_of_nonneg_left (adaptiveCorrelationEnvelope_nonneg hM))
  · have hQcentral : (M : ℝ) ^ 2 ≤ 16 * Q := by
      have hMaR : (M : ℝ) ≤ (a + 1 : ℕ) := by exact_mod_cast (hMa.trans (by omega))
      have hsq : (M : ℝ) ^ 2 ≤ ((a + 1 : ℕ) : ℝ) ^ 2 := by gcongr
      have hlarge : ((a + 1 : ℕ) : ℝ) ^ 2 / 2 < Q := by
        have hden : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) ^ 2 := by positivity
        have hsmall' : (1 / 2 : ℝ) <
            Q / ((a + 1 : ℕ) : ℝ) ^ 2 := lt_of_not_ge hsmall
        have := (lt_div_iff₀ hden).mp hsmall'
        nlinarith
      nlinarith
    have hbase := baseShift_predicate_of_frequency_upper hQ.le hM hQhi hsize
    exact (norm_reciprocalProductIntervalSum_le_adaptive
      hQ hM hQcentral hbase hab hMa hbM).trans
        (le_add_of_nonneg_right (firstDerivativeEnvelope_nonneg H))

/-- Scale bounds for an off-diagonal Vaughan correlation when the original
frequency is allowed to be smaller by `H²`. -/
lemma relaxedCorrelation_scale_bounds
    {X : ℝ} {H x y M K r s : ℕ}
    (hH : 1 ≤ H) (hM : 1 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hr : r ∈ Finset.Ioc K (2 * K))
    (hs : s ∈ Finset.Ioc K (2 * K)) (hrs : r < s)
    (hXlo : (y : ℝ) ^ 2 ≤ 4 * (H : ℝ) ^ 2 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hNpos : 0 < centralCorrelationLength x y M r s) :
    let a := centralCorrelationLower x M r s
    let b := centralCorrelationUpper y M r s
    let Q := centralCorrelationFrequency X r s
    a < b ∧ M ≤ a ∧ b ≤ 2 * M ∧ 0 < Q ∧
      (M : ℝ) ^ 2 ≤ 16 * (H : ℝ) ^ 2 * Q ∧
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
  have haM : M ≤ a := Nat.le_max_left _ _
  have hbM : b ≤ 2 * M := Nat.min_le_left _ _
  have hab : a < b := by
    dsimp only [centralCorrelationLength] at hNpos
    omega
  have hmMem : a + 1 ∈ commonProductInterval x y M (2 * M) r s := by
    rw [commonProductInterval, Finset.mem_Ioc]
    simpa only [a, b, centralCorrelationLower, centralCorrelationUpper] using
      (show a < a + 1 ∧ a + 1 ≤ b by omega)
  rcases (mem_commonProductInterval_iff hrPos hsPos).mp hmMem with
    ⟨hmIoc, hmr, _hms⟩
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
    have hHpos : (0 : ℝ) < H := by positivity
    nlinarith [sq_pos_of_pos hyPos]
  have hrsPos : (0 : ℝ) < ((r * s : ℕ) : ℝ) := by positivity
  have hQpos : 0 < Q := by
    dsimp only [Q, centralCorrelationFrequency]
    positivity
  have hrs_le_fourKsq : r * s ≤ 4 * K ^ 2 := by nlinarith
  have hKsq_le_rs : K ^ 2 ≤ r * s := by nlinarith
  have hyLowerR : (M : ℝ) * K ≤ y := by exact_mod_cast hyLower.le
  have hrsUpperR : (((r * s : ℕ) : ℝ)) ≤ 4 * (K : ℝ) ^ 2 := by
    exact_mod_cast hrs_le_fourKsq
  have hQlowerD : (M : ℝ) ^ 2 * d ≤
      16 * (H : ℝ) ^ 2 * Q := by
    dsimp only [Q, centralCorrelationFrequency]
    rw [show 16 * (H : ℝ) ^ 2 *
        (X * (d : ℝ) / ((r * s : ℕ) : ℝ)) =
      (16 * (H : ℝ) ^ 2 * X * (d : ℝ)) /
        ((r * s : ℕ) : ℝ) by ring]
    rw [le_div_iff₀ hrsPos]
    have hbase : (M : ℝ) ^ 2 * ((r * s : ℕ) : ℝ) ≤
        16 * (H : ℝ) ^ 2 * X := by
      have hMK : (M : ℝ) ^ 2 * (K : ℝ) ^ 2 ≤ (y : ℝ) ^ 2 := by
        have hmul := mul_le_mul hyLowerR hyLowerR (by positivity) (by positivity)
        nlinarith
      calc
        (M : ℝ) ^ 2 * ((r * s : ℕ) : ℝ) ≤
            (M : ℝ) ^ 2 * (4 * (K : ℝ) ^ 2) := by gcongr
        _ ≤ 4 * (y : ℝ) ^ 2 := by nlinarith
        _ ≤ 16 * (H : ℝ) ^ 2 * X := by nlinarith
    calc
      (M : ℝ) ^ 2 * (d : ℝ) * ((r * s : ℕ) : ℝ) =
          ((M : ℝ) ^ 2 * ((r * s : ℕ) : ℝ)) * d := by ring
      _ ≤ (16 * (H : ℝ) ^ 2 * X) * d := by gcongr
      _ = 16 * (H : ℝ) ^ 2 * X * (d : ℝ) := by ring
  have hQlower : (M : ℝ) ^ 2 ≤ 16 * (H : ℝ) ^ 2 * Q := by
    have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hdPos
    calc
      (M : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 * d := by
        rw [le_mul_iff_one_le_right (by positivity)]
        exact hdOne
      _ ≤ 16 * (H : ℝ) ^ 2 * Q := hQlowerD
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
  have hKsqR : (K : ℝ) ^ 2 ≤ ((r * s : ℕ) : ℝ) := by
    exact_mod_cast hKsq_le_rs
  have hupperNumerator : X * (d : ℝ) ≤
      (8 ^ 16 * (M : ℝ) ^ 31) * ((r * s : ℕ) : ℝ) := by
    calc
      X * (d : ℝ) ≤
          (8 ^ 16 * (M : ℝ) ^ 16 * (K : ℝ) ^ 16) * K := by gcongr
      _ = 8 ^ 16 * (M : ℝ) ^ 16 * (K : ℝ) ^ 15 * (K : ℝ) ^ 2 := by ring
      _ ≤ 8 ^ 16 * (M : ℝ) ^ 16 * (M : ℝ) ^ 15 * (K : ℝ) ^ 2 := by
        have hp := pow_le_pow_left₀ (by positivity) hKMR 15
        gcongr
      _ = (8 ^ 16 * (M : ℝ) ^ 31) * (K : ℝ) ^ 2 := by ring
      _ ≤ (8 ^ 16 * (M : ℝ) ^ 31) * ((r * s : ℕ) : ℝ) := by gcongr
  have hQupper : Q ≤ centralFrequencyConstant * (M : ℝ) ^ 31 := by
    dsimp only [Q, centralCorrelationFrequency]
    rw [div_le_iff₀ hrsPos]
    simpa only [centralFrequencyConstant] using hupperNumerator
  exact ⟨hab, haM, hbM, hQpos, hQlower, hQupper⟩

/-- Off-diagonal cutoff correlation in the relaxed range. -/
theorem norm_relaxed_cutoff_correlation_le
    {X : ℝ} {H x y M K r s : ℕ}
    (hH : 1 ≤ H) (hM : 1 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hr : r ∈ Finset.Ioc K (2 * K))
    (hs : s ∈ Finset.Ioc K (2 * K)) (hrs : r < s)
    (hXlo : (y : ℝ) ^ 2 ≤ 4 * (H : ℝ) ^ 2 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hsize : centralCorrelationSizeCondition M) :
    ‖∑ m ∈ Finset.Ioc M (2 * M),
        reciprocalCutoffWeight X x y m s *
          conj (reciprocalCutoffWeight X x y m r)‖ ≤
      relaxedCorrelationEnvelope H M := by
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
    rw [hempty, Finset.sum_empty, norm_zero]
    exact relaxedCorrelationEnvelope_nonneg H hM
  · have hscale := relaxedCorrelation_scale_bounds hH hM hK hKM hr hs hrs
      hXlo hXhi hyx (Nat.pos_of_ne_zero hN)
    rcases hscale with ⟨hab, hMa, hbM, hQpos, hQlo, hQhi⟩
    let Q := centralCorrelationFrequency X r s
    rw [norm_sum_reciprocalCutoffWeight_correlation_comm X x y M (2 * M) s r]
    rw [sum_reciprocalCutoffWeight_correlation_eq_phase X
      (hK.trans (Finset.mem_Ioc.mp hr).1)
      (hK.trans (Finset.mem_Ioc.mp hs).1) hrs.le]
    exact norm_reciprocalProductIntervalSum_le_relaxed
      hQpos hH hM hQlo hQhi hsize hab hMa hbM

/-- Cauchy--Schwarz transports the relaxed off-diagonal estimate to an
arbitrary bilinear block. -/
theorem norm_relaxed_reciprocalBilinearBlock_sq_le_energy
    {X : ℝ} {H x y M K : ℕ} (a b : ℕ → ℂ)
    (hH : 1 ≤ H) (hM : 1 ≤ M) (hK : 0 < K) (hKM : K ≤ M)
    (hXlo : (y : ℝ) ^ 2 ≤ 4 * (H : ℝ) ^ 2 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hsize : centralCorrelationSizeCondition M) :
    ‖reciprocalBilinearBlock X x y M (2 * M) K (2 * K) a b‖ ^ 2 ≤
      (∑ m ∈ Finset.Ioc M (2 * M), ‖a m‖ ^ 2) *
        ((M : ℝ) * (∑ k ∈ Finset.Ioc K (2 * K), ‖b k‖ ^ 2) +
          relaxedCorrelationEnvelope H M *
            (∑ k ∈ Finset.Ioc K (2 * K), ‖b k‖) ^ 2) := by
  let t := Finset.Ioc K (2 * K)
  let B := relaxedCorrelationEnvelope H M
  have hB : 0 ≤ B := relaxedCorrelationEnvelope_nonneg H hM
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
      _ ≤ ∑ r ∈ t, ∑ s ∈ t,
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
                _ ≤ ‖b r‖ * ‖b r‖ * (M : ℝ) := by
                  gcongr
                _ = _ := by ring
            exact hmain.trans (le_add_of_nonneg_right (by positivity))
          · simp only [if_neg hrs, zero_add]
            rcases lt_or_gt_of_ne hrs with hrslt | hsrlt
            · exact mul_le_mul_of_nonneg_left
                (norm_relaxed_cutoff_correlation_le hH hM hK hKM
                  hr hs hrslt hXlo hXhi hyx hsize) (by positivity)
            · rw [norm_sum_reciprocalCutoffWeight_correlation_comm
                X x y M (2 * M) s r]
              exact mul_le_mul_of_nonneg_left
                (norm_relaxed_cutoff_correlation_le hH hM hK hKM
                  hs hr hsrlt hXlo hXhi hyx hsize) (by positivity)
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
            _ = _ := by rw [← Finset.sum_mul]; ring
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

private lemma relaxed_quotient_endpoint_le
    {x y d : ℕ} (hd : 0 < d) (hdx : d ≤ x) (hyx : y ≤ 2 * x) :
    y / d ≤ 2 * (x / d) + 1 := by
  have hxlt : x < d * (x / d + 1) := Nat.lt_mul_div_succ x hd
  have hylt : y < d * (2 * (x / d) + 2) := by
    calc
      y ≤ 2 * x := hyx
      _ < 2 * (d * (x / d + 1)) := by omega
      _ = d * (2 * (x / d) + 2) := by ring
  have hdiv : y / d < 2 * (x / d) + 2 :=
    (Nat.div_lt_iff_lt_mul hd).2 (by simpa [mul_comm] using hylt)
  omega

private lemma relaxed_product_frequency_bounds
    {X : ℝ} {H x y d : ℕ} (hX : 0 < X) (hH : 1 ≤ H)
    (hd : 0 < d) (hdx : d ≤ x) (hdscale : d ≤ x / d + 1)
    (hXlo : (y : ℝ) ^ 2 ≤ 4 * (H : ℝ) ^ 2 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hxy : x < y) (hyx : y ≤ 2 * x) :
    let M := x / d + 1
    (M : ℝ) ^ 2 ≤ 16 * (H : ℝ) ^ 2 * (X / (d : ℝ)) ∧
      X / (d : ℝ) ≤ centralFrequencyConstant * (M : ℝ) ^ 31 := by
  let M := x / d + 1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdxM : d * M ≤ 2 * x := by
    dsimp only [M]
    nlinarith [Nat.div_mul_le_self x d]
  have hdxMR : (d : ℝ) * M ≤ 2 * y := by
    exact_mod_cast hdxM.trans (Nat.mul_le_mul_left 2 hxy.le)
  have hsq : (d : ℝ) ^ 2 * (M : ℝ) ^ 2 ≤
      16 * (H : ℝ) ^ 2 * X := by
    have hsquare : ((d : ℝ) * M) ^ 2 ≤ (2 * (y : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hdxMR 2
    nlinarith
  have hlowerMul : (d : ℝ) * (M : ℝ) ^ 2 ≤
      16 * (H : ℝ) ^ 2 * X := by
    calc
      (d : ℝ) * (M : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 * (M : ℝ) ^ 2 := by
        gcongr
        nlinarith
      _ ≤ _ := hsq
  have hlower : (M : ℝ) ^ 2 ≤
      16 * (H : ℝ) ^ 2 * (X / (d : ℝ)) := by
    rw [show 16 * (H : ℝ) ^ 2 * (X / (d : ℝ)) =
      (16 * (H : ℝ) ^ 2 * X) / d by ring]
    exact (le_div_iff₀ hdR).2 (by simpa [mul_comm] using hlowerMul)
  have hxlt : x < d * M := Nat.lt_mul_div_succ x hd
  have hyUpper : (y : ℝ) ≤ 2 * (d : ℝ) * M := by
    have hnat : y ≤ 2 * d * M := by
      have : y < 2 * (d * M) := hyx.trans_lt (by omega)
      simpa [Nat.mul_assoc] using this.le
    exact_mod_cast hnat
  have hXupper : X ≤ 2 ^ 16 * (d : ℝ) ^ 16 * (M : ℝ) ^ 16 := by
    calc
      X ≤ (y : ℝ) ^ 16 := hXhi
      _ ≤ (2 * (d : ℝ) * M) ^ 16 :=
        pow_le_pow_left₀ (by positivity) hyUpper 16
      _ = _ := by ring
  have hdM : (d : ℝ) ≤ M := by exact_mod_cast hdscale
  have hupperMul : X ≤
      (centralFrequencyConstant * (M : ℝ) ^ 31) * d := by
    calc
      X ≤ 2 ^ 16 * (d : ℝ) ^ 16 * (M : ℝ) ^ 16 := hXupper
      _ = 2 ^ 16 * (d : ℝ) ^ 15 * (M : ℝ) ^ 16 * d := by ring
      _ ≤ 2 ^ 16 * (M : ℝ) ^ 15 * (M : ℝ) ^ 16 * d := by
        have hp := pow_le_pow_left₀ (by positivity) hdM 15
        gcongr
      _ ≤ 8 ^ 16 * (M : ℝ) ^ 31 * d := by
        have hc : (2 : ℝ) ^ 16 ≤ 8 ^ 16 := by norm_num
        have hMp : 0 ≤ (M : ℝ) ^ 31 := pow_nonneg (by positivity) 31
        nlinarith
      _ = (centralFrequencyConstant * (M : ℝ) ^ 31) * d := by
        unfold centralFrequencyConstant
        ring
  have hupper : X / (d : ℝ) ≤
      centralFrequencyConstant * (M : ℝ) ^ 31 :=
    (div_le_iff₀ hdR).2 (by simpa [mul_comm] using hupperMul)
  exact ⟨hlower, hupper⟩

private lemma relaxed_sum_Ioc_split_first
    (f : ℕ → ℂ) {a b : ℕ} (hab : a < b) :
    (∑ n ∈ Finset.Ioc a b, f n) =
      f (a + 1) + ∑ n ∈ Finset.Ioc (a + 1) b, f n := by
  have hdisj : Disjoint (Finset.Ioc a (a + 1)) (Finset.Ioc (a + 1) b) := by
    rw [Finset.disjoint_left]
    intro n hn₁ hn₂
    have h₁ := Finset.mem_Ioc.mp hn₁
    have h₂ := Finset.mem_Ioc.mp hn₂
    omega
  calc
    _ = ∑ n ∈ Finset.Ioc a (a + 1) ∪ Finset.Ioc (a + 1) b, f n := by
      rw [Finset.Ioc_union_Ioc_eq_Ioc (show a ≤ a + 1 by omega)
        (show a + 1 ≤ b by omega)]
    _ = (∑ n ∈ Finset.Ioc a (a + 1), f n) +
        ∑ n ∈ Finset.Ioc (a + 1) b, f n := Finset.sum_union hdisj
    _ = _ := by rw [Finset.sum_Ioc_succ_top (le_refl a)]; simp

/-- Prefix estimate after extracting a small Vaughan factor. -/
theorem norm_relaxed_reciprocalProductInterval_partial_le
    {X : ℝ} (hX : 0 < X) {H x y d b : ℕ}
    (hH : 1 ≤ H) (hd : 0 < d) (hdx : d ≤ x)
    (hdscale : d ≤ x / d + 1) (hxy : x < y) (hby : b ≤ y / d)
    (hXlo : (y : ℝ) ^ 2 ≤ 4 * (H : ℝ) ^ 2 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hsize : centralCorrelationSizeCondition (x / d + 1)) :
    ‖reciprocalProductIntervalSum X d (x / d) b‖ ≤
      1 + relaxedCorrelationEnvelope H (x / d + 1) := by
  let a := x / d
  let M := a + 1
  have hM : 1 ≤ M := by omega
  have hQ : 0 < X / (d : ℝ) := div_pos hX (by exact_mod_cast hd)
  have hbtop : b ≤ 2 * a + 1 := hby.trans (by
    simpa only [a] using relaxed_quotient_endpoint_le hd hdx hyx)
  have hfreq := relaxed_product_frequency_bounds hX hH hd hdx
    (by simpa only [a, M] using hdscale) hXlo hXhi hxy hyx
  change ‖reciprocalProductIntervalSum X d a b‖ ≤ _
  by_cases hab : a < b
  · have hrest : ‖reciprocalProductIntervalSum X d M b‖ ≤
        relaxedCorrelationEnvelope H M := by
      by_cases hMlt : M < b
      · rw [CentralProductInterval.reciprocalProductIntervalSum_rescale X hd]
        exact norm_reciprocalProductIntervalSum_le_relaxed hQ hH hM
          hfreq.1 hfreq.2 hsize hMlt le_rfl (by omega)
      · unfold reciprocalProductIntervalSum
        rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
        exact relaxedCorrelationEnvelope_nonneg H hM
    unfold reciprocalProductIntervalSum at ⊢ hrest
    rw [relaxed_sum_Ioc_split_first (fun n ↦ reciprocalWeight X (d * n)) hab]
    exact (norm_add_le _ _).trans <| by
      simpa only [M, norm_reciprocalWeight] using add_le_add le_rfl hrest
  · unfold reciprocalProductIntervalSum
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    exact add_nonneg (by norm_num) (relaxedCorrelationEnvelope_nonneg H hM)

/-- Abel summation with the relaxed prefix envelope. -/
theorem norm_log_weighted_relaxedProductInterval_le
    {X : ℝ} (hX : 0 < X) {H x y d : ℕ}
    (hH : 1 ≤ H) (hd : 0 < d) (hdx : d ≤ x)
    (hdscale : d ≤ x / d + 1) (hxy : x < y)
    (hXlo : (y : ℝ) ^ 2 ≤ 4 * (H : ℝ) ^ 2 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hsize : centralCorrelationSizeCondition (x / d + 1)) :
    ‖∑ h ∈ Finset.Ioc (x / d) (y / d),
        ((Real.log (h : ℝ) : ℝ) : ℂ) * reciprocalWeight X (d * h)‖ ≤
      2 * Real.log (y : ℝ) *
        (1 + relaxedCorrelationEnvelope H (x / d + 1)) := by
  let a := x / d
  let b := y / d
  let B := 1 + relaxedCorrelationEnvelope H (a + 1)
  have hM : 1 ≤ a + 1 := by omega
  have hB : 0 ≤ B := add_nonneg (by norm_num)
    (relaxedCorrelationEnvelope_nonneg H hM)
  have hyone : 1 ≤ y := by omega
  have hlogY0 : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hyone)
  by_cases hab : a < b
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, b = a + n + 1 :=
      ⟨b - a - 1, by omega⟩
    let z : ℕ → ℂ := fun h ↦ reciprocalWeight X (d * h)
    have hparts := central_log_sum_by_parts_aux z a n
    change ‖∑ h ∈ Finset.Ioc a b,
        ((Real.log (h : ℝ) : ℝ) : ℂ) * z h‖ ≤ _
    rw [show Finset.Ioc a b = Finset.Ioc a (a + n + 1) by rw [hn]]
    rw [hparts]
    have hfull : ‖∑ i ∈ Finset.Ioc a (a + n + 1), z i‖ ≤ B := by
      simpa only [reciprocalProductIntervalSum, z, a, B, hn] using
        norm_relaxed_reciprocalProductInterval_partial_le
          hX hH hd hdx hdscale hxy
            (show a + n + 1 ≤ y / d by rw [← hn])
            hXlo hXhi hyx hsize
    have hprefix (j : ℕ) (hj : j ∈ Finset.Ioc a (a + n)) :
        ‖∑ i ∈ Finset.Ioc a j, z i‖ ≤ B := by
      have hjtop := (Finset.mem_Ioc.mp hj).2
      have hjb : j ≤ b := by omega
      simpa only [reciprocalProductIntervalSum, z, a, B] using
        norm_relaxed_reciprocalProductInterval_partial_le
          hX hH hd hdx hdscale hxy (hjb.trans (by exact le_rfl))
            hXlo hXhi hyx hsize
    have hdiff0 (j : ℕ) (hj : j ∈ Finset.Ioc a (a + n)) :
        0 ≤ Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) := by
      have haj := (Finset.mem_Ioc.mp hj).1
      have hjpos : 0 < j := by omega
      exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hjpos)
        (by exact_mod_cast (show j ≤ j + 1 by omega)))
    have hcorrection :
        ‖∑ j ∈ Finset.Ioc a (a + n),
          ((Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) : ℝ) : ℂ) *
            ∑ i ∈ Finset.Ioc a j, z i‖ ≤
          (Real.log (a + n + 1 : ℕ) - Real.log (a + 1 : ℕ)) * B := by
      calc
        _ ≤ ∑ j ∈ Finset.Ioc a (a + n),
            ‖((Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) : ℝ) : ℂ) *
              ∑ i ∈ Finset.Ioc a j, z i‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.Ioc a (a + n),
            (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)) * B := by
          apply Finset.sum_le_sum
          intro j hj
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hdiff0 j hj)]
          exact mul_le_mul_of_nonneg_left (hprefix j hj) (hdiff0 j hj)
        _ = (Real.log (a + n + 1 : ℕ) - Real.log (a + 1 : ℕ)) * B := by
          rw [← Finset.sum_mul]
          congr 1
          simpa only [Nat.cast_add, Nat.cast_one] using
            central_sum_log_succ_sub_Ioc a n
    have hblog : Real.log (a + n + 1 : ℕ) ≤ Real.log (y : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast (show 0 < a + n + 1 by omega)
      · exact_mod_cast (show a + n + 1 ≤ y by
          rw [← hn]
          exact Nat.div_le_self y d)
    have hsub : Real.log (a + n + 1 : ℕ) - Real.log (a + 1 : ℕ) ≤
        Real.log (y : ℝ) := by
      have hloga : 0 ≤ Real.log (a + 1 : ℕ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ a + 1 by omega))
      linarith
    refine (norm_sub_le _ _).trans ?_
    calc
      _ ≤ Real.log (a + n + 1 : ℕ) * B +
          (Real.log (a + n + 1 : ℕ) - Real.log (a + 1 : ℕ)) * B := by
        apply add_le_add
        · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg]
          · exact mul_le_mul_of_nonneg_left hfull (by
              exact Real.log_nonneg (by exact_mod_cast
                (show 1 ≤ a + n + 1 by omega)))
          · exact Real.log_nonneg (by exact_mod_cast
              (show 1 ≤ a + n + 1 by omega))
        · exact hcorrection
      _ ≤ Real.log (y : ℝ) * B + Real.log (y : ℝ) * B :=
        add_le_add (mul_le_mul_of_nonneg_right hblog hB)
          (mul_le_mul_of_nonneg_right hsub hB)
      _ = 2 * Real.log (y : ℝ) * B := by ring
  · change ‖∑ h ∈ Finset.Ioc a b,
        ((Real.log (h : ℝ) : ℝ) : ℂ) * reciprocalWeight X (d * h)‖ ≤ _
    rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hlogY0) hB

end

end RelaxedReciprocal
end Erdos378
