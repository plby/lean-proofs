/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.CentralCorrelation
import ErdosProblems.Erdos378.VaughanReciprocalEstimate

/-!
# Vaughan's fourth term in the central range
-/

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Erdos378
namespace CentralVaughan

open PrimeReciprocal
open BilinearReciprocal
open VaughanReciprocalBlocks
open VaughanReciprocalEstimate
open AdaptiveShifts
open CentralCorrelation

noncomputable section

def centralVaughanBlockMajorant (V : ℝ) (M K : ℕ) : ℝ :=
  (8 / 3 : ℝ) * (M : ℝ) * (K : ℝ) *
    (Real.log (2 * (M : ℝ))) ^ 2 * (Real.log V + 3) ^ 2 *
      ((max M K : ℕ) +
        adaptiveCorrelationEnvelope (max M K) * (min M K : ℕ))

lemma centralVaughanBlockMajorant_nonneg
    {V : ℝ} {M K : ℕ} (hmax : 1 ≤ max M K) :
    0 ≤ centralVaughanBlockMajorant V M K := by
  unfold centralVaughanBlockMajorant
  have hB := adaptiveCorrelationEnvelope_nonneg hmax
  positivity

theorem norm_central_reciprocalVaughanBlock_sq_le
    {X U V : ℝ} {x y M K : ℕ}
    (hV : 1 ≤ V) (hM : 0 < M) (hK : 0 < K)
    (hsize : centralCorrelationSizeCondition (max M K))
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x) :
    ‖reciprocalBilinearBlock X x y M (2 * M) K (2 * K)
        (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V)‖ ^ 2 ≤
      centralVaughanBlockMajorant V M K := by
  rcases le_total K M with hKM | hMK
  · have hmax : max M K = M := max_eq_left hKM
    have hbase := norm_central_reciprocalBilinearBlock_sq_le_energy
      (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V)
      (show 1 ≤ M by omega) hK hKM hXlo hXhi hyx (by simpa [hmax] using hsize)
    let EA := (M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2
    let EB := (8 / 3 : ℝ) * (K : ℝ) * (Real.log V + 3) ^ 2
    let B := adaptiveCorrelationEnvelope M
    have hEA : (∑ m ∈ Finset.Ioc M (2 * M),
        ‖cutoffMangoldtCoefficient U m‖ ^ 2) ≤ EA :=
      sum_norm_sq_cutoffMangoldtCoefficient_Ioc_le U M
    have hEB : (∑ k ∈ Finset.Ioc K (2 * K),
        ‖cutoffFourthCoefficient V k‖ ^ 2) ≤ EB :=
      sum_norm_sq_cutoffFourthCoefficient_Ioc_le hV K
    have hL1 : (∑ k ∈ Finset.Ioc K (2 * K),
        ‖cutoffFourthCoefficient V k‖) ^ 2 ≤ (K : ℝ) * EB :=
      sum_norm_cutoffFourthCoefficient_Ioc_sq_le hV
    have hB : 0 ≤ B := adaptiveCorrelationEnvelope_nonneg (by omega)
    have hEA0 : 0 ≤ EA := by dsimp only [EA]; positivity
    have hEB0 : 0 ≤ EB := by dsimp only [EB]; positivity
    have hinner :
        (M : ℝ) * (∑ k ∈ Finset.Ioc K (2 * K),
            ‖cutoffFourthCoefficient V k‖ ^ 2) +
          B * (∑ k ∈ Finset.Ioc K (2 * K),
            ‖cutoffFourthCoefficient V k‖) ^ 2 ≤
        EB * ((M : ℝ) + B * (K : ℝ)) := by
      calc
        _ ≤ (M : ℝ) * EB + B * ((K : ℝ) * EB) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hEB (by positivity))
            (mul_le_mul_of_nonneg_left hL1 hB)
        _ = EB * ((M : ℝ) + B * (K : ℝ)) := by ring
    calc
      _ ≤ (∑ m ∈ Finset.Ioc M (2 * M),
          ‖cutoffMangoldtCoefficient U m‖ ^ 2) *
          ((M : ℝ) * (∑ k ∈ Finset.Ioc K (2 * K),
            ‖cutoffFourthCoefficient V k‖ ^ 2) +
          B * (∑ k ∈ Finset.Ioc K (2 * K),
            ‖cutoffFourthCoefficient V k‖) ^ 2) := hbase
      _ ≤ EA * (EB * ((M : ℝ) + B * (K : ℝ))) := by
        exact mul_le_mul hEA hinner (by positivity) hEA0
      _ = centralVaughanBlockMajorant V M K := by
        simp only [EA, EB, B, centralVaughanBlockMajorant, hmax,
          min_eq_right hKM]
        push_cast
        ring
  · have hmax : max M K = K := max_eq_right hMK
    have hbase := norm_central_reciprocalBilinearBlock_sq_le_energy
      (cutoffFourthCoefficient V) (cutoffMangoldtCoefficient U)
      (show 1 ≤ K by omega) hM hMK hXlo hXhi hyx (by simpa [hmax] using hsize)
    let EA := (M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2
    let EB := (8 / 3 : ℝ) * (K : ℝ) * (Real.log V + 3) ^ 2
    let B := adaptiveCorrelationEnvelope K
    have hEA : (∑ m ∈ Finset.Ioc M (2 * M),
        ‖cutoffMangoldtCoefficient U m‖ ^ 2) ≤ EA :=
      sum_norm_sq_cutoffMangoldtCoefficient_Ioc_le U M
    have hEB : (∑ k ∈ Finset.Ioc K (2 * K),
        ‖cutoffFourthCoefficient V k‖ ^ 2) ≤ EB :=
      sum_norm_sq_cutoffFourthCoefficient_Ioc_le hV K
    have hL1 : (∑ m ∈ Finset.Ioc M (2 * M),
        ‖cutoffMangoldtCoefficient U m‖) ^ 2 ≤ (M : ℝ) * EA :=
      sum_norm_cutoffMangoldtCoefficient_Ioc_sq_le
    have hB : 0 ≤ B := adaptiveCorrelationEnvelope_nonneg (by omega)
    have hEA0 : 0 ≤ EA := by dsimp only [EA]; positivity
    have hEB0 : 0 ≤ EB := by dsimp only [EB]; positivity
    have hinner :
        (K : ℝ) * (∑ m ∈ Finset.Ioc M (2 * M),
            ‖cutoffMangoldtCoefficient U m‖ ^ 2) +
          B * (∑ m ∈ Finset.Ioc M (2 * M),
            ‖cutoffMangoldtCoefficient U m‖) ^ 2 ≤
        EA * ((K : ℝ) + B * (M : ℝ)) := by
      calc
        _ ≤ (K : ℝ) * EA + B * ((M : ℝ) * EA) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hEA (by positivity))
            (mul_le_mul_of_nonneg_left hL1 hB)
        _ = EA * ((K : ℝ) + B * (M : ℝ)) := by ring
    rw [reciprocalBilinearBlock_comm]
    calc
      _ ≤ (∑ k ∈ Finset.Ioc K (2 * K),
          ‖cutoffFourthCoefficient V k‖ ^ 2) *
          ((K : ℝ) * (∑ m ∈ Finset.Ioc M (2 * M),
            ‖cutoffMangoldtCoefficient U m‖ ^ 2) +
          B * (∑ m ∈ Finset.Ioc M (2 * M),
            ‖cutoffMangoldtCoefficient U m‖) ^ 2) := hbase
      _ ≤ EB * (EA * ((K : ℝ) + B * (M : ℝ))) := by
        exact mul_le_mul hEB hinner (by positivity) hEB0
      _ = centralVaughanBlockMajorant V M K := by
        simp only [EA, EB, B, centralVaughanBlockMajorant, hmax,
          min_eq_left hMK]
        push_cast
        ring

/-- Every dyadic fourth-term block has its scale-specific majorant. -/
theorem norm_central_reciprocalVaughanFourthDyadicBlock_sq_le
    {X : ℝ} {x y T alpha beta : ℕ}
    (hT : 0 < T)
    (hsize : centralCorrelationSizeCondition (max (2 ^ alpha) (2 ^ beta)))
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x) :
    ‖reciprocalVaughanFourthDyadicBlock X T T x y alpha beta‖ ^ 2 ≤
      centralVaughanBlockMajorant T (2 ^ alpha) (2 ^ beta) := by
  rw [reciprocalVaughanFourthDyadicBlock_eq_full]
  simp only [reciprocalVaughanFourthFullDyadicBlock, pow_succ,
    Nat.mul_comm]
  exact norm_central_reciprocalVaughanBlock_sq_le
    (by exact_mod_cast hT) (by positivity) (by positivity)
      hsize hXlo hXhi hyx

end

end CentralVaughan
end Erdos378
