/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.InverseSquareHybridAsymptotic
import ErdosProblems.Erdos378.InverseSquareVaughanBlocks
import ErdosProblems.Erdos378.VaughanReciprocalEstimate

/-!
# Hybrid inverse-square bounds for Vaughan's fourth term

The close-column width is `K / H`.  Its diagonal cost is `O(1/H)`, while
the third-derivative estimate on separated columns is also `O(1/H)` once
the original phase is at least `H² y²`.
-/

open scoped BigOperators ComplexConjugate ArithmeticFunction.vonMangoldt

namespace Erdos378
namespace InverseSquareVaughanHybrid

open BoundedGaps.Maynard
open PrimeReciprocal
open AdaptiveShifts
open InverseSquareCorrelation
open InverseSquareBilinear
open InverseSquareVaughanBlocks
open InverseSquareAdaptiveShifts
open InverseSquareCentralCorrelation
open InverseSquareHybridCorrelation
open InverseSquareHybridAsymptotic

noncomputable section

def orientedCorrelationBound (M H : ℕ) (delta : ℝ) : ℝ :=
  2 + 96 * (M : ℝ) / (H : ℝ) + delta * (M : ℝ)

def inverseSquareOrientedBlockMajorant
    (V : ℝ) (M K H : ℕ) (delta : ℝ) : ℝ :=
  ((M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2) *
    (((M : ℝ) * (((2 * (K / H) + 1 : ℕ) : ℝ) : ℝ) +
        orientedCorrelationBound M H delta * (K : ℝ)) *
      ((8 / 3 : ℝ) * (K : ℝ) * (Real.log V + 3) ^ 2))

lemma inverseSquareOrientedBlockMajorant_nonneg
    {V delta : ℝ} {M K H : ℕ}
    (hM : 0 < M) (hH : 0 < H) (hdelta : 0 ≤ delta) :
    0 ≤ inverseSquareOrientedBlockMajorant V M K H delta := by
  unfold inverseSquareOrientedBlockMajorant orientedCorrelationBound
  positivity

private lemma sum_norm_sq_cutoffMangoldtCoefficient_Ioc_le
    (U : ℝ) (M : ℕ) :
    (∑ m ∈ Finset.Ioc M (2 * M),
      ‖InverseSquareVaughanBlocks.cutoffMangoldtCoefficient U m‖ ^ 2) ≤
      (M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2 := by
  simpa [InverseSquareVaughanBlocks.cutoffMangoldtCoefficient,
    VaughanReciprocalBlocks.cutoffMangoldtCoefficient] using
    VaughanReciprocalEstimate.sum_norm_sq_cutoffMangoldtCoefficient_Ioc_le U M

private lemma sum_norm_sq_cutoffFourthCoefficient_Ioc_le
    {V : ℝ} (hV : 1 ≤ V) (K : ℕ) :
    (∑ k ∈ Finset.Ioc K (2 * K),
      ‖InverseSquareVaughanBlocks.cutoffFourthCoefficient V k‖ ^ 2) ≤
      (8 / 3 : ℝ) * (K : ℝ) * (Real.log V + 3) ^ 2 := by
  simpa [InverseSquareVaughanBlocks.cutoffFourthCoefficient,
    VaughanReciprocalBlocks.cutoffFourthCoefficient] using
    VaughanReciprocalEstimate.sum_norm_sq_cutoffFourthCoefficient_Ioc_le hV K

/-- The elementary comparison which makes both the close and separated
contributions cost `O(1/H)`. -/
lemma separated_fraction_le
    {M K H : ℕ} (hM : 0 < M) (hH : 0 < H) :
    96 * (M : ℝ) * (K : ℝ) /
        ((H : ℝ) ^ 2 * (((K / H + 1 : ℕ) : ℝ))) ≤
      96 * (M : ℝ) / (H : ℝ) := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hden : (0 : ℝ) < (H : ℝ) ^ 2 * (((K / H + 1 : ℕ) : ℝ)) := by
    positivity
  rw [div_le_iff₀ hden]
  have hk : K ≤ H * (K / H + 1) := by
    exact (Nat.lt_mul_div_succ K hH).le
  have hkR : (K : ℝ) ≤ (H : ℝ) * ((K / H + 1 : ℕ) : ℝ) := by
    exact_mod_cast hk
  calc
    96 * (M : ℝ) * (K : ℝ) ≤
        96 * (M : ℝ) * ((H : ℝ) * ((K / H + 1 : ℕ) : ℝ)) := by
      gcongr
    _ = (96 * (M : ℝ) / (H : ℝ)) *
        ((H : ℝ) ^ 2 * ((K / H + 1 : ℕ) : ℝ)) := by
      field_simp [ne_of_gt hHR]

/-- One oriented dyadic block, with the longer variable in the outer
Cauchy--Schwarz position. -/
theorem norm_inverseSquareVaughanBlock_sq_le_oriented
    {X delta U V : ℝ} {x y M K H C : ℕ}
    (hX : 0 < X) (hH : 0 < H) (hdelta : 0 ≤ delta)
    (hV : 1 ≤ V) (hM : 0 < M) (hK : 0 < K) (hKM : K ≤ M)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hXratio : (H : ℝ) ^ 2 * (y : ℝ) ^ 2 ≤ X)
    (hsize : inverseSquareCentralCorrelationSizeCondition M)
    (hC : 2 ≤ C) (hbaseCap : baseShift M ≤ M / C)
    (hlargeEnvelope : ∀ Q : ℝ, 0 < Q →
      (M : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * (M : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q M C ≤ delta * M) :
    ‖inverseSquareBilinearBlock X x y M (2 * M) K (2 * K)
        (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V)‖ ^ 2 ≤
      inverseSquareOrientedBlockMajorant V M K H delta := by
  let D := K / H
  let B := orientedCorrelationBound M H delta
  have hMone : 1 ≤ M := hM
  have hB : 0 ≤ B := by
    dsimp only [B, orientedCorrelationBound]
    positivity
  have hcorr : ∀ r ∈ Finset.Ioc K (2 * K),
      ∀ s ∈ Finset.Ioc K (2 * K), r < s → D < s - r →
      ‖∑ m ∈ Finset.Ioc M (2 * M),
        inverseSquareCutoffWeight X x y m s *
          conj (inverseSquareCutoffWeight X x y m r)‖ ≤ B := by
    intro r hr s hs hrs hfar
    have hraw := norm_inverseSquareCentral_cutoff_correlation_le_separated
      hX (show (0 : ℝ) < (H : ℝ) ^ 2 by positivity) hdelta
      hMone hK hKM hr hs hrs hfar hXlo hXhi hyx hXratio
      hsize hC hbaseCap hlargeEnvelope
    have hfrac := separated_fraction_le hM hH (K := K)
    dsimp only [D] at hraw
    dsimp only [B, orientedCorrelationBound]
    exact hraw.trans (by linarith)
  have hbase := norm_inverseSquareCentral_bilinearBlock_sq_le_hybrid
    (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V)
    hX hMone hK hKM hXlo hXhi hyx hsize hC hbaseCap B hB hcorr
  let EA := (M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2
  let EB := (8 / 3 : ℝ) * (K : ℝ) * (Real.log V + 3) ^ 2
  have hEA : (∑ m ∈ Finset.Ioc M (2 * M),
      ‖cutoffMangoldtCoefficient U m‖ ^ 2) ≤ EA :=
    sum_norm_sq_cutoffMangoldtCoefficient_Ioc_le U M
  have hEB : (∑ k ∈ Finset.Ioc K (2 * K),
      ‖cutoffFourthCoefficient V k‖ ^ 2) ≤ EB :=
    sum_norm_sq_cutoffFourthCoefficient_Ioc_le hV K
  have hEA0 : 0 ≤ EA := by dsimp only [EA]; positivity
  have hinner :
      (((M : ℝ) * (((2 * D + 1 : ℕ) : ℝ)) + B * (K : ℝ)) *
        (∑ k ∈ Finset.Ioc K (2 * K),
          ‖cutoffFourthCoefficient V k‖ ^ 2)) ≤
      (((M : ℝ) * (((2 * D + 1 : ℕ) : ℝ)) + B * (K : ℝ)) * EB) := by
    exact mul_le_mul_of_nonneg_left hEB (by positivity)
  calc
    _ ≤ (∑ m ∈ Finset.Ioc M (2 * M),
        ‖cutoffMangoldtCoefficient U m‖ ^ 2) *
      (((M : ℝ) * (((2 * D + 1 : ℕ) : ℝ)) + B * (K : ℝ)) *
        (∑ k ∈ Finset.Ioc K (2 * K),
          ‖cutoffFourthCoefficient V k‖ ^ 2)) := hbase
    _ ≤ EA *
      (((M : ℝ) * (((2 * D + 1 : ℕ) : ℝ)) + B * (K : ℝ)) * EB) := by
      exact mul_le_mul hEA hinner (by positivity) hEA0
    _ = inverseSquareOrientedBlockMajorant V M K H delta := by
      simp only [EA, EB, D, B, inverseSquareOrientedBlockMajorant]

def inverseSquareFourthUniformMajorant
    (y T H : ℕ) (delta : ℝ) : ℝ :=
  (8 / 3 : ℝ) * (y : ℝ) ^ 2 *
    (Real.log (2 * (y : ℝ))) ^ 2 *
    (Real.log (T : ℝ) + 3) ^ 2 *
    (6 / (T : ℝ) + 98 / (H : ℝ) + delta)

lemma inverseSquareFourthUniformMajorant_nonneg
    {y T H : ℕ} {delta : ℝ}
    (hT : 0 < T) (hH : 0 < H) (hdelta : 0 ≤ delta) :
    0 ≤ inverseSquareFourthUniformMajorant y T H delta := by
  unfold inverseSquareFourthUniformMajorant
  positivity

private lemma long_le_product_mul_two_div
    {L S T : ℕ} (hL : 0 < L) (hT : 0 < T) (hTS : T < 2 * S) :
    (L : ℝ) ≤ (L : ℝ) * (S : ℝ) * (2 / (T : ℝ)) := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hTSR : (T : ℝ) ≤ 2 * S := by exact_mod_cast hTS.le
  have hone : (1 : ℝ) ≤ (S : ℝ) * (2 / (T : ℝ)) := by
    rw [show (S : ℝ) * (2 / (T : ℝ)) =
      (2 * (S : ℝ)) / T by ring]
    exact (le_div_iff₀ hTR).2 (by simpa using hTSR)
  calc
    (L : ℝ) = (L : ℝ) * 1 := by ring
    _ ≤ (L : ℝ) * ((S : ℝ) * (2 / (T : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hone (by positivity)
    _ = (L : ℝ) * (S : ℝ) * (2 / (T : ℝ)) := by ring

lemma inverseSquareOrientedBlockMajorant_le_uniform
    {V delta : ℝ} {y T M K H : ℕ}
    (hT : 0 < T) (hH : 0 < H) (hM : 0 < M) (hK : 0 < K)
    (hprod : M * K ≤ y) (hTM : T < 2 * M) (hTK : T < 2 * K)
    (hdelta : 0 ≤ delta) (hV : V = T) :
    inverseSquareOrientedBlockMajorant V M K H delta ≤
      inverseSquareFourthUniformMajorant y T H delta := by
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hprodR : (M : ℝ) * K ≤ y := by exact_mod_cast hprod
  have hMy : M ≤ y := by nlinarith
  have hlogM0 : 0 ≤ Real.log (2 * (M : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * M by omega))
  have hlog : Real.log (2 * (M : ℝ)) ≤ Real.log (2 * (y : ℝ)) :=
    Real.log_le_log (by positivity)
      (by exact_mod_cast Nat.mul_le_mul_left 2 hMy)
  have hD : ((K / H : ℕ) : ℝ) ≤ (K : ℝ) / (H : ℝ) := Nat.cast_div_le
  have hclose : (M : ℝ) * (((2 * (K / H) + 1 : ℕ) : ℝ)) ≤
      ((M : ℝ) * K) * (2 / (H : ℝ)) + (M : ℝ) := by
    push_cast
    calc
      (M : ℝ) * (2 * (K / H : ℕ) + 1) ≤
          (M : ℝ) * (2 * ((K : ℝ) / H) + 1) := by gcongr
      _ = ((M : ℝ) * K) * (2 / (H : ℝ)) + (M : ℝ) := by ring
  have hMcost := long_le_product_mul_two_div hM hT hTK
  have hKcost : (2 : ℝ) * K ≤
      ((M : ℝ) * K) * (4 / (T : ℝ)) := by
    have hbase := long_le_product_mul_two_div hK hT hTM
    calc
      (2 : ℝ) * K ≤ 2 * ((K : ℝ) * M * (2 / (T : ℝ))) := by
        gcongr
      _ = ((M : ℝ) * K) * (4 / (T : ℝ)) := by ring
  have hbracket :
      (M : ℝ) * (((2 * (K / H) + 1 : ℕ) : ℝ)) +
          orientedCorrelationBound M H delta * (K : ℝ) ≤
        ((M : ℝ) * K) *
          (6 / (T : ℝ) + 98 / (H : ℝ) + delta) := by
    unfold orientedCorrelationBound
    calc
      _ ≤ (((M : ℝ) * K) * (2 / (H : ℝ)) + (M : ℝ)) +
          (2 + 96 * (M : ℝ) / H + delta * M) * K := by gcongr
      _ = ((M : ℝ) + 2 * K) +
          ((M : ℝ) * K) * (98 / (H : ℝ) + delta) := by
        field_simp [ne_of_gt hHR]
        ring
      _ ≤ ((M : ℝ) * K) * (6 / (T : ℝ)) +
          ((M : ℝ) * K) * (98 / (H : ℝ) + delta) := by
        gcongr
        calc
          (M : ℝ) + 2 * K ≤
              ((M : ℝ) * K) * (2 / (T : ℝ)) +
                ((M : ℝ) * K) * (4 / (T : ℝ)) :=
            add_le_add hMcost hKcost
          _ = ((M : ℝ) * K) * (6 / (T : ℝ)) := by ring
      _ = ((M : ℝ) * K) *
          (6 / (T : ℝ) + 98 / (H : ℝ) + delta) := by ring
  have hfac : 0 ≤ 6 / (T : ℝ) + 98 / (H : ℝ) + delta := by positivity
  subst V
  unfold inverseSquareOrientedBlockMajorant
  unfold inverseSquareFourthUniformMajorant
  calc
    _ = (8 / 3 : ℝ) * ((M : ℝ) * K) *
        (Real.log (2 * (M : ℝ))) ^ 2 *
        (Real.log (T : ℝ) + 3) ^ 2 *
        ((M : ℝ) * (((2 * (K / H) + 1 : ℕ) : ℝ)) +
          orientedCorrelationBound M H delta * K) := by ring
    _ ≤ (8 / 3 : ℝ) * ((M : ℝ) * K) *
        (Real.log (2 * (M : ℝ))) ^ 2 *
        (Real.log (T : ℝ) + 3) ^ 2 *
        (((M : ℝ) * K) *
          (6 / (T : ℝ) + 98 / (H : ℝ) + delta)) := by gcongr
    _ ≤ (8 / 3 : ℝ) * (y : ℝ) *
        (Real.log (2 * (y : ℝ))) ^ 2 *
        (Real.log (T : ℝ) + 3) ^ 2 *
        ((y : ℝ) *
          (6 / (T : ℝ) + 98 / (H : ℝ) + delta)) := by gcongr
    _ = _ := by ring

def inverseSquareReverseBlockMajorant
    (V : ℝ) (M K H : ℕ) (delta : ℝ) : ℝ :=
  ((8 / 3 : ℝ) * (K : ℝ) * (Real.log V + 3) ^ 2) *
    (((K : ℝ) * (((2 * (M / H) + 1 : ℕ) : ℝ)) +
        orientedCorrelationBound K H delta * (M : ℝ)) *
      ((M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2))

lemma inverseSquareReverseBlockMajorant_nonneg
    {V delta : ℝ} {M K H : ℕ}
    (hK : 0 < K) (hH : 0 < H) (hdelta : 0 ≤ delta) :
    0 ≤ inverseSquareReverseBlockMajorant V M K H delta := by
  unfold inverseSquareReverseBlockMajorant orientedCorrelationBound
  positivity

/-- The complementary orientation, where the fourth coefficient is on the
long Cauchy--Schwarz variable. -/
theorem norm_inverseSquareVaughanBlock_sq_le_reverse
    {X delta U V : ℝ} {x y M K H C : ℕ}
    (hX : 0 < X) (hH : 0 < H) (hdelta : 0 ≤ delta)
    (hV : 1 ≤ V) (hM : 0 < M) (hK : 0 < K) (hMK : M ≤ K)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hXratio : (H : ℝ) ^ 2 * (y : ℝ) ^ 2 ≤ X)
    (hsize : inverseSquareCentralCorrelationSizeCondition K)
    (hC : 2 ≤ C) (hbaseCap : baseShift K ≤ K / C)
    (hlargeEnvelope : ∀ Q : ℝ, 0 < Q →
      (K : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * (K : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q K C ≤ delta * K) :
    ‖inverseSquareBilinearBlock X x y M (2 * M) K (2 * K)
        (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V)‖ ^ 2 ≤
      inverseSquareReverseBlockMajorant V M K H delta := by
  rw [inverseSquareBilinearBlock_comm]
  let D := M / H
  let B := orientedCorrelationBound K H delta
  have hKone : 1 ≤ K := hK
  have hB : 0 ≤ B := by
    dsimp only [B, orientedCorrelationBound]
    positivity
  have hcorr : ∀ r ∈ Finset.Ioc M (2 * M),
      ∀ s ∈ Finset.Ioc M (2 * M), r < s → D < s - r →
      ‖∑ k ∈ Finset.Ioc K (2 * K),
        inverseSquareCutoffWeight X x y k s *
          conj (inverseSquareCutoffWeight X x y k r)‖ ≤ B := by
    intro r hr s hs hrs hfar
    have hraw := norm_inverseSquareCentral_cutoff_correlation_le_separated
      hX (show (0 : ℝ) < (H : ℝ) ^ 2 by positivity) hdelta
      hKone hM hMK hr hs hrs hfar hXlo hXhi hyx hXratio
      hsize hC hbaseCap hlargeEnvelope
    have hfrac := separated_fraction_le hK hH (K := M)
    dsimp only [D] at hraw
    dsimp only [B, orientedCorrelationBound]
    exact hraw.trans (by linarith)
  have hbase := norm_inverseSquareCentral_bilinearBlock_sq_le_hybrid
    (cutoffFourthCoefficient V) (cutoffMangoldtCoefficient U)
    hX hKone hM hMK hXlo hXhi hyx hsize hC hbaseCap B hB hcorr
  let EA := (M : ℝ) * (Real.log (2 * (M : ℝ))) ^ 2
  let EB := (8 / 3 : ℝ) * (K : ℝ) * (Real.log V + 3) ^ 2
  have hEA : (∑ m ∈ Finset.Ioc M (2 * M),
      ‖cutoffMangoldtCoefficient U m‖ ^ 2) ≤ EA :=
    sum_norm_sq_cutoffMangoldtCoefficient_Ioc_le U M
  have hEB : (∑ k ∈ Finset.Ioc K (2 * K),
      ‖cutoffFourthCoefficient V k‖ ^ 2) ≤ EB :=
    sum_norm_sq_cutoffFourthCoefficient_Ioc_le hV K
  have hEB0 : 0 ≤ EB := by dsimp only [EB]; positivity
  have hinner :
      (((K : ℝ) * (((2 * D + 1 : ℕ) : ℝ)) + B * (M : ℝ)) *
        (∑ m ∈ Finset.Ioc M (2 * M),
          ‖cutoffMangoldtCoefficient U m‖ ^ 2)) ≤
      (((K : ℝ) * (((2 * D + 1 : ℕ) : ℝ)) + B * (M : ℝ)) * EA) := by
    exact mul_le_mul_of_nonneg_left hEA (by positivity)
  calc
    _ ≤ (∑ k ∈ Finset.Ioc K (2 * K),
        ‖cutoffFourthCoefficient V k‖ ^ 2) *
      (((K : ℝ) * (((2 * D + 1 : ℕ) : ℝ)) + B * (M : ℝ)) *
        (∑ m ∈ Finset.Ioc M (2 * M),
          ‖cutoffMangoldtCoefficient U m‖ ^ 2)) := hbase
    _ ≤ EB *
      (((K : ℝ) * (((2 * D + 1 : ℕ) : ℝ)) + B * (M : ℝ)) * EA) := by
      exact mul_le_mul hEB hinner (by positivity) hEB0
    _ = inverseSquareReverseBlockMajorant V M K H delta := by
      simp only [EA, EB, D, B, inverseSquareReverseBlockMajorant]

lemma inverseSquareReverseBlockMajorant_le_uniform
    {V delta : ℝ} {y T M K H : ℕ}
    (hT : 0 < T) (hH : 0 < H) (hM : 0 < M) (hK : 0 < K)
    (hprod : M * K ≤ y) (hTM : T < 2 * M) (hTK : T < 2 * K)
    (hdelta : 0 ≤ delta) (hV : V = T) :
    inverseSquareReverseBlockMajorant V M K H delta ≤
      inverseSquareFourthUniformMajorant y T H delta := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hprodR : (M : ℝ) * K ≤ y := by exact_mod_cast hprod
  have hMy : M ≤ y := by nlinarith
  have hlogM0 : 0 ≤ Real.log (2 * (M : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * M by omega))
  have hlog : Real.log (2 * (M : ℝ)) ≤ Real.log (2 * (y : ℝ)) :=
    Real.log_le_log (by positivity)
      (by exact_mod_cast Nat.mul_le_mul_left 2 hMy)
  have hD : ((M / H : ℕ) : ℝ) ≤ (M : ℝ) / (H : ℝ) := Nat.cast_div_le
  have hclose : (K : ℝ) * (((2 * (M / H) + 1 : ℕ) : ℝ)) ≤
      ((M : ℝ) * K) * (2 / (H : ℝ)) + (K : ℝ) := by
    push_cast
    calc
      (K : ℝ) * (2 * (M / H : ℕ) + 1) ≤
          (K : ℝ) * (2 * ((M : ℝ) / H) + 1) := by gcongr
      _ = ((M : ℝ) * K) * (2 / (H : ℝ)) + (K : ℝ) := by ring
  have hKcost := long_le_product_mul_two_div hK hT hTM
  have hMcost : (2 : ℝ) * M ≤
      ((M : ℝ) * K) * (4 / (T : ℝ)) := by
    have hbase := long_le_product_mul_two_div hM hT hTK
    calc
      (2 : ℝ) * M ≤ 2 * ((M : ℝ) * K * (2 / (T : ℝ))) := by
        gcongr
      _ = ((M : ℝ) * K) * (4 / (T : ℝ)) := by ring
  have hbracket :
      (K : ℝ) * (((2 * (M / H) + 1 : ℕ) : ℝ)) +
          orientedCorrelationBound K H delta * (M : ℝ) ≤
        ((M : ℝ) * K) *
          (6 / (T : ℝ) + 98 / (H : ℝ) + delta) := by
    unfold orientedCorrelationBound
    calc
      _ ≤ (((M : ℝ) * K) * (2 / (H : ℝ)) + (K : ℝ)) +
          (2 + 96 * (K : ℝ) / H + delta * K) * M := by gcongr
      _ = ((K : ℝ) + 2 * M) +
          ((M : ℝ) * K) * (98 / (H : ℝ) + delta) := by
        field_simp [ne_of_gt hHR]
        ring
      _ ≤ ((M : ℝ) * K) * (6 / (T : ℝ)) +
          ((M : ℝ) * K) * (98 / (H : ℝ) + delta) := by
        gcongr
        calc
          (K : ℝ) + 2 * M ≤
              ((K : ℝ) * M) * (2 / (T : ℝ)) +
                ((M : ℝ) * K) * (4 / (T : ℝ)) :=
            add_le_add hKcost hMcost
          _ = ((M : ℝ) * K) * (6 / (T : ℝ)) := by ring
      _ = ((M : ℝ) * K) *
          (6 / (T : ℝ) + 98 / (H : ℝ) + delta) := by ring
  have hfac : 0 ≤ 6 / (T : ℝ) + 98 / (H : ℝ) + delta := by positivity
  subst V
  unfold inverseSquareReverseBlockMajorant
  unfold inverseSquareFourthUniformMajorant
  calc
    _ = (8 / 3 : ℝ) * ((M : ℝ) * K) *
        (Real.log (2 * (M : ℝ))) ^ 2 *
        (Real.log (T : ℝ) + 3) ^ 2 *
        ((K : ℝ) * (((2 * (M / H) + 1 : ℕ) : ℝ)) +
          orientedCorrelationBound K H delta * M) := by ring
    _ ≤ (8 / 3 : ℝ) * ((M : ℝ) * K) *
        (Real.log (2 * (M : ℝ))) ^ 2 *
        (Real.log (T : ℝ) + 3) ^ 2 *
        (((M : ℝ) * K) *
          (6 / (T : ℝ) + 98 / (H : ℝ) + delta)) := by gcongr
    _ ≤ (8 / 3 : ℝ) * (y : ℝ) *
        (Real.log (2 * (y : ℝ))) ^ 2 *
        (Real.log (T : ℝ) + 3) ^ 2 *
        ((y : ℝ) *
          (6 / (T : ℝ) + 98 / (H : ℝ) + delta)) := by gcongr
    _ = _ := by ring

lemma inverseSquareVaughanBlock_eq_zero_of_product_above
    (X U V : ℝ) (x y M K : ℕ) (hy : y < M * K) :
    inverseSquareBilinearBlock X x y M (2 * M) K (2 * K)
      (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V) = 0 := by
  unfold inverseSquareBilinearBlock
  apply Finset.sum_eq_zero
  intro m hm
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro k hk
  apply mul_eq_zero_of_right
  unfold inverseSquareCutoffWeight
  rw [if_neg]
  intro hactive
  have hmlo := (Finset.mem_Ioc.mp hm).1
  have hklo := (Finset.mem_Ioc.mp hk).1
  have hprod : M * K < m * k := by
    calc
      M * K ≤ m * K := Nat.mul_le_mul_right K hmlo.le
      _ < m * k := Nat.mul_lt_mul_of_pos_left hklo (by omega)
  exact (not_le_of_gt (hy.trans hprod)) hactive.2

lemma inverseSquareVaughanBlock_eq_zero_of_product_below
    (X U V : ℝ) (x y M K : ℕ) (hx : 4 * M * K ≤ x) :
    inverseSquareBilinearBlock X x y M (2 * M) K (2 * K)
      (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V) = 0 := by
  unfold inverseSquareBilinearBlock
  apply Finset.sum_eq_zero
  intro m hm
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro k hk
  apply mul_eq_zero_of_right
  unfold inverseSquareCutoffWeight
  rw [if_neg]
  intro hactive
  have hmhi := (Finset.mem_Ioc.mp hm).2
  have hkhi := (Finset.mem_Ioc.mp hk).2
  nlinarith

lemma inverseSquareVaughanBlock_eq_zero_of_mangoldt_cutoff
    (X U V : ℝ) (x y M K : ℕ) (hU : (2 * M : ℕ) ≤ U) :
    inverseSquareBilinearBlock X x y M (2 * M) K (2 * K)
      (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V) = 0 := by
  unfold inverseSquareBilinearBlock
  apply Finset.sum_eq_zero
  intro m hm
  apply mul_eq_zero_of_left
  unfold cutoffMangoldtCoefficient
  rw [if_neg]
  have hmhiR : (m : ℝ) ≤ (2 * M : ℕ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hm).2
  exact not_lt_of_ge (hmhiR.trans hU)

lemma inverseSquareVaughanBlock_eq_zero_of_fourth_cutoff
    (X U V : ℝ) (x y M K : ℕ) (hV : (2 * K : ℕ) ≤ V) :
    inverseSquareBilinearBlock X x y M (2 * M) K (2 * K)
      (cutoffMangoldtCoefficient U) (cutoffFourthCoefficient V) = 0 := by
  unfold inverseSquareBilinearBlock
  apply Finset.sum_eq_zero
  intro m hm
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro k hk
  apply mul_eq_zero_of_left
  unfold cutoffFourthCoefficient
  rw [if_neg]
  have hkhiR : (k : ℝ) ≤ (2 * K : ℕ) := by
    exact_mod_cast (Finset.mem_Ioc.mp hk).2
  exact not_lt_of_ge (hkhiR.trans hV)

/-- Every dyadic block has one uniform bound once all scales capable of
meeting the product interval satisfy the capped large-frequency estimate. -/
theorem norm_inverseSquare_fourthDyadicBlock_sq_le_uniform
    {X delta : ℝ} {x y T H C alpha beta : ℕ}
    (hX : 0 < X) (hT : 0 < T) (hH : 0 < H) (hdelta : 0 ≤ delta)
    (hC : 2 ≤ C)
    (hsize : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      inverseSquareCentralCorrelationSizeCondition L)
    (hbaseCap : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y → baseShift L ≤ L / C)
    (hlargeEnvelope : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      ∀ Q : ℝ, 0 < Q → (L : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * (L : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q L C ≤ delta * L)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hXratio : (H : ℝ) ^ 2 * (y : ℝ) ^ 2 ≤ X) :
    ‖inverseSquareVaughanFourthDyadicBlock X T T x y alpha beta‖ ^ 2 ≤
      inverseSquareFourthUniformMajorant y T H delta := by
  let M : ℕ := 2 ^ alpha
  let K : ℕ := 2 ^ beta
  have hM : 0 < M := by dsimp only [M]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  rw [inverseSquareVaughanFourthDyadicBlock_eq_full]
  simp only [inverseSquareVaughanFourthFullDyadicBlock, pow_succ,
    Nat.mul_comm]
  change ‖inverseSquareBilinearBlock X x y M (2 * M) K (2 * K)
      (cutoffMangoldtCoefficient T) (cutoffFourthCoefficient T)‖ ^ 2 ≤ _
  by_cases hyprod : y < M * K
  · rw [inverseSquareVaughanBlock_eq_zero_of_product_above
      X T T x y M K hyprod, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact inverseSquareFourthUniformMajorant_nonneg hT hH hdelta
  have hprod : M * K ≤ y := Nat.le_of_not_gt hyprod
  by_cases hxprod : 4 * M * K ≤ x
  · rw [inverseSquareVaughanBlock_eq_zero_of_product_below
      X T T x y M K hxprod, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact inverseSquareFourthUniformMajorant_nonneg hT hH hdelta
  have hxprod' : x < 4 * M * K := Nat.lt_of_not_ge hxprod
  by_cases hTM : 2 * M ≤ T
  · rw [inverseSquareVaughanBlock_eq_zero_of_mangoldt_cutoff
      X T T x y M K (by exact_mod_cast hTM), norm_zero,
      zero_pow (by norm_num : 2 ≠ 0)]
    exact inverseSquareFourthUniformMajorant_nonneg hT hH hdelta
  have hTM' : T < 2 * M := Nat.lt_of_not_ge hTM
  by_cases hTK : 2 * K ≤ T
  · rw [inverseSquareVaughanBlock_eq_zero_of_fourth_cutoff
      X T T x y M K (by exact_mod_cast hTK), norm_zero,
      zero_pow (by norm_num : 2 ≠ 0)]
    exact inverseSquareFourthUniformMajorant_nonneg hT hH hdelta
  have hTK' : T < 2 * K := Nat.lt_of_not_ge hTK
  rcases le_total K M with hKM | hMK
  · have hxM : x < 4 * M ^ 2 := hxprod'.trans_le (by
      nlinarith [Nat.mul_le_mul_left M hKM])
    have hMy : M ≤ y := by nlinarith
    have hblock := norm_inverseSquareVaughanBlock_sq_le_oriented
      (U := (T : ℝ)) (V := (T : ℝ)) hX hH hdelta
      (by exact_mod_cast hT) hM hK hKM
      hXlo hXhi hyx hXratio (hsize M hxM hMy) hC
      (hbaseCap M hxM hMy) (hlargeEnvelope M hxM hMy)
    exact hblock.trans (inverseSquareOrientedBlockMajorant_le_uniform
      hT hH hM hK hprod hTM' hTK' hdelta rfl)
  · have hxK : x < 4 * K ^ 2 := hxprod'.trans_le (by
      nlinarith [Nat.mul_le_mul_right K hMK])
    have hKy : K ≤ y := by nlinarith
    have hblock := norm_inverseSquareVaughanBlock_sq_le_reverse
      (U := (T : ℝ)) (V := (T : ℝ)) hX hH hdelta
      (by exact_mod_cast hT) hM hK hMK
      hXlo hXhi hyx hXratio (hsize K hxK hKy) hC
      (hbaseCap K hxK hKy) (hlargeEnvelope K hxK hKy)
    exact hblock.trans (inverseSquareReverseBlockMajorant_le_uniform
      hT hH hM hK hprod hTM' hTK' hdelta rfl)

/-- Sum the exact two-dimensional dyadic decomposition. -/
theorem norm_weightedVaughanIntervalFour_inverseSquare_le
    {X delta : ℝ} {x y T H C : ℕ}
    (hX : 0 < X) (hT : 0 < T) (hH : 0 < H) (hdelta : 0 ≤ delta)
    (hC : 2 ≤ C)
    (hsize : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      inverseSquareCentralCorrelationSizeCondition L)
    (hbaseCap : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y → baseShift L ≤ L / C)
    (hlargeEnvelope : ∀ L : ℕ, x < 4 * L ^ 2 → L ≤ y →
      ∀ Q : ℝ, 0 < Q → (L : ℝ) ^ 3 ≤ 4 * Q →
      Q ≤ inverseSquareFrequencyConstant * (L : ℝ) ^ 31 →
      cappedInverseSquareCorrelationEnvelope Q L C ≤ delta * L)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hXratio : (H : ℝ) ^ 2 * (y : ℝ) ^ 2 ≤ X) :
    ‖weightedVaughanIntervalFour (inverseSquareWeight X) T T x y‖ ≤
      ((dyadicExponentRange y).card : ℝ) ^ 2 *
        Real.sqrt (inverseSquareFourthUniformMajorant y T H delta) := by
  let A := inverseSquareFourthUniformMajorant y T H delta
  have hA : 0 ≤ A := inverseSquareFourthUniformMajorant_nonneg hT hH hdelta
  have hblock (alpha beta : ℕ) :
      ‖inverseSquareVaughanFourthDyadicBlock X T T x y alpha beta‖ ≤
        Real.sqrt A := by
    apply (Real.le_sqrt (norm_nonneg _) hA).2
    exact norm_inverseSquare_fourthDyadicBlock_sq_le_uniform
      hX hT hH hdelta hC hsize hbaseCap hlargeEnvelope
      hXlo hXhi hyx hXratio
  rw [weightedVaughanIntervalFour_reciprocal_eq_neg_sum_dyadicBlocks
    X (by exact_mod_cast hT) (by exact_mod_cast hT) x y, norm_neg]
  calc
    ‖∑ alpha ∈ dyadicExponentRange y,
        ∑ beta ∈ dyadicExponentRange y,
          inverseSquareVaughanFourthDyadicBlock X T T x y alpha beta‖ ≤
      ∑ alpha ∈ dyadicExponentRange y,
        ‖∑ beta ∈ dyadicExponentRange y,
          inverseSquareVaughanFourthDyadicBlock X T T x y alpha beta‖ :=
      norm_sum_le _ _
    _ ≤ ∑ alpha ∈ dyadicExponentRange y,
        ∑ beta ∈ dyadicExponentRange y,
          ‖inverseSquareVaughanFourthDyadicBlock X T T x y alpha beta‖ := by
      apply Finset.sum_le_sum
      intro alpha halpha
      exact norm_sum_le _ _
    _ ≤ ∑ _alpha ∈ dyadicExponentRange y,
        ∑ _beta ∈ dyadicExponentRange y, Real.sqrt A := by
      apply Finset.sum_le_sum
      intro alpha halpha
      apply Finset.sum_le_sum
      intro beta hbeta
      exact hblock alpha beta
    _ = ((dyadicExponentRange y).card : ℝ) ^ 2 * Real.sqrt A := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring

end

end InverseSquareVaughanHybrid
end Erdos378
