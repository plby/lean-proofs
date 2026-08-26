import ErdosProblems.Erdos327.Analytic.ThreeFormBoxSharp
import ErdosProblems.Erdos327.Analytic.ThreeFormSmallCutoff

/-!
# Sharp three-form boxes in both cutoff orderings

The finite-sieve schedule crosses the roughness cutoff.  This file combines
the existing `L ≤ z` box bounds with the stronger Euler products available
when `z < L`.
-/

namespace Erdos327.Analytic

open Real Finset
open scoped BigOperators

noncomputable section

/-- Source box estimate in the `z < L` branch. -/
theorem source_threeFormBoxSum_le_sharp_of_lt
    {L z X R : ℕ} (hz : 2 ≤ z) (hzL : z < L) :
    finiteWeightBoxSum
        (centeredRetainedFamily (P := oddPrimesUpTo z)
          (sourceQU L) (sourceQV L) (sourceQSum L)) X ≤
      8 * (X : ℝ) ^ 2 *
          exp (sourceSmallCutoffMertensEnvelope z) +
        8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) +
        ((2 * R + 1 : ℕ) : ℝ) *
          (z : ℝ) ^ (2 * R) * (3 : ℝ) ^ (2 * R) *
          (9 * (X : ℝ) + (z : ℝ) ^ (2 * R)) := by
  let w := centeredRetainedFamily (P := oddPrimesUpTo z)
    (sourceQU L) (sourceQV L) (sourceQSum L)
  let ell := centeredLossFamily (P := oddPrimesUpTo z)
    (sourceQU L) (sourceQV L) (sourceQSum L)
  have hprime : ∀ p ∈ oddPrimesUpTo z, p.Prime :=
    fun p hp ↦ (mem_oddPrimesUpTo.mp hp).1
  have hPz : oddPrimesUpTo z ⊆ Nat.primesLE z :=
    fun _ hp ↦ mem_of_mem_erase hp
  have hz1 : 1 ≤ z := by omega
  have hlocal (p : oddPrimesUpTo z)
      (u : ZMod (p : ℕ) × ZMod (p : ℕ)) :
      0 ≤ w p u ∧ w p u ≤ 1 := by
    dsimp [w]
    exact centeredLocalWeight_nonneg_le_one
      (sourceQU L p) (sourceQV L p) (sourceQSum L p)
      (sourceQU_nonneg_le_one L p).1
      (sourceQU_nonneg_le_one L p).2
      (sourceQV_nonneg_le_one L p).1
      (sourceQV_nonneg_le_one L p).2
      (sourceQSum_nonneg_le_one L p).1
      (sourceQSum_nonneg_le_one L p).2 u
  have hcomplement : ∀ (p : oddPrimesUpTo z) u,
      w p u + ell p u = 1 := by
    intro p u
    simp [w, ell, centeredLossFamily]
  have hell0 : ∀ (p : oddPrimesUpTo z) u, 0 ≤ ell p u :=
    fun p u ↦ sub_nonneg.mpr (hlocal p u).2
  have hell1 : ∀ (p : oddPrimesUpTo z) u, ell p u ≤ 1 :=
    fun p u ↦ sub_le_self _ (hlocal p u).1
  have hsupport : ∀ p : oddPrimesUpTo z,
      (residueWeightSupport (p : ℕ) (ell p)).card ≤
        3 * (p : ℕ) := by
    intro p
    dsimp [ell]
    exact centeredLossFamily_support_card_le
      (sourceQU L) (sourceQV L) (sourceQSum L) p
  have hmean : ∀ p : oddPrimesUpTo z,
      localLossMean ell p ≤ 3 / (p : ℝ) :=
    localLossMean_le_three_div hprime ell hell1 hsupport
  have hbase :=
    finiteWeightBoxSum_le_primeInvSum_add_truncated_boundary
      (P := oddPrimesUpTo z) (z := z)
      hprime w ell hcomplement hell0 hell1 hsupport
      hPz hmean hz1 X R
  have hproduct :
      (∏ p : oddPrimesUpTo z, localWeightMean w p) ≤
        exp (sourceSmallCutoffMertensEnvelope z) := by
    dsimp [w]
    exact source_localMeanProduct_le_mertens_of_lt hz hzL
  have hproductScaled :
      8 * (X : ℝ) ^ 2 *
          (∏ p : oddPrimesUpTo z, localWeightMean w p) ≤
        8 * (X : ℝ) ^ 2 *
          exp (sourceSmallCutoffMertensEnvelope z) :=
    mul_le_mul_of_nonneg_left hproduct (by positivity)
  change finiteWeightBoxSum w X ≤ _
  exact hbase.trans
    (add_le_add (add_le_add hproductScaled le_rfl) le_rfl)

/-- Mixed box estimate in the `z < L` branch. -/
theorem mixed_threeFormBoxSum_le_sharp_of_lt
    {L z X R : ℕ} {alpha beta s : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hz : 2 ≤ z) (hzL : z < L) :
    finiteWeightBoxSum
        (crossRetainedFamily (P := oddPrimesUpTo z)
          (mixedQU L alpha) (mixedQW L beta)
          (mixedQLinear L s)) X ≤
      8 * (X : ℝ) ^ 2 *
          exp (mixedSmallCutoffMertensEnvelope z) +
        8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) +
        ((2 * R + 1 : ℕ) : ℝ) *
          (z : ℝ) ^ (2 * R) * (3 : ℝ) ^ (2 * R) *
          (9 * (X : ℝ) + (z : ℝ) ^ (2 * R)) := by
  let w := crossRetainedFamily (P := oddPrimesUpTo z)
    (mixedQU L alpha) (mixedQW L beta) (mixedQLinear L s)
  let ell := crossLossFamily (P := oddPrimesUpTo z)
    (mixedQU L alpha) (mixedQW L beta) (mixedQLinear L s)
  have hprime : ∀ p ∈ oddPrimesUpTo z, p.Prime :=
    fun p hp ↦ (mem_oddPrimesUpTo.mp hp).1
  have hodd : ∀ p ∈ oddPrimesUpTo z, p ≠ 2 :=
    fun p hp ↦ (mem_oddPrimesUpTo.mp hp).2.2
  have hPz : oddPrimesUpTo z ⊆ Nat.primesLE z :=
    fun _ hp ↦ mem_of_mem_erase hp
  have hz1 : 1 ≤ z := by omega
  have hlocal (p : oddPrimesUpTo z)
      (u : ZMod (p : ℕ) × ZMod (p : ℕ)) :
      0 ≤ w p u ∧ w p u ≤ 1 := by
    dsimp [w]
    exact crossLocalWeight_nonneg_le_one
      (mixedQU L alpha p) (mixedQW L beta p)
      (mixedQLinear L s p)
      (mixedQU_nonneg_le_one ha0 ha1 L p).1
      (mixedQU_nonneg_le_one ha0 ha1 L p).2
      (mixedQW_nonneg_le_one hb0 hb1 L p).1
      (mixedQW_nonneg_le_one hb0 hb1 L p).2
      (mixedQLinear_nonneg_le_one hs0 hs1 L p).1
      (mixedQLinear_nonneg_le_one hs0 hs1 L p).2 u
  have hcomplement : ∀ (p : oddPrimesUpTo z) u,
      w p u + ell p u = 1 := by
    intro p u
    simp [w, ell, crossLossFamily]
  have hell0 : ∀ (p : oddPrimesUpTo z) u, 0 ≤ ell p u :=
    fun p u ↦ sub_nonneg.mpr (hlocal p u).2
  have hell1 : ∀ (p : oddPrimesUpTo z) u, ell p u ≤ 1 :=
    fun p u ↦ sub_le_self _ (hlocal p u).1
  have hsupport : ∀ p : oddPrimesUpTo z,
      (residueWeightSupport (p : ℕ) (ell p)).card ≤
        3 * (p : ℕ) := by
    intro p
    dsimp [ell]
    exact crossLossFamily_support_card_le hprime hodd
      (mixedQU L alpha) (mixedQW L beta)
      (mixedQLinear L s) p
  have hmean : ∀ p : oddPrimesUpTo z,
      localLossMean ell p ≤ 3 / (p : ℝ) :=
    localLossMean_le_three_div hprime ell hell1 hsupport
  have hbase :=
    finiteWeightBoxSum_le_primeInvSum_add_truncated_boundary
      (P := oddPrimesUpTo z) (z := z)
      hprime w ell hcomplement hell0 hell1 hsupport
      hPz hmean hz1 X R
  have hproduct :
      (∏ p : oddPrimesUpTo z, localWeightMean w p) ≤
        exp (mixedSmallCutoffMertensEnvelope z) := by
    dsimp [w]
    exact mixed_localMeanProduct_le_mertens_of_lt
      ha0 ha1 hb0 hb1 hs0 hs1 hz hzL
  have hproductScaled :
      8 * (X : ℝ) ^ 2 *
          (∏ p : oddPrimesUpTo z, localWeightMean w p) ≤
        8 * (X : ℝ) ^ 2 *
          exp (mixedSmallCutoffMertensEnvelope z) :=
    mul_le_mul_of_nonneg_left hproduct (by positivity)
  change finiteWeightBoxSum w X ≤ _
  exact hbase.trans
    (add_le_add (add_le_add hproductScaled le_rfl) le_rfl)

/-- Piecewise source envelope valid in both cutoff orderings. -/
noncomputable def sourceAllCutoffMertensEnvelope
    (L z : ℕ) : ℝ :=
  if L ≤ z then sourceMertensEnvelope L z
  else sourceSmallCutoffMertensEnvelope z

/-- Piecewise mixed envelope valid in both cutoff orderings. -/
noncomputable def mixedAllCutoffMertensEnvelope
    (L z : ℕ) (alpha beta s : ℝ) : ℝ :=
  if L ≤ z then mixedMertensEnvelope L z alpha beta s
  else mixedSmallCutoffMertensEnvelope z

/-- Sharp source box estimate without assuming an ordering between `L`
and `z`. -/
theorem source_threeFormBoxSum_le_allCutoffs
    {L z X R : ℕ} (hL : 2 ≤ L) (hz : 2 ≤ z) :
    finiteWeightBoxSum
        (centeredRetainedFamily (P := oddPrimesUpTo z)
          (sourceQU L) (sourceQV L) (sourceQSum L)) X ≤
      8 * (X : ℝ) ^ 2 *
          exp (sourceAllCutoffMertensEnvelope L z) +
        8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) +
        ((2 * R + 1 : ℕ) : ℝ) *
          (z : ℝ) ^ (2 * R) * (3 : ℝ) ^ (2 * R) *
          (9 * (X : ℝ) + (z : ℝ) ^ (2 * R)) := by
  by_cases hLz : L ≤ z
  · simpa [sourceAllCutoffMertensEnvelope, hLz] using
      (source_threeFormBoxSum_le_sharp
        (L := L) (z := z) (X := X) (R := R) hL hLz)
  · have hzL : z < L := Nat.lt_of_not_ge hLz
    simpa [sourceAllCutoffMertensEnvelope, hLz] using
      (source_threeFormBoxSum_le_sharp_of_lt
        (L := L) (z := z) (X := X) (R := R) hz hzL)

/-- Sharp mixed box estimate without assuming an ordering between `L`
and `z`. -/
theorem mixed_threeFormBoxSum_le_allCutoffs
    {L z X R : ℕ} {alpha beta s : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hL : 2 ≤ L) (hz : 2 ≤ z) :
    finiteWeightBoxSum
        (crossRetainedFamily (P := oddPrimesUpTo z)
          (mixedQU L alpha) (mixedQW L beta)
          (mixedQLinear L s)) X ≤
      8 * (X : ℝ) ^ 2 *
          exp (mixedAllCutoffMertensEnvelope L z alpha beta s) +
        8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) +
        ((2 * R + 1 : ℕ) : ℝ) *
          (z : ℝ) ^ (2 * R) * (3 : ℝ) ^ (2 * R) *
          (9 * (X : ℝ) + (z : ℝ) ^ (2 * R)) := by
  by_cases hLz : L ≤ z
  · simpa [mixedAllCutoffMertensEnvelope, hLz] using
      (mixed_threeFormBoxSum_le_sharp
        (L := L) (z := z) (X := X) (R := R)
        ha0 ha1 hb0 hb1 hs0 hs1 hL hLz)
  · have hzL : z < L := Nat.lt_of_not_ge hLz
    simpa [mixedAllCutoffMertensEnvelope, hLz] using
      (mixed_threeFormBoxSum_le_sharp_of_lt
        (L := L) (z := z) (X := X) (R := R)
        ha0 ha1 hb0 hb1 hs0 hs1 hz hzL)

end

end Erdos327.Analytic
