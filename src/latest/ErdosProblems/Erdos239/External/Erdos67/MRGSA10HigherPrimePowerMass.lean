import ErdosProblems.Erdos239.External.Erdos67.MRGSA10GeneralizedMangoldtSplit
import ErdosProblems.Erdos239.External.Erdos67.PrimeEstimates

/-!
# The higher-prime-power mass in GS A.10

The generalized Mangoldt coefficient of an ordinary multiplicative
function can lose a factor `2^k` at `p^k`.  This file proves the finite
geometric estimate which makes that loss harmless: after the prefix-count
factor `p^{-k}`, all exponents `k ≥ 2` have total mass `O(p^{-2})`.
-/

open scoped BigOperators

namespace Erdos67.MRHalaszBands

noncomputable section

open Erdos67 Erdos67.PrimeEstimates

/-- The geometric `k ≥ 2` tail attached to one prime. -/
theorem sum_geometricMangoldtPrimePowerTail_le
    {p : ℝ} (hp : 3 ≤ p) (K : ℕ) :
    (∑ k ∈ Finset.Icc 2 K, (((2 : ℝ) ^ k - 1) / p ^ k)) ≤
      12 / p ^ 2 := by
  let q : ℝ := 2 / p
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hq0 : 0 ≤ q := div_nonneg (by norm_num) hp0.le
  have hq : q ≤ 2 / 3 := by
    dsimp [q]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp
  have hq1 : q < 1 := hq.trans_lt (by norm_num)
  calc
    (∑ k ∈ Finset.Icc 2 K, (((2 : ℝ) ^ k - 1) / p ^ k)) ≤
        ∑ k ∈ Finset.Icc 2 K, q ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have hpk : 0 < p ^ k := pow_pos hp0 _
      calc
        ((2 : ℝ) ^ k - 1) / p ^ k ≤ (2 : ℝ) ^ k / p ^ k :=
          div_le_div_of_nonneg_right (by linarith) hpk.le
        _ = q ^ k := by rw [div_pow]
    _ ≤ q ^ 2 * (∑ j ∈ Finset.range (K + 1), q ^ j) := by
      have hset : Finset.Icc 2 K ⊆ Finset.Ico 2 (K + 1) := by
        intro k hk
        simp only [Finset.mem_Icc, Finset.mem_Ico] at hk ⊢
        omega
      calc
        ∑ k ∈ Finset.Icc 2 K, q ^ k ≤
            ∑ k ∈ Finset.Ico 2 (K + 1), q ^ k := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hset
            (fun _ _ _ ↦ pow_nonneg hq0 _)
        _ = ∑ j ∈ Finset.range (K + 1 - 2), q ^ (2 + j) := by
          rw [Finset.sum_Ico_eq_sum_range]
        _ = q ^ 2 * ∑ j ∈ Finset.range (K + 1 - 2), q ^ j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [pow_add]
        _ ≤ q ^ 2 * ∑ j ∈ Finset.range (K + 1), q ^ j := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg q)
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.sub_le _ _))
            (fun _ _ _ ↦ pow_nonneg hq0 _)
    _ ≤ q ^ 2 / (1 - q) := by
      have hgeom :
          (∑ j ∈ Finset.range (K + 1), q ^ j) =
            (1 - q ^ (K + 1)) / (1 - q) := by
        rw [geom_sum_eq (ne_of_lt hq1)]
        have hqne : q - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt hq1)
        have honeq : 1 - q ≠ 0 := sub_ne_zero.mpr (ne_of_gt hq1)
        field_simp [hqne, honeq]
        ring
      rw [hgeom, div_eq_mul_inv, div_eq_mul_inv]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg q)
      apply mul_le_of_le_one_left (inv_nonneg.mpr (sub_pos.mpr hq1).le)
      have hpow : 0 ≤ q ^ (K + 1) := pow_nonneg hq0 _
      linarith
    _ ≤ 3 * q ^ 2 := by
      rw [div_le_iff₀ (sub_pos.mpr hq1)]
      nlinarith
    _ ≤ 12 / p ^ 2 := by
      dsimp [q]
      rw [div_pow]
      field_simp
      norm_num

/-- The finite higher-prime-power mass above `y`, with the geometric
generalized-Mangoldt majorant already inserted. -/
def gsA10HigherPrimePowerGeometricMass (y X : ℕ) : ℝ :=
  ∑ p ∈ (primesUpTo X).filter (fun p ↦ y < p),
    Real.log p *
      ∑ k ∈ Finset.Icc 2 X,
        (((2 : ℝ) ^ k - 1) / (p : ℝ) ^ k)

/-- The complete higher-prime-power error is `O(log X / y)` times the
reciprocal-prime mass.  This is uniform in the ordinary multiplicative
coefficient and is negligible for the source choice of `y`. -/
theorem gsA10HigherPrimePowerGeometricMass_le
    {y X : ℕ} (hy : 3 ≤ y) :
    gsA10HigherPrimePowerGeometricMass y X ≤
      12 * Real.log X / y * primeReciprocals X := by
  unfold gsA10HigherPrimePowerGeometricMass
  calc
    _ ≤ ∑ p ∈ (primesUpTo X).filter (fun p ↦ y < p),
        Real.log p * (12 / (p : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpmem := Finset.mem_filter.mp hp
      have hpprime := (mem_primesUpTo.mp hpmem.1).1
      have hp3 : (3 : ℝ) ≤ p := by
        exact_mod_cast hy.trans (Nat.le_of_lt hpmem.2)
      exact mul_le_mul_of_nonneg_left
        (sum_geometricMangoldtPrimePowerTail_le hp3 X)
        (Real.log_nonneg (by exact_mod_cast hpprime.one_lt.le))
    _ ≤ ∑ p ∈ (primesUpTo X).filter (fun p ↦ y < p),
        (12 * Real.log X / y) * (1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpmem := Finset.mem_filter.mp hp
      have hpdata := mem_primesUpTo.mp hpmem.1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpdata.1.pos
      have hy0 : (0 : ℝ) < y := by
        exact_mod_cast (show 0 < y by omega)
      have hlog : Real.log (p : ℝ) ≤ Real.log (X : ℝ) :=
        Real.log_le_log hp0 (by exact_mod_cast hpdata.2)
      have hpy : (y : ℝ) ≤ p := by
        exact_mod_cast (Nat.le_of_lt hpmem.2)
      have hlog0 : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hpdata.1.one_lt.le)
      have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
      field_simp
      nlinarith
    _ ≤ ∑ p ∈ primesUpTo X,
        (12 * Real.log X / y) * (1 / (p : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hpfull hpnot
      positivity
    _ = 12 * Real.log X / y * primeReciprocals X := by
      rw [← Finset.mul_sum]
      rw [primeReciprocals_eq_primeHarmonic]
      unfold Erdos697.PrimeHarmonic.sum
      rfl

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.sum_geometricMangoldtPrimePowerTail_le
#print axioms Erdos67.MRHalaszBands.gsA10HigherPrimePowerGeometricMass_le
