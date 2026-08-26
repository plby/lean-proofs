import ErdosProblems.Erdos67b.MRGSA10ShiuMajorant

/-!
# The unconditional Shiu mean bound for the A.10 weight

This specializes the generic finite Halberstam--Richert theorem and the
shifted Euler scalar to the exact multiplicative majorant used by the two
source Lemma 2.4 secondary sums.
-/

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b.PrimeEstimates Erdos67b.EulerQuantitative

/-- The exact A.10 Shiu weight has the source `X / log X` mean bound, with
all Euler factors reduced to explicit repository constants. -/
theorem gsA10ShiuWeight_partialSum_le
    {y N : ℕ} (hy : 2 ≤ y) (hyN : y ≤ N) :
    HalberstamScratch.partialSum
        (gsA10ShiuWeight y (Real.log (y : ℝ))⁻¹) N ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          Real.exp
            (primeReciprocals y + (Real.log 2 + 2 * mertensBound) +
              primeQuadraticConstant) := by
  let eta : ℝ := (Real.log (y : ℝ))⁻¹
  let h : ℕ → ℝ := gsA10ShiuWeight y eta
  have heta : 0 ≤ eta := by
    dsimp [eta]
    exact inv_nonneg.mpr (Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ y by omega)))
  have hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n := by
    intro m n hcop
    by_cases hm : m = 0
    · subst m
      have hn : n = 1 := by simpa using hcop
      subst n
      simp [h]
    by_cases hn : n = 0
    · subst n
      have hm1 : m = 1 := by simpa [Nat.coprime_comm] using hcop
      subst m
      simp [h]
    exact gsA10ShiuWeight_mul y eta
      (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)
  have hHR := Erdos67b.MRShiu.partialSum_le_exp
    (h := h) (gsA10ShiuWeight_zero y eta)
    (gsA10ShiuWeight_one y eta) hmul
    (gsA10ShiuWeight_nonneg y eta)
    (gsA10ShiuWeight_primePower_le_one heta) N (hy.trans hyN)
  have hprime : ∀ p : ℕ, p.Prime →
      h p ≤ if p ≤ y then 1 else
        (p : ℝ) ^ (-(Real.log (y : ℝ))⁻¹) := by
    intro p hp
    rw [show h p = gsA10ShiuWeight y eta p by rfl,
      gsA10ShiuWeight_prime y eta hp]
  have hE := Erdos67b.MRShiu.globalEulerExponent_le_shifted
    (h := h) hy hyN hprime
  have hexp := Real.exp_le_exp.mpr hE
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hfactor : 0 ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) := by
    exact div_nonneg
      (mul_nonneg
        (add_nonneg
          (HalberstamScratch.explicitMassConstant_nonneg
            (by norm_num) (by norm_num)) zero_le_one)
        (Nat.cast_nonneg _)) hlog.le
  change HalberstamScratch.partialSum h N ≤ _
  exact hHR.trans (mul_le_mul_of_nonneg_left hexp hfactor)

/-- The same explicit mean bound holds for every stronger high-prime
shift.  This is the form used by the `2 * eta + alpha` cofactor in the
second source secondary sum. -/
theorem gsA10ShiuWeight_partialSum_le_of_invLog_le
    {y N : ℕ} (hy : 2 ≤ y) (hyN : y ≤ N)
    {rho : ℝ} (hrho : (Real.log (y : ℝ))⁻¹ ≤ rho) :
    HalberstamScratch.partialSum (gsA10ShiuWeight y rho) N ≤
      (HalberstamScratch.explicitMassConstant 1 1 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          Real.exp
            (primeReciprocals y + (Real.log 2 + 2 * mertensBound) +
              primeQuadraticConstant) := by
  calc
    HalberstamScratch.partialSum (gsA10ShiuWeight y rho) N ≤
        HalberstamScratch.partialSum
          (gsA10ShiuWeight y (Real.log (y : ℝ))⁻¹) N := by
      unfold HalberstamScratch.partialSum
      apply Finset.sum_le_sum
      intro n _hn
      exact gsA10ShiuWeight_antitone_shift y n hrho
    _ ≤ _ := gsA10ShiuWeight_partialSum_le hy hyN

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.gsA10ShiuWeight_partialSum_le
