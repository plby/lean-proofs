import ErdosProblems.Erdos67b.MRSelectedPowerOrder
import ErdosProblems.Erdos67b.MRSparsePrimeNormalizedEnergy

/-! # Finite sampled energy after paying the cofactor cutoff cost -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrNormSquare_le_of_cutoff_paid {R : ℕ} {theta E : ℝ} (htheta : 0 < theta)
    {z q : ℂ}
    (hpaid : (mrPrimeSieveExponent R)⁻¹ * theta⁻¹ ^ 2 * ‖z‖ ^ 2 ≤ E * ‖q‖ ^ 2) :
    ‖z‖ ^ 2 ≤ E * mrPrimeSieveExponent R * theta ^ 2 * ‖q‖ ^ 2 := by
  have hk := mrPrimeSieveExponent_pos R
  have hid : (mrPrimeSieveExponent R * theta ^ 2) *
      ((mrPrimeSieveExponent R)⁻¹ * theta⁻¹ ^ 2) = 1 := by field_simp
  calc
    _ = (mrPrimeSieveExponent R * theta ^ 2) *
        ((mrPrimeSieveExponent R)⁻¹ * theta⁻¹ ^ 2 * ‖z‖ ^ 2) := by
      rw [← mul_assoc, hid, one_mul]
    _ ≤ (mrPrimeSieveExponent R * theta ^ 2) * (E * ‖q‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hpaid (by positivity)
    _ = _ := by ring

theorem mrSum_normSquare_le_of_cutoff_paid {ι : Type*} (S : Finset ι) (z q : ι → ℂ)
    {R : ℕ} {theta E B : ℝ} (htheta : 0 < theta) (hE : 0 ≤ E)
    (hpaid : ∀ t ∈ S, (mrPrimeSieveExponent R)⁻¹ * theta⁻¹ ^ 2 * ‖z t‖ ^ 2 ≤ E * ‖q t‖ ^ 2)
    (hprime : (∑ t ∈ S, ‖q t‖ ^ 2) ≤ B) :
    (∑ t ∈ S, ‖z t‖ ^ 2) ≤ E * mrPrimeSieveExponent R * theta ^ 2 * B := by
  have hk := mrPrimeSieveExponent_pos R
  calc
    _ ≤ ∑ t ∈ S, E * mrPrimeSieveExponent R * theta ^ 2 * ‖q t‖ ^ 2 :=
      Finset.sum_le_sum (fun t ht ↦ mrNormSquare_le_of_cutoff_paid htheta (hpaid t ht))
    _ = E * mrPrimeSieveExponent R * theta ^ 2 * ∑ t ∈ S, ‖q t‖ ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hprime (by positivity)

def mrSelectedPaidPrimeEnergyBudget (r theta E X : ℝ) (N : ℕ) : ℝ :=
  80000 * mrPrimeBlockMassConstant * E / (r ^ 2 * (Real.log X) ^ 2) +
    2 * E * mrPrimeSieveExponent (mrSelectedPowerOrder r theta) * theta *
      mrPrimeKernelErrorConstant (mrSelectedPowerOrder r theta) * mrPrimeBlockMassConstant * N /
        (r * X ^ ((r * theta / 2) * mrPrimeKernelSaving (mrSelectedPowerOrder r theta)) *
          Real.log X)

theorem mrSelectedPaidPrimeEnergyBudget_nonneg {r theta E X : ℝ}
    (hr : 0 < r) (htheta : 0 < theta) (hE : 0 ≤ E) (hX : 1 ≤ X) (N : ℕ) :
    0 ≤ mrSelectedPaidPrimeEnergyBudget r theta E X N := by
  have := mrPrimeSieveExponent_pos (mrSelectedPowerOrder r theta)
  have := mrPrimeKernelErrorConstant_pos (mrSelectedPowerOrder r theta)
  have := mrPrimeBlockMassConstant_pos
  have := Real.log_nonneg hX
  unfold mrSelectedPaidPrimeEnergyBudget
  positivity

theorem mrSelectedPaid_primeBudget_le {r theta E X P : ℝ}
    (hr : 0 < r) (htheta : 0 < theta) (hE : 0 ≤ E) (hX : 1 < X)
    (hpower : X ^ (r * theta / 2) ≤ P)
    (hlog : (r * theta / 2) * Real.log X ≤ Real.log P) (N : ℕ) :
    E * mrPrimeSieveExponent (mrSelectedPowerOrder r theta) * theta ^ 2 *
      mrSparsePrimeNormalizedBudget (mrSelectedPowerOrder r theta) P N ≤
        mrSelectedPaidPrimeEnergyBudget r theta E X N := by
  let R := mrSelectedPowerOrder r theta
  let alpha := r * theta / 2
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have hXpos : 0 < X := by linarith
  have hLX : 0 < Real.log X := Real.log_pos hX
  have hLP : 0 < Real.log P := (mul_pos halpha hLX).trans_le hlog
  have hPpos : 0 < P := (Real.rpow_pos_of_pos hXpos _).trans_le hpower
  have hk := mrPrimeSieveExponent_pos R
  have hg := mrPrimeKernelSaving_pos R
  have hC := mrPrimeKernelErrorConstant_pos R
  have hm := mrPrimeBlockMassConstant_pos
  have hpow : X ^ (alpha * mrPrimeKernelSaving R) ≤ P ^ mrPrimeKernelSaving R := by
    rw [Real.rpow_mul hXpos.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hXpos.le _) hpower hg.le
  have hden : X ^ (alpha * mrPrimeKernelSaving R) * (alpha * Real.log X) ≤
      P ^ mrPrimeKernelSaving R * Real.log P :=
    mul_le_mul hpow hlog (by positivity) (by positivity)
  have hmain : 20000 * mrPrimeBlockMassConstant * E * theta ^ 2 / (Real.log P) ^ 2 ≤
      80000 * mrPrimeBlockMassConstant * E / (r ^ 2 * (Real.log X) ^ 2) := by
    calc
      _ ≤ 20000 * mrPrimeBlockMassConstant * E * theta ^ 2 / (alpha * Real.log X) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ (by positivity) hlog _)
      _ = _ := by dsimp [alpha]; field_simp; ring
  have herr : E * mrPrimeSieveExponent R * theta ^ 2 *
      (mrPrimeKernelErrorConstant R * mrPrimeBlockMassConstant * N) /
        (P ^ mrPrimeKernelSaving R * Real.log P) ≤
      2 * E * mrPrimeSieveExponent R * theta * mrPrimeKernelErrorConstant R *
        mrPrimeBlockMassConstant * N / (r * X ^ (alpha * mrPrimeKernelSaving R) * Real.log X) := by
    calc
      _ ≤ E * mrPrimeSieveExponent R * theta ^ 2 *
          (mrPrimeKernelErrorConstant R * mrPrimeBlockMassConstant * N) /
          (X ^ (alpha * mrPrimeKernelSaving R) * (alpha * Real.log X)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ = _ := by dsimp [alpha]; field_simp
  unfold mrSparsePrimeNormalizedBudget mrSelectedPaidPrimeEnergyBudget
  change E * mrPrimeSieveExponent R * theta ^ 2 *
    (20000 * mrPrimeBlockMassConstant / (mrPrimeSieveExponent R * (Real.log P) ^ 2) +
      mrPrimeKernelErrorConstant R * mrPrimeBlockMassConstant * N /
        (P ^ mrPrimeKernelSaving R * Real.log P)) ≤ _
  have heq : E * mrPrimeSieveExponent R * theta ^ 2 *
      (20000 * mrPrimeBlockMassConstant / (mrPrimeSieveExponent R * (Real.log P) ^ 2)) =
      20000 * mrPrimeBlockMassConstant * E * theta ^ 2 / (Real.log P) ^ 2 := by field_simp
  rw [mul_add, heq, ← mul_div_assoc]
  exact add_le_add hmain herr

end

end Erdos67b
