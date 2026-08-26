import ErdosProblems.Erdos67b.UniformResidueLogPhase
import ErdosProblems.Erdos67b.MRPrimeMellinKernel

/-!
# Explicit power saving for the finite logarithmic Weyl bands

The residue-prefix estimate is kept as a fixed power of its comparison
scale. This is needed when its error is multiplied by a growing sieve level.
-/

open scoped BigOperators

namespace Erdos67b

noncomputable section

open LogWeylParameters LogBandDecay LogBandCoverage UniformResidueLogPhase
open ResidueLogPhase LogPhaseSum LSeriesLogPhaseBridge

def mrPrimeWeylConstant (R : ℕ) : ℝ :=
  21 + 2 * ∑ r ∈ Finset.Icc 2 R, realStartBandConstant r

theorem mrPrimeWeylConstant_pos (R : ℕ) : 0 < mrPrimeWeylConstant R := by
  have hs : 0 ≤ ∑ r ∈ Finset.Icc 2 R, realStartBandConstant r :=
    Finset.sum_nonneg fun r _ ↦ realStartBandConstant_nonneg r
  unfold mrPrimeWeylConstant
  linarith

theorem mrSavingExponent_antitone : Antitone savingExponent := by
  intro r R hrR
  unfold savingExponent shiftExponent
  apply div_le_div₀ (by positivity)
  · apply one_div_le_one_div_of_le
    · have := depth_pos r
      positivity
    · have hd : depth r ≤ depth R := by simpa only [depth] using Nat.add_le_add_right hrR 1
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hd) (by norm_num)
  · positivity
  · apply pow_le_pow_right₀ (by norm_num)
    simpa only [depth] using Nat.add_le_add_right hrR 1

theorem mrSavingExponent_le_one_div_sixtyFour {R : ℕ} (hR : 2 ≤ R) :
    savingExponent R ≤ 1 / 64 := by
  have h := mrSavingExponent_antitone hR
  norm_num [savingExponent, shiftExponent, depth] at h ⊢
  linarith

theorem mrUniformResidueBlockError_le_power {R X : ℕ}
    (hR : 2 ≤ R) (hX : 1 ≤ X) :
    uniformResidueBlockError R X ≤
      mrPrimeWeylConstant R * (X : ℝ) ^ (1 - savingExponent R) := by
  have hx : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hxpos : (0 : ℝ) < X := zero_lt_one.trans_le hx
  have hd := mrSavingExponent_le_one_div_sixtyFour hR
  let V : ℝ := (X : ℝ) ^ (1 - savingExponent R)
  have hV : 1 ≤ V := Real.one_le_rpow hx (by linarith)
  have hpow (c : ℝ) : (X : ℝ) ^ c * X = (X : ℝ) ^ (c + 1) := by
    rw [Real.rpow_add hxpos, Real.rpow_one]
  have hfirst : (X : ℝ) ^ (-1 / 64 : ℝ) * X ≤ V := by
    rw [hpow]
    apply Real.rpow_le_rpow_of_exponent_le hx
    linarith
  have hterm (r : ℕ) (hr : r ∈ Finset.Icc 2 R) :
      realStartBandConstant r * (X : ℝ) ^ (-savingExponent r) * X ≤
        realStartBandConstant r * V := by
    rw [mul_assoc, hpow]
    apply mul_le_mul_of_nonneg_left _ (realStartBandConstant_nonneg r)
    apply Real.rpow_le_rpow_of_exponent_le hx
    have hh := mrSavingExponent_antitone (Finset.mem_Icc.1 hr).2
    linarith
  have hsum :
      (∑ r ∈ Finset.Icc 2 R, realStartBandConstant r *
        (X : ℝ) ^ (-savingExponent r)) * X ≤
      (∑ r ∈ Finset.Icc 2 R, realStartBandConstant r) * V := by
    simp only [Finset.sum_mul]
    exact Finset.sum_le_sum hterm
  have hlag : (rOneLagBudget X : ℝ) ≤ 2 * V := by
    apply (Erdos1149.AnalyticParameters.natCeil_le_two_mul
      (Real.one_le_rpow hx (by norm_num : (0 : ℝ) ≤ 1 / 16))).trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Real.rpow_le_rpow_of_exponent_le hx
    linarith
  unfold uniformResidueBlockError finiteBandDecay mrPrimeWeylConstant
  change 2 * (9 * (X : ℝ) ^ (-1 / 64 : ℝ) +
      ∑ r ∈ Finset.Icc 2 R, realStartBandConstant r *
        (X : ℝ) ^ (-savingExponent r)) * X + rOneLagBudget X + 1 ≤
    (21 + 2 * ∑ r ∈ Finset.Icc 2 R, realStartBandConstant r) * V
  nlinarith

theorem mrFirstResidueAtOrAbove_mod_one (A : ℕ) :
    firstResidueAtOrAbove A (0 : ZMod 1) = A := by
  apply le_antisymm
  · have hh := firstResidueIndex_min (A := A) (0 : ZMod 1)
      (k := A) (by simp)
    simpa [firstResidueAtOrAbove] using hh
  · exact le_firstResidueAtOrAbove _

theorem mrPrimeMellinMonomial_zero_eq_natLogTwist (n : ℕ) (t : ℝ) :
    mrPrimeMellinMonomial 0 t n = natLogTwist n (-t) := by
  unfold mrPrimeMellinMonomial mrPrimeMellinCoefficient natLogTwist logPhase
  congr 1
  push_cast
  ring

/-- Above the linear height threshold, the actual positive complex-power
sum has a fixed power saving on every dyadic prefix. -/
theorem mrExists_primeMellin_dyadic_power_bound (R : ℕ) (hR : 2 ≤ R) :
    ∃ A₀ : ℕ, 1 ≤ A₀ ∧ ∀ {A M : ℕ}, A₀ ≤ A → M ≤ 2 * A →
      ∀ {t : ℝ}, (A : ℝ) ≤ positiveLogCoefficient t →
        positiveLogCoefficient t < (A : ℝ) ^ (R + 1) →
        ‖∑ n ∈ Finset.Icc A M, mrPrimeMellinMonomial 0 t n‖ ≤
          mrPrimeWeylConstant R * (A : ℝ) ^ (1 - savingExponent R) := by
  obtain ⟨A₀, hA₀⟩ := exists_uniformResidueBlock_threshold R hR
  refine ⟨max 1 A₀, Nat.le_max_left _ _, ?_⟩
  intro A M hA hM t hl hu
  have hAone : 1 ≤ A := (Nat.le_max_left 1 A₀).trans hA
  have hAlarge : A₀ ≤ A := (Nat.le_max_right 1 A₀).trans hA
  have hneg : positiveLogCoefficient (-t) = positiveLogCoefficient t := by
    simp [positiveLogCoefficient]
  have hb := hA₀ (q := 1) (A := A) (M := M) (0 : ZMod 1) (t := -t)
    (by omega) hM
    (by simpa only [mrFirstResidueAtOrAbove_mod_one, Nat.div_one] using hAlarge)
    (by simpa only [mrFirstResidueAtOrAbove_mod_one, Nat.cast_one, div_one, hneg] using hl)
    (by simpa only [mrFirstResidueAtOrAbove_mod_one, Nat.div_one, hneg] using hu)
  simp only [mrFirstResidueAtOrAbove_mod_one, Nat.div_one,
    residueClassSum, Subsingleton.elim (_ : ZMod 1) 0, Finset.filter_true] at hb
  simp_rw [mrPrimeMellinMonomial_zero_eq_natLogTwist]
  exact hb.trans (mrUniformResidueBlockError_le_power hR hAone)

end

end Erdos67b
