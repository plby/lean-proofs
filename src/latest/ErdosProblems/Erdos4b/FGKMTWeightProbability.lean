/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceWeightEstimates
import ErdosProblems.Erdos4b.FGKMTProbabilityNormalizationAlgebra

/-! # The literal sieve weights as finite integer probability masses -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def commonPrimeSieveProbability (k W M R : ℕ) (y : ℝ) (h : Fin k → ℕ)
    (p : ℕ) (n : ℤ) : ℝ :=
  commonPrimeSieveWeight k W M R y h p n / commonPrimeSieveTotalMass k W M R y h p

theorem commonPrimeSieveProbability_nonneg (k W M R : ℕ) (y : ℝ)
    (h : Fin k → ℕ) (p : ℕ) (n : ℤ) :
    0 ≤ commonPrimeSieveProbability k W M R y h p n := by
  apply div_nonneg (commonPrimeSieveWeight_nonneg _ _ _ _ _ _ _ _)
  exact Finset.sum_nonneg fun a _ha => commonPrimeSieveWeight_nonneg _ _ _ _ _ _ _ _

theorem commonPrimeSieveProbability_zero_of_outside (k W M R : ℕ) (y : ℝ)
    (h : Fin k → ℕ) (p : ℕ) (n : ℤ) (hn : y < |(n : ℝ)|) :
    commonPrimeSieveProbability k W M R y h p n = 0 := by
  rw [commonPrimeSieveProbability, commonPrimeSieveWeight_zero_of_outside _ _ _ _ _ _ _ _ hn,
    zero_div]

theorem sum_commonPrimeSieveProbability_eq_one {k W M R : ℕ} {y : ℝ}
    {h : Fin k → ℕ} {p : ℕ} (hpos : 0 < commonPrimeSieveTotalMass k W M R y h p) :
    (∑ n ∈ integerWeightWindow y, commonPrimeSieveProbability k W M R y h p n) = 1 := by
  simp only [commonPrimeSieveProbability, ← Finset.sum_div]
  exact div_self hpos.ne'

theorem tsum_commonPrimeSieveProbability_eq_one {k W M R : ℕ} {y : ℝ}
    {h : Fin k → ℕ} {p : ℕ} (hpos : 0 < commonPrimeSieveTotalMass k W M R y h p) :
    (∑' n : ℤ, commonPrimeSieveProbability k W M R y h p n) = 1 := by
  simp only [commonPrimeSieveProbability, tsum_div_const, commonPrimeSieveWeight_tsum_eq_totalMass]
  exact div_self hpos.ne'

theorem commonPrimeSieveProbability_eq_finite_normalization (k W M R : ℕ) (y : ℝ)
    (h : Fin k → ℕ) (p : ℕ) (n : integerWeightWindow y) :
    commonPrimeSieveProbability k W M R y h p n =
      normalizeFiniteWeight (fun a : integerWeightWindow y =>
        commonPrimeSieveWeight k W M R y h p a) n := by
  simp only [commonPrimeSieveProbability, normalizeFiniteWeight, commonPrimeSieveTotalMass,
    Finset.sum_coe_sort]

theorem CommonWeightEstimates.totalMass_pos {x m B : ℕ} {y e : ℝ}
    {h : Fin (m + 1) → ℕ} (H : CommonWeightEstimates x m B y h e)
    (hy : 0 < y) (hL : 0 < Real.log (x : ℝ))
    (herror : 1 / Real.log (Real.log (x : ℝ)) ^ 10 ≤ (1 / 2 : ℝ))
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x) :
    0 < commonPrimeSieveTotalMass (m + 1) (dimensionPreSieveModulus (m + 1) B)
      (B * dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) y h p := by
  obtain ⟨htau, _hu, _htlow, _hulow, _huup, _hnonneg, _hsupp, _hpoint, htotal, _hpin⟩ := H
  have hT : 0 < commonWeightTau (m + 1) (dimensionPreSieveModulus (m + 1) B)
      (B * dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) x h * y /
        Real.log (x : ℝ) ^ (m + 1) := by positivity
  have ht := (div_le_iff₀ hT).mp (htotal p hp)
  rw [commonPrimeSieveWeight_tsum_eq_totalMass] at ht
  exact (mass_pos_of_relative_error hT herror ht).2

theorem CommonWeightEstimates.totalMass_ge_massScale {x m B : ℕ} {y e : ℝ}
    {h : Fin (m + 1) → ℕ} (H : CommonWeightEstimates x m B y h e)
    (hy : 0 < y) (hL : 0 < Real.log (x : ℝ))
    (herror : 1 / Real.log (Real.log (x : ℝ)) ^ 10 ≤ (1 / 2 : ℝ))
    {p : ℕ} (hp : p ∈ commonPinnedPrimeSet (x / 2) x) :
    y * commonWeightMassScale (m + 1) (dimensionPreSieveModulus (m + 1) B)
        (B * dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) h ≤
      commonPrimeSieveTotalMass (m + 1) (dimensionPreSieveModulus (m + 1) B)
        (B * dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) y h p := by
  obtain ⟨htau, _hu, _htlow, _hulow, _huup, _hnonneg, _hsupp, _hpoint, htotal, _hpin⟩ := H
  have hT : 0 < commonWeightTau (m + 1) (dimensionPreSieveModulus (m + 1) B)
      (B * dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) x h * y /
        Real.log (x : ℝ) ^ (m + 1) := by positivity
  have ht := (div_le_iff₀ hT).mp (htotal p hp)
  rw [commonPrimeSieveWeight_tsum_eq_totalMass] at ht
  have hlo := (mass_pos_of_relative_error hT herror ht).1
  rw [commonWeightTau_total_identity hL.ne' h y] at hlo
  linarith

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPrimeSieveProbability_eq_finite_normalization
#print axioms Erdos4b.FGKMT.CommonWeightEstimates.totalMass_pos
#print axioms Erdos4b.FGKMT.CommonWeightEstimates.totalMass_ge_massScale
