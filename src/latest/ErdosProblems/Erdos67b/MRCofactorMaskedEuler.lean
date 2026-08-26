import ErdosProblems.Erdos67b.MRMaskedEulerSum
import ErdosProblems.Erdos67b.MRCofactorPerron

/-!
# Euler bounds for denominator-weighted prime masks

The beta integral for the Ramaré denominator preserves the refined
deleted-prime cost. This concerns the complete convergent L-series;
finite cofactor polynomial estimates remain a further analytic step.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

open MRHalaszBands MRHalaszEuler EulerResidue EulerQuantitative

noncomputable section

theorem mrPrimeScaled_primeBandCoefficient
    (A : Finset ℕ) (f : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P] (u : ℝ) :
    mrPrimeScaledCoefficient A (primeBandCoefficient f P) u =
      primeBandCoefficient (mrPrimeScaledCoefficient A f u) P := by
  funext n
  unfold mrPrimeScaledCoefficient primeBandCoefficient
  split_ifs <;> simp

theorem mrNorm_masked_cofactor_LSeries_le_distance_add_mass
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P] {X : ℕ} (hX : 1 < X)
    (hsmall : ∀ p ∈ primesUpTo X, ¬ P p → Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
    (t : ℝ) :
    ‖mrCofactorLSeries A (primeBandCoefficient f P) (halaszPoint X t)‖ ≤
      Real.exp (Real.log (riemannZeta (taoExponent X : ℂ)).re + 3 * primeQuadraticConstant -
        Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X +
        Real.exp (-1) / 16 * mrSelectedPrimeReciprocalMass A X -
        (3 / 4 : ℝ) * mrRemovedPrimeMass P X) := by
  let E := Real.exp (Real.log (riemannZeta (taoExponent X : ℂ)).re + 3 * primeQuadraticConstant -
    Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X +
    Real.exp (-1) / 16 * mrSelectedPrimeReciprocalMass A X -
    (3 / 4 : ℝ) * mrRemovedPrimeMass P X)
  have hmaskBound : ∀ n, 0 < n → ‖primeBandCoefficient f P n‖ ≤ 1 :=
    fun n hn ↦ norm_primeBandCoefficient_le_one hbound P hn
  rw [mrCofactorLSeries_eq_intervalIntegral A hmaskBound
    (by rw [halaszPoint_re]; exact one_lt_taoExponent hX)]
  have hpoint : ∀ u ∈ Ι (0 : ℝ) 1,
      ‖LSeries (mrPrimeScaledCoefficient A (primeBandCoefficient f P) u) (halaszPoint X t)‖ ≤ E := by
    intro u hu
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    have hscaledBound : ∀ n, 0 < n → ‖mrPrimeScaledCoefficient A f u n‖ ≤ 1 :=
      fun n hn ↦ norm_mrPrimeScaledCoefficient_le_one hbound hu.1.le hu.2 hn
    have hbase := mrNorm_masked_LSeries_le_distance_add_mass
      (mrPrimeScaledCoefficient_isMultiplicative hA hmul u) hscaledBound P hX hsmall t
    have hdist := pretentiousDistSq_le_scaled_add_mass (X := X) hA hu.1.le hu.2
      (fun p hp ↦ hbound p hp.pos) (fun p hp ↦ (norm_archimedeanTwist hp.pos t).le)
    rw [mrPrimeScaled_primeBandCoefficient]
    apply hbase.trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hdist (show 0 ≤ Real.exp (-1) / 16 by positivity)
    linarith
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  simpa only [sub_zero, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1), mul_one] using hh

theorem mrSum_norm_masked_cofactor_LSeries_le
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ℕ) (B : ℕ → Finset ℕ) {X : ℕ} (hX : 1 < X)
    (hJ : ∀ j ∈ J, 1 ≤ j) (hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
    (hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
    (hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
    (hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (t : ℝ) :
    (∑ S ∈ J.powerset,
      ‖mrCofactorLSeries A (primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B)) (halaszPoint X t)‖) ≤
      Real.exp (Real.log (riemannZeta (taoExponent X : ℂ)).re +
        3 * primeQuadraticConstant + mrMaskProductSeries -
        Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X +
        Real.exp (-1) / 16 * mrSelectedPrimeReciprocalMass A X) := by
  let E := Real.log (riemannZeta (taoExponent X : ℂ)).re + 3 * primeQuadraticConstant -
    Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X +
    Real.exp (-1) / 16 * mrSelectedPrimeReciprocalMass A X
  let m := fun j ↦ ∑ p ∈ B j, 1 / (p : ℝ)
  have hpoint (S : Finset ℕ) (hS : S ⊆ J) :
      ‖mrCofactorLSeries A (primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B)) (halaszPoint X t)‖ ≤
        Real.exp E * ∏ j ∈ S, Real.exp (-(3 / 4 : ℝ) * m j) := by
    have hdeleted : ∀ p ∈ primesUpTo X, ¬(p ∉ S.biUnion B) →
        Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16 := by
      intro p hp hnot
      have hmem : p ∈ S.biUnion B := by simpa only [not_not] using hnot
      obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hmem
      exact hsmall j (hS hj) p hpj
    have hbase := mrNorm_masked_cofactor_LSeries_le_distance_add_mass A hA hmul hbound
      (fun p ↦ p ∉ S.biUnion B) hX hdeleted t
    have hdisjS : Set.PairwiseDisjoint (↑S : Set ℕ) B := by
      intro i hi j hj hij
      exact hdisj (hS hi) (hS hj) hij
    rw [mrRemovedPrimeMass_outside_biUnion S B (fun j hj ↦ hB j (hS hj)) hdisjS] at hbase
    rw [← Real.exp_sum, ← Finset.mul_sum, ← Real.exp_add]
    convert hbase using 1
    dsimp only [E, m]
    congr 1
    ring
  have hprod := mrMaskProduct_le_series J (fun j ↦ (3 / 4 : ℝ) * m j) hJ (by
    intro j hj
    have hh := hmass j hj
    change 2 * Real.log (j : ℝ) ≤ m j at hh
    nlinarith)
  calc
    _ ≤ ∑ S ∈ J.powerset, Real.exp E * ∏ j ∈ S, Real.exp (-(3 / 4 : ℝ) * m j) :=
      Finset.sum_le_sum (fun S hS ↦ hpoint S (Finset.mem_powerset.mp hS))
    _ = Real.exp E * ∏ j ∈ J, (1 + Real.exp (-(3 / 4 : ℝ) * m j)) := by
      rw [← Finset.mul_sum, Finset.prod_one_add]
    _ ≤ Real.exp E * Real.exp mrMaskProductSeries := by
      apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      simpa only [neg_mul] using hprod
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp only [E]; ring

end

end Erdos67b
