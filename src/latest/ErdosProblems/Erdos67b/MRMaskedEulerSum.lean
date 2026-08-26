import ErdosProblems.Erdos67b.MRMaskedEuler
import ErdosProblems.Erdos67b.MRScheduledMaskSum

/-!
# Uniform sum of actual masked L-series norms

The refined Euler deficit gives a summable deleted-block contribution.
All masks of the actual last-block schedule are included. This estimates
L-series on their convergent line, not finite cofactor polynomials.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

open MRHalaszBands MRHalaszEuler EulerResidue EulerQuantitative

noncomputable section

theorem mrSum_norm_masked_LSeries_le
    (J : Finset ℕ) (B : ℕ → Finset ℕ) {X : ℕ} (hX : 1 < X)
    (hJ : ∀ j ∈ J, 1 ≤ j) (hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
    (hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
    (hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
    (hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (t : ℝ) :
    (∑ S ∈ J.powerset,
      ‖LSeries (primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B)) (halaszPoint X t)‖) ≤
      Real.exp (Real.log (riemannZeta (taoExponent X : ℂ)).re +
        3 * primeQuadraticConstant + mrMaskProductSeries -
        Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X) := by
  let E := Real.log (riemannZeta (taoExponent X : ℂ)).re + 3 * primeQuadraticConstant -
    Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X
  let m := fun j ↦ ∑ p ∈ B j, 1 / (p : ℝ)
  have hpoint (S : Finset ℕ) (hS : S ⊆ J) :
      ‖LSeries (primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B)) (halaszPoint X t)‖ ≤
        Real.exp E * ∏ j ∈ S, Real.exp (-(3 / 4 : ℝ) * m j) := by
    have hdeleted : ∀ p ∈ primesUpTo X, ¬(p ∉ S.biUnion B) →
        Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16 := by
      intro p hp hnot
      have hmem : p ∈ S.biUnion B := by simpa only [not_not] using hnot
      obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hmem
      exact hsmall j (hS hj) p hpj
    have hbase := mrNorm_masked_LSeries_le_distance_add_mass hmul hbound
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

theorem mrScheduledPrimeBlocks_log_le_sixteenth
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    {X J : ℕ} (hlogX : 256 ≤ Real.log (X : ℝ))
    (hJX : mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)))
    {j : ℕ} (hj : j ∈ Finset.Icc 1 J) {p : ℕ}
    (hpB : p ∈ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) :
    Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16 := by
  have hqj := mrLogScheduleUpper_mono_positive heta hp hq hpq hlogq hbudget
    (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
  have hs : Real.sqrt (Real.log (X : ℝ)) ≤ Real.log (X : ℝ) / 16 := by
    have hsq := Real.sq_sqrt (show 0 ≤ Real.log (X : ℝ) by linarith)
    have hs0 := Real.sqrt_nonneg (Real.log (X : ℝ))
    have hs16 : 16 ≤ Real.sqrt (Real.log (X : ℝ)) := by nlinarith
    nlinarith
  exact (mem_primesInBlock_mrLogPrimeInterval_bounds hpB).2.trans
    (hqj.trans (hJX.trans hs))

theorem mrScheduled_sum_norm_masked_LSeries_le
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : 2 * p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    (hmertens : Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁)
    {X J : ℕ} (hX : 1 < X) (hlogX : 256 ≤ Real.log (X : ℝ))
    (hJX : mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)))
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (t : ℝ) :
    (∑ S ∈ (Finset.Icc 1 J).powerset,
      ‖LSeries (primeBandCoefficient f (fun p ↦ p ∉ S.biUnion
        (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)))) (halaszPoint X t)‖) ≤
      Real.exp (Real.log (riemannZeta (taoExponent X : ℂ)).re +
        3 * primeQuadraticConstant + mrMaskProductSeries -
        Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X) := by
  have hpq' : p₁ ≤ q₁ := by linarith
  apply mrSum_norm_masked_LSeries_le (Finset.Icc 1 J) _ hX
    (fun j hj ↦ (Finset.mem_Icc.mp hj).1)
  · intro j hj
    exact mrScheduledPrimeBlocks_subset_primesUpTo heta hp hq hpq' hlogq hbudget
      (by omega) (by linarith) hJX hj
  · intro i hi j hj hij
    exact mrScheduledPrimeInterval_disjoint heta hp hq hpq' hlogq hbudget
      (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1 hij
  · intro j hj p hpb
    exact mrScheduledPrimeBlocks_log_le_sixteenth heta hp hq hpq' hlogq hbudget hlogX hJX hj hpb
  · intro j hj
    exact mrScheduledPrimeInterval_reciprocalMass_ge_two_log hp hq hpq hmertens
      (Finset.mem_Icc.mp hj).1
  · exact hmul
  · exact hbound

end

end Erdos67b
