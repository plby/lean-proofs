import ErdosProblems.Erdos67b.MRCofactorMaskedEuler
import ErdosProblems.Erdos67b.MRPrimeMaskInclusion

/-!
# The actual typical cofactor on the convergent Euler line

Finite inclusion-exclusion and the summed masked Euler estimate apply to
the typical coefficient without asserting that it is multiplicative.
-/

open scoped BigOperators Classical
open Finset

namespace Erdos67b

open MRHalaszBands MRHalaszEuler EulerResidue EulerQuantitative

noncomputable section

theorem mrIndexedTypicalCoefficient_div {ι : Type*}
    (J : Finset ι) (B : ι → Finset ℕ) (f D : ℕ → ℂ) :
    mrIndexedTypicalCoefficient J B (fun n ↦ f n / D n) =
      fun n ↦ mrIndexedTypicalCoefficient J B f n / D n := by
  funext n
  unfold mrIndexedTypicalCoefficient
  split_ifs <;> simp

theorem mrPrimeBandCoefficient_div (f D : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P] :
    primeBandCoefficient (fun n ↦ f n / D n) P =
      fun n ↦ primeBandCoefficient f P n / D n := by
  funext n
  unfold primeBandCoefficient
  split_ifs <;> simp

theorem mrCommonCofactorCoefficient_norm_le_one (A : Finset ℕ)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {n : ℕ} (hn : 0 < n) :
    ‖f n / (mrCommonDenominator A n : ℂ)‖ ≤ 1 := by
  have hd : (1 : ℝ) ≤ mrCommonDenominator A n := by
    unfold mrCommonDenominator
    push_cast
    linarith [show (0 : ℝ) ≤ primeDivisorCount A n by positivity]
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < mrCommonDenominator A n)).mpr
  simpa only [one_mul] using (hbound n hn).trans hd

theorem mrNorm_typical_cofactor_LSeries_le_mask_sum {ι : Type*} [DecidableEq ι]
    (A : Finset ℕ) (J : Finset ι) (B : ι → Finset ℕ)
    (hB : ∀ j ∈ J, ∀ p ∈ B j, p.Prime)
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    ‖mrCofactorLSeries A (mrIndexedTypicalCoefficient J B f) s‖ ≤
      ∑ S ∈ J.powerset, ‖mrCofactorLSeries A
        (primeBandCoefficient f (fun p ↦ p ∉ S.biUnion B)) s‖ := by
  have hh := mrNorm_LSeries_indexedTypical_le_mask_norm_sum J B hB
    (fun n hn ↦ mrCommonCofactorCoefficient_norm_le_one A hbound hn) hs
  rw [mrIndexedTypicalCoefficient_div] at hh
  simp only [mrPrimeBandCoefficient_div] at hh
  exact hh

theorem mrNorm_typical_cofactor_LSeries_le
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (J : Finset ℕ) (B : ℕ → Finset ℕ) {X : ℕ} (hX : 1 < X)
    (hJ : ∀ j ∈ J, 1 ≤ j) (hB : ∀ j ∈ J, B j ⊆ primesUpTo X)
    (hdisj : Set.PairwiseDisjoint (↑J : Set ℕ) B)
    (hsmall : ∀ j ∈ J, ∀ p ∈ B j, Real.log (p : ℝ) ≤ Real.log (X : ℝ) / 16)
    (hmass : ∀ j ∈ J, 2 * Real.log (j : ℝ) ≤ ∑ p ∈ B j, 1 / (p : ℝ))
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (t : ℝ) :
    ‖mrCofactorLSeries A (mrIndexedTypicalCoefficient J B f) (halaszPoint X t)‖ ≤
      Real.exp (Real.log (riemannZeta (taoExponent X : ℂ)).re +
        3 * primeQuadraticConstant + mrMaskProductSeries -
        Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X +
        Real.exp (-1) / 16 * mrSelectedPrimeReciprocalMass A X) := by
  apply (mrNorm_typical_cofactor_LSeries_le_mask_sum A J B
    (fun j hj p hp ↦ (mem_primesUpTo.mp (hB j hj hp)).1) hbound
    (by rw [halaszPoint_re]; exact one_lt_taoExponent hX)).trans
  exact mrSum_norm_masked_cofactor_LSeries_le A hA J B hX hJ hB hdisj hsmall hmass hmul hbound t

theorem mrIndexedTypicalCoefficient_schedule_eq (p₁ q₁ : ℝ) (J : ℕ) (f : ℕ → ℂ) :
    mrIndexedTypicalCoefficient (Finset.Icc 1 J)
      (fun j ↦ primesInBlock (mrScheduledPrimeInterval p₁ q₁ j)) f =
      fun n ↦ if HasTypicalFactorization (mrScheduledBlocks p₁ q₁ J) n then f n else 0 := by
  funext n
  unfold mrIndexedTypicalCoefficient HasTypicalFactorization mrScheduledBlocks
  simp only [Finset.forall_mem_image, HasPrimeFactorInBlock, mrPrimeBlockHit]
  exact (ite_eq_ite _ _ _).mpr trivial

theorem mrScheduled_norm_typical_cofactor_LSeries_le
    (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    {eta p₁ q₁ : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : 2 * p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁)
    (hmertens : Real.log 2 + 2 * PrimeEstimates.mertensBound ≤ Real.log q₁ - Real.log p₁)
    {X J : ℕ} (hX : 1 < X) (hlogX : 256 ≤ Real.log (X : ℝ))
    (hJX : mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)))
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) (t : ℝ) :
    ‖mrCofactorLSeries A
      (fun n ↦ if HasTypicalFactorization (mrScheduledBlocks p₁ q₁ J) n then f n else 0)
      (halaszPoint X t)‖ ≤
      Real.exp (Real.log (riemannZeta (taoExponent X : ℂ)).re +
        3 * primeQuadraticConstant + mrMaskProductSeries -
        Real.exp (-1) / 16 * pretentiousDistSq f (archimedeanTwist t) X +
        Real.exp (-1) / 16 * mrSelectedPrimeReciprocalMass A X) := by
  have hpq' : p₁ ≤ q₁ := by linarith
  rw [← mrIndexedTypicalCoefficient_schedule_eq]
  apply mrNorm_typical_cofactor_LSeries_le A hA (Finset.Icc 1 J) _ hX
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
