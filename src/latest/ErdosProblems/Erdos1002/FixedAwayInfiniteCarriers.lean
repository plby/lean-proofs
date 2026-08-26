import ErdosProblems.Erdos1002.FixedAwayL2Realization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Infinite Bernoulli-carrier aggregation for fixed-away blocks

The finite-cutoff carrier estimates are not the end of the argument: the
Bernoulli mark has infinitely many Fourier modes.  This file performs the
limit in the actual circle `L²` space.  Absolute summability of the carrier
majorant and a common one-carrier square-energy bound imply norm summability
of the vector series.  Fourier coefficients may then be taken through the
sum by continuity.
-/

open Filter MeasureTheory Set AddCircle
open scoped BigOperators ComplexConjugate Real Topology

namespace Erdos1002

noncomputable section

/-- The `ell`-th weighted `L²` carrier associated with a square-summable
coefficient sequence. -/
def fixedAwayCarrierL2Term
    (c : NonzeroFourierIndex → ℤ → ℂ)
    (hc : ∀ ell, Summable fun n : ℤ ↦ ‖c ell n‖ ^ 2)
    (ell : NonzeroFourierIndex) : UnitCircleL2 :=
  bernoulliMarkFourierCoefficient (ell : ℤ) •
    fixedAwayCoefficientL2 (c ell) (hc ell)

/-- A common coefficient-energy bound makes the complete nonzero carrier
series norm summable.  In particular, passage from symmetric finite carrier
cutoffs to all carriers loses no cardinality factor. -/
theorem summable_fixedAwayCarrierL2Term
    (c : NonzeroFourierIndex → ℤ → ℂ)
    (hc : ∀ ell, Summable fun n : ℤ ↦ ‖c ell n‖ ^ 2)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ell, (∑' n : ℤ, ‖c ell n‖ ^ 2) ≤ C) :
    Summable (fixedAwayCarrierL2Term c hc) := by
  have hmajorAll : Summable fun ell : ℤ ↦
      bernoulliCarrierMajorant ell * Real.sqrt C :=
    summable_bernoulliCarrierMajorant.mul_right (Real.sqrt C)
  have hmajor : Summable fun ell : NonzeroFourierIndex ↦
      bernoulliCarrierMajorant (ell : ℤ) * Real.sqrt C :=
    hmajorAll.subtype {ell : ℤ | ell ≠ 0}
  apply hmajor.of_norm_bounded
  intro ell
  have hnormSq :
      ‖fixedAwayCoefficientL2 (c ell) (hc ell)‖ ^ 2 ≤ C := by
    rw [norm_fixedAwayCoefficientL2_sq]
    exact hbound ell
  have hnorm :
      ‖fixedAwayCoefficientL2 (c ell) (hc ell)‖ ≤ Real.sqrt C := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).mp
    rw [Real.sq_sqrt hC]
    exact hnormSq
  unfold fixedAwayCarrierL2Term
  rw [norm_smul]
  calc
    ‖bernoulliMarkFourierCoefficient (ell : ℤ)‖ *
        ‖fixedAwayCoefficientL2 (c ell) (hc ell)‖ ≤
      ‖bernoulliMarkFourierCoefficient (ell : ℤ)‖ *
        Real.sqrt C :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ ≤ bernoulliCarrierMajorant (ell : ℤ) * Real.sqrt C :=
      mul_le_mul_of_nonneg_right
        (norm_bernoulliMarkFourierCoefficient_le_majorant (ell : ℤ))
        (Real.sqrt_nonneg C)

/-- The actual `L²` sum of all nonzero Bernoulli carriers. -/
def fixedAwayInfiniteCarrierL2
    (c : NonzeroFourierIndex → ℤ → ℂ)
    (hc : ∀ ell, Summable fun n : ℤ ↦ ‖c ell n‖ ^ 2) :
    UnitCircleL2 :=
  ∑' ell : NonzeroFourierIndex, fixedAwayCarrierL2Term c hc ell

/-- Fourier coefficients of the complete carrier sum are the absolutely
convergent scalar carrier sums. -/
theorem fourierCoeff_fixedAwayInfiniteCarrierL2
    (c : NonzeroFourierIndex → ℤ → ℂ)
    (hc : ∀ ell, Summable fun n : ℤ ↦ ‖c ell n‖ ^ 2)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ell, (∑' n : ℤ, ‖c ell n‖ ^ 2) ≤ C)
    (n : ℤ) :
    fourierCoeff
        (fixedAwayInfiniteCarrierL2 c hc : AddCircle (1 : ℝ) → ℂ) n =
      ∑' ell : NonzeroFourierIndex,
        bernoulliMarkFourierCoefficient (ell : ℤ) * c ell n := by
  have hs := summable_fixedAwayCarrierL2Term c hc hC hbound
  rw [← fourierCoefficientCLM_apply]
  unfold fixedAwayInfiniteCarrierL2
  rw [(fourierCoefficientCLM n).map_tsum hs]
  apply tsum_congr
  intro ell
  simp only [fixedAwayCarrierL2Term, map_smul,
    fourierCoefficientCLM_apply, fourierCoeff_fixedAwayCoefficientL2,
    smul_eq_mul]

/-- The norm of the complete carrier sum is bounded by total carrier mass
times the common one-carrier norm. -/
theorem norm_fixedAwayInfiniteCarrierL2_le
    (c : NonzeroFourierIndex → ℤ → ℂ)
    (hc : ∀ ell, Summable fun n : ℤ ↦ ‖c ell n‖ ^ 2)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ell, (∑' n : ℤ, ‖c ell n‖ ^ 2) ≤ C) :
    ‖fixedAwayInfiniteCarrierL2 c hc‖ ≤
      windowCarrierMassConstant * Real.sqrt C := by
  have hs := summable_fixedAwayCarrierL2Term c hc hC hbound
  have hnorms : Summable fun ell : NonzeroFourierIndex ↦
      ‖fixedAwayCarrierL2Term c hc ell‖ := by
    have hmajorAll : Summable fun ell : ℤ ↦
        bernoulliCarrierMajorant ell * Real.sqrt C :=
      summable_bernoulliCarrierMajorant.mul_right (Real.sqrt C)
    have hmajor : Summable fun ell : NonzeroFourierIndex ↦
        bernoulliCarrierMajorant (ell : ℤ) * Real.sqrt C :=
      hmajorAll.subtype {ell : ℤ | ell ≠ 0}
    apply hmajor.of_nonneg_of_le
    · intro ell
      exact norm_nonneg _
    · intro ell
      have hnormSq :
          ‖fixedAwayCoefficientL2 (c ell) (hc ell)‖ ^ 2 ≤ C := by
        rw [norm_fixedAwayCoefficientL2_sq]
        exact hbound ell
      have hnorm :
          ‖fixedAwayCoefficientL2 (c ell) (hc ell)‖ ≤ Real.sqrt C := by
        apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).mp
        rw [Real.sq_sqrt hC]
        exact hnormSq
      unfold fixedAwayCarrierL2Term
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right
          (norm_bernoulliMarkFourierCoefficient_le_majorant (ell : ℤ))
          (Real.sqrt_nonneg C))
  calc
    ‖fixedAwayInfiniteCarrierL2 c hc‖ ≤
        ∑' ell : NonzeroFourierIndex,
          ‖fixedAwayCarrierL2Term c hc ell‖ :=
      norm_tsum_le_tsum_norm hnorms
    _ ≤ ∑' ell : NonzeroFourierIndex,
        bernoulliCarrierMajorant (ell : ℤ) * Real.sqrt C := by
      apply hnorms.tsum_le_tsum
      · intro ell
        have hnormSq :
            ‖fixedAwayCoefficientL2 (c ell) (hc ell)‖ ^ 2 ≤ C := by
          rw [norm_fixedAwayCoefficientL2_sq]
          exact hbound ell
        have hnorm :
            ‖fixedAwayCoefficientL2 (c ell) (hc ell)‖ ≤ Real.sqrt C := by
          apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg C)).mp
          rw [Real.sq_sqrt hC]
          exact hnormSq
        unfold fixedAwayCarrierL2Term
        rw [norm_smul]
        exact (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_right
            (norm_bernoulliMarkFourierCoefficient_le_majorant (ell : ℤ))
            (Real.sqrt_nonneg C))
      · exact
          (summable_bernoulliCarrierMajorant.mul_right (Real.sqrt C)).subtype
            {ell : ℤ | ell ≠ 0}
    _ ≤ ∑' ell : ℤ,
        bernoulliCarrierMajorant ell * Real.sqrt C := by
      exact Summable.tsum_subtype_le
        (fun ell : ℤ ↦ bernoulliCarrierMajorant ell * Real.sqrt C)
        {ell : ℤ | ell ≠ 0}
        (fun ell ↦ mul_nonneg (bernoulliCarrierMajorant_nonneg ell)
          (Real.sqrt_nonneg C))
        (summable_bernoulliCarrierMajorant.mul_right (Real.sqrt C))
    _ = windowCarrierMassConstant * Real.sqrt C := by
      rw [tsum_mul_right]
      rfl

end

end Erdos1002
