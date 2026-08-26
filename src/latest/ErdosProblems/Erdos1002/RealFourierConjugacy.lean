import ErdosProblems.Erdos1002.NaturalCutoffShotCoefficientBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Conjugacy of Fourier coefficients for real-valued circle representatives

This records the negative-frequency symmetry needed for the literal
primitive shot.  The proof is at the Bochner-integral level and uses an
explicit almost-everywhere reality hypothesis.
-/

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Erdos1002

noncomputable section

/-- A complex circle function which is real almost everywhere has conjugate
Fourier coefficients at opposite frequencies. -/
theorem fourierCoeff_neg_eq_conj_of_ae_real
    (f : AddCircle (1 : ℝ) → ℂ)
    (hf : ∀ᵐ x ∂AddCircle.haarAddCircle, starRingEnd ℂ (f x) = f x)
    (n : ℤ) :
    fourierCoeff f (-n) = starRingEnd ℂ (fourierCoeff f n) := by
  unfold fourierCoeff
  rw [neg_neg, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  change (fourier n x : ℂ) * f x =
    starRingEnd ℂ ((fourier (-n) x : ℂ) * f x)
  rw [map_mul, hx]
  rw [← fourier_neg]
  simp

/-- The chosen circle representative of the finite primitive shot sum is
pointwise fixed by complex conjugation. -/
theorem primitiveShotSumCircle_star
    (N P : ℕ) (x : AddCircle (1 : ℝ)) :
    starRingEnd ℂ (primitiveShotSumCircle N P x) =
      primitiveShotSumCircle N P x := by
  unfold primitiveShotSumCircle
  have hcomp :
      AddCircle.liftIoc (1 : ℝ) 0
          ((starRingEnd ℂ) ∘
            (fun alpha : ℝ ↦ (primitiveShotSum N P alpha : ℂ))) x =
        starRingEnd ℂ
          (AddCircle.liftIoc (1 : ℝ) 0
            (fun alpha : ℝ ↦ (primitiveShotSum N P alpha : ℂ)) x) :=
    AddCircle.liftIoc_comp_apply
  rw [← hcomp]
  congr 1
  funext alpha
  simp

/-- Negative coefficients of the literal finite primitive-shot `L²` class
are the conjugates of its positive coefficients. -/
theorem fourierCoeff_primitiveShotSumL2_neg
    (N P : ℕ) (n : ℤ) :
    fourierCoeff
        (primitiveShotSumL2 N P : AddCircle (1 : ℝ) → ℂ) (-n) =
      starRingEnd ℂ
        (fourierCoeff
          (primitiveShotSumL2 N P : AddCircle (1 : ℝ) → ℂ) n) := by
  apply fourierCoeff_neg_eq_conj_of_ae_real
  filter_upwards [primitiveShotSumL2_coe_ae N P] with x hx
  rw [hx]
  exact primitiveShotSumCircle_star N P x

/-- Negative coefficients of the central shot `Y_N` obey the same exact
conjugacy. -/
theorem fourierCoeff_reconstructedShotL2_neg (N : ℕ) (n : ℤ) :
    fourierCoeff
        (reconstructedShotL2 N : AddCircle (1 : ℝ) → ℂ) (-n) =
      starRingEnd ℂ
        (fourierCoeff
          (reconstructedShotL2 N : AddCircle (1 : ℝ) → ℂ) n) := by
  exact fourierCoeff_primitiveShotSumL2_neg N N n

/-- The canonical circle representative of the sawtooth is pointwise real. -/
theorem sawtoothCircle_star (x : AddCircle (1 : ℝ)) :
    starRingEnd ℂ (sawtoothCircle x) = sawtoothCircle x := by
  unfold sawtoothCircle
  have hcomp :
      AddCircle.liftIoc (1 : ℝ) 0
          ((starRingEnd ℂ) ∘ (fun alpha : ℝ ↦ (sawtooth alpha : ℂ))) x =
        starRingEnd ℂ
          (AddCircle.liftIoc (1 : ℝ) 0
            (fun alpha : ℝ ↦ (sawtooth alpha : ℂ)) x) :=
    AddCircle.liftIoc_comp_apply
  rw [← hcomp]
  congr 1
  funext alpha
  simp

/-- The exact all-denominator reconstruction is real almost everywhere,
so its negative Fourier coefficients are conjugate to the positive ones. -/
theorem fourierCoeff_allDenominatorReconstructionL2_neg
    (N : ℕ+) (n : ℤ) :
    fourierCoeff
        (allDenominatorReconstructionL2 N : AddCircle (1 : ℝ) → ℂ) (-n) =
      starRingEnd ℂ
        (fourierCoeff
          (allDenominatorReconstructionL2 N : AddCircle (1 : ℝ) → ℂ) n) := by
  apply fourierCoeff_neg_eq_conj_of_ae_real
  filter_upwards [allDenominatorReconstructionL2_coe_ae N] with x hx
  rw [hx]
  unfold allDenominatorReconstructionCircle rotationSumCircleFunction
  have htwo : starRingEnd ℂ (2 : ℂ) = 2 := by
    exact map_ofNat (starRingEnd ℂ) 2
  simp [sawtoothCircle_star, htwo]

end

end Erdos1002
