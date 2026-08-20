/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos407.AuxiliaryHeightEstimates
import ErdosProblems.Erdos407.RankDrop

/-!
# Projective-height bridge for the GLR auxiliary polynomial

This acyclic adapter combines the integral coefficient-vector estimate from
`RankDrop` with the uniform rounded logarithmic bound from
`AuxiliaryHeightEstimates`.
-/

namespace Erdos407.RankDrop

open scoped BigOperators

/-- An auxiliary coefficient vector satisfying the Bombieri--Vaaler norm
bound gives a projective coefficient height which is linear in the total
multidegree, with a constant depending only on the fixed coordinate change. -/
theorem projectiveCoeffHeight_rationalAuxiliaryPolynomial_le_sum_degree
    {blocks n : ℕ} {degree : Fin blocks → ℕ} (eta : ℚ)
    (T : GLRAuxiliary.Place23 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (hblocks : 0 < blocks) (hdegree : ∀ h, 0 < degree h)
    (heta : 0 < eta)
    (hmany : (6 : ℚ) * ((n + 1 : ℕ) : ℚ) < blocks * eta ^ 2)
    (coeff : AuxiliaryPolynomial.MonomialIndex blocks (n + 1) degree → ℤ)
    (hcoeff : ‖coeff‖ ≤
      GLRAuxiliary.coefficientHeightBound (degree := degree) eta T) :
    PolynomialHeights.projectiveCoeffHeight
        (rationalAuxiliaryPolynomial coeff) ≤
      Real.log (2 * AuxiliaryHeightEstimates.coefficientHeightBase T) *
        ∑ h, (degree h : ℝ) := by
  calc
    PolynomialHeights.projectiveCoeffHeight
        (rationalAuxiliaryPolynomial coeff) ≤
        Real.log (max 1
          ⌈GLRAuxiliary.coefficientHeightBound
            (degree := degree) eta T⌉₊) :=
      projectiveCoeffHeight_rationalAuxiliaryPolynomial_le_of_norm_le
        coeff hcoeff
    _ ≤ Real.log (2 * AuxiliaryHeightEstimates.coefficientHeightBase T) *
        ∑ h, (degree h : ℝ) :=
      AuxiliaryHeightEstimates.log_max_ceil_coefficientHeightBound_le
        eta T hblocks (by omega) hdegree heta hmany

/-- Existential-slope packaging of the preceding projective-height bound. -/
theorem exists_projectiveCoeffHeightSlope {blocks n : ℕ} (eta : ℚ)
    (T : GLRAuxiliary.Place23 → Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (hblocks : 0 < blocks) (heta : 0 < eta)
    (hmany : (6 : ℚ) * ((n + 1 : ℕ) : ℚ) < blocks * eta ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (degree : Fin blocks → ℕ)
        (coeff : AuxiliaryPolynomial.MonomialIndex blocks (n + 1) degree → ℤ),
      (∀ h, 0 < degree h) →
      ‖coeff‖ ≤ GLRAuxiliary.coefficientHeightBound
        (degree := degree) eta T →
      PolynomialHeights.projectiveCoeffHeight
          (rationalAuxiliaryPolynomial coeff) ≤
        C * ∑ h, (degree h : ℝ) := by
  refine ⟨Real.log (2 * AuxiliaryHeightEstimates.coefficientHeightBase T),
    Real.log_nonneg (by
      nlinarith [AuxiliaryHeightEstimates.one_le_coefficientHeightBase T]), ?_⟩
  intro degree coeff hdegree hcoeff
  exact projectiveCoeffHeight_rationalAuxiliaryPolynomial_le_sum_degree
    eta T hblocks hdegree heta hmany coeff hcoeff

end Erdos407.RankDrop
