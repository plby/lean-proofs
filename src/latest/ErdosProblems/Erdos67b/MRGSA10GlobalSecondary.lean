import ErdosProblems.Erdos67b.MRGSA10FullIntegralIdentity
import ErdosProblems.Erdos67b.MRGSA10SpecializedPerron
import ErdosProblems.Erdos67b.MRGSA10ToA9Central

/-!
# The single global secondary error in the GS A.10 reconstruction

The finite identity in `MRGSA10FullIntegralIdentity` reconstructs the whole
low--high prefix from one rectangular average and two secondary sums.  The
source contour uses finite generalized-Mangoldt windows, so we also keep the
single rectangular full-to-windowed discrepancy.  This file packages all
three contributions into one explicit coefficient-side scalar.  No prefix
bound, L-series bound, or desired conclusion occurs among its hypotheses.
-/

open scoped BigOperators

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- The unwindowed rectangular prefix average in GS Lemma 2.2, after the
source change of variables `beta_source = 2 * beta`. -/
def gsA10FullIntegratedPrefix
    (low high lambda : ArithmeticFunction ℂ) (X : ℕ) (eta : ℝ) : ℂ :=
  2 * ∫ alpha in 0..eta, ∫ beta in 0..eta,
    positivePrefixSum (gsA10FullCoefficient low high lambda alpha beta) X

/-- The finite-window rectangular prefix average used by the A.10 Perron
contour. -/
def gsA10TailoredIntegratedPrefix
    (low high lambda : ArithmeticFunction ℂ) (y X : ℕ) (eta : ℝ) : ℂ :=
  2 * ∫ alpha in 0..eta, ∫ beta in 0..eta,
    positivePrefixSum
      (gsA10TailoredCoefficient low high lambda y X alpha beta) X

/-- The first secondary sum in source equation (2.4). -/
def gsA10FirstSecondaryPrefix
    (low high : ArithmeticFunction ℂ) (X : ℕ) (eta : ℝ) : ℂ :=
  positivePrefixSum (fun n ↦ (low * gsRealShift eta high) n) X

/-- The single integrated generalized-Mangoldt secondary sum in source
equation (2.4). -/
def gsA10SecondSecondaryPrefix
    (low high lambda : ArithmeticFunction ℂ) (X : ℕ) (eta : ℝ) : ℂ :=
  ∫ alpha in 0..eta,
    positivePrefixSum
      (fun n ↦ ((low * gsRealShift alpha lambda) *
        gsRealShift (2 * eta + alpha) high) n) X

/-- One global coefficient-side error.  Its first two summands are exactly
the two Shiu sums of source Lemma 2.4; its last summand is the single
full-to-windowed discrepancy before Perron.  Keeping the discrepancy whole
avoids any block-count or Cauchy loss. -/
def gsA10GlobalSecondaryError
    (low high lambda : ArithmeticFunction ℂ)
    (y X : ℕ) (eta : ℝ) : ℝ :=
  ‖gsA10FirstSecondaryPrefix low high X eta‖ +
    ‖gsA10SecondSecondaryPrefix low high lambda X eta‖ +
    ‖gsA10FullIntegratedPrefix low high lambda X eta -
      gsA10TailoredIntegratedPrefix low high lambda y X eta‖

/-- Specialized rectangular average for the actual reconstructed two-block
coefficient. -/
def gsA10TwoBlockTailoredIntegratedPrefix
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (eta : ℝ) : ℂ :=
  gsA10TailoredIntegratedPrefix
    (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
    (gsA9HighArithmetic f y)
    (gsA9HighGeneralizedMangoldt hmul y) y X eta

/-- Specialized global secondary error for the actual whole two-block
reconstruction. -/
def gsA10TwoBlockGlobalSecondaryError
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (eta : ℝ) : ℝ :=
  gsA10GlobalSecondaryError
    (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
    (gsA9HighArithmetic f y)
    (gsA9HighGeneralizedMangoldt hmul y) y X eta

/-- The exact finite Lemma 2.2 identity bounds the whole low--high prefix by
the tailored rectangular average plus the one global secondary scalar.
This statement is unconditional apart from the algebraic generalized-
Mangoldt identity. -/
theorem norm_positivePrefixSum_mul_sub_gsA10TailoredIntegratedPrefix_le
    (low high lambda : ArithmeticFunction ℂ)
    (y X : ℕ) (eta : ℝ)
    (hlambda : lambda * high = gsLogWeighted high) :
    ‖positivePrefixSum (fun n ↦ (low * high) n) X -
        gsA10TailoredIntegratedPrefix low high lambda y X eta‖ ≤
      gsA10GlobalSecondaryError low high lambda y X eta := by
  have hid :
      gsA10FullIntegratedPrefix low high lambda X eta =
        positivePrefixSum (fun n ↦ (low * high) n) X -
          gsA10FirstSecondaryPrefix low high X eta -
          gsA10SecondSecondaryPrefix low high lambda X eta := by
    simpa [gsA10FullIntegratedPrefix, gsA10FirstSecondaryPrefix,
      gsA10SecondSecondaryPrefix] using
      two_mul_intervalIntegral_intervalIntegral_gsA10FullCoefficient_eq
        low high lambda X eta hlambda
  have hdecomp :
      positivePrefixSum (fun n ↦ (low * high) n) X -
          gsA10TailoredIntegratedPrefix low high lambda y X eta =
        (gsA10FirstSecondaryPrefix low high X eta +
          gsA10SecondSecondaryPrefix low high lambda X eta) +
          (gsA10FullIntegratedPrefix low high lambda X eta -
            gsA10TailoredIntegratedPrefix low high lambda y X eta) := by
    rw [hid]
    ring
  rw [hdecomp]
  unfold gsA10GlobalSecondaryError
  calc
    ‖gsA10FirstSecondaryPrefix low high X eta +
          gsA10SecondSecondaryPrefix low high lambda X eta +
        (gsA10FullIntegratedPrefix low high lambda X eta -
          gsA10TailoredIntegratedPrefix low high lambda y X eta)‖ ≤
        ‖gsA10FirstSecondaryPrefix low high X eta +
          gsA10SecondSecondaryPrefix low high lambda X eta‖ +
        ‖gsA10FullIntegratedPrefix low high lambda X eta -
          gsA10TailoredIntegratedPrefix low high lambda y X eta‖ :=
      norm_add_le _ _
    _ ≤
        (‖gsA10FirstSecondaryPrefix low high X eta‖ +
          ‖gsA10SecondSecondaryPrefix low high lambda X eta‖) +
        ‖gsA10FullIntegratedPrefix low high lambda X eta -
          gsA10TailoredIntegratedPrefix low high lambda y X eta‖ := by
      gcongr
      exact norm_add_le _ _

/-- Source-ready whole two-block A.10 reconstruction.  The left side is the
actual reconstructed coefficient consumed by `MRGSA10ToA9Central`; the
rectangular term contains the finite tailored coefficients used by Perron,
and the right side is one explicit global secondary error. -/
theorem norm_positivePrefixSum_gsA10TwoBlockReconstructed_sub_tailored_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (eta : ℝ) :
    ‖positivePrefixSum
          (gsA10TwoBlockReconstructedCoefficient f P₁ P₂ y) X -
        gsA10TwoBlockTailoredIntegratedPrefix
          f hmul P₁ P₂ y X eta‖ ≤
      gsA10TwoBlockGlobalSecondaryError f hmul P₁ P₂ y X eta := by
  change
    ‖positivePrefixSum
          (fun n ↦ (gsA10TwoBlockAlternatingLow f P₁ P₂ y *
            gsA9HighArithmetic f y) n) X -
        gsA10TailoredIntegratedPrefix
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsA9HighGeneralizedMangoldt hmul y) y X eta‖ ≤
      gsA10GlobalSecondaryError
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y) y X eta
  exact norm_positivePrefixSum_mul_sub_gsA10TailoredIntegratedPrefix_le
    (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
    (gsA9HighArithmetic f y)
    (gsA9HighGeneralizedMangoldt hmul y) y X eta
    (gsA9HighGeneralizedMangoldt_mul_high hmul y)

/-- Direct source-facing form: the reconstructed prefix is controlled by
the norm of the one tailored rectangular average and the one global
secondary scalar. -/
theorem norm_positivePrefixSum_gsA10TwoBlockReconstructed_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (eta : ℝ) :
    ‖positivePrefixSum
        (gsA10TwoBlockReconstructedCoefficient f P₁ P₂ y) X‖ ≤
      ‖gsA10TwoBlockTailoredIntegratedPrefix
        f hmul P₁ P₂ y X eta‖ +
      gsA10TwoBlockGlobalSecondaryError f hmul P₁ P₂ y X eta := by
  let A := positivePrefixSum
    (gsA10TwoBlockReconstructedCoefficient f P₁ P₂ y) X
  let T := gsA10TwoBlockTailoredIntegratedPrefix
    f hmul P₁ P₂ y X eta
  let E := gsA10TwoBlockGlobalSecondaryError f hmul P₁ P₂ y X eta
  have hdiff : ‖A - T‖ ≤ E :=
    norm_positivePrefixSum_gsA10TwoBlockReconstructed_sub_tailored_le
      hmul P₁ P₂ y X eta
  have hsplit : A = (A - T) + T := by ring
  change ‖A‖ ≤ ‖T‖ + E
  rw [hsplit]
  calc
    ‖A - T + T‖ ≤ ‖A - T‖ + ‖T‖ := norm_add_le _ _
    _ ≤ E + ‖T‖ := by gcongr
    _ = ‖T‖ + E := by ring

end

end Erdos67b.MRHalaszBands
