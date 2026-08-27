/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OffsetOuterQuadraticBarrier
import ErdosProblems.Erdos207.FineInitialOuterCorridorStart

/-!
# Fine constant-offset barriers

The exact eligible-pair clock permits favourable coefficients `4 - ε` and
`4 + ε`.  A constant `32 ε N` pays for both initial inequalities and then
cancels from every discrete derivative.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

def fineOffsetUpperCoefficient (t : ℕ) : ℝ≥0 :=
  4 - fineOuterCorridorError t

def fineOffsetLowerCoefficient (t : ℕ) : ℝ≥0 :=
  4 + fineOuterCorridorError t

def fineOuterInitialOffset (N : ℕ) (t : ℕ) : ℝ :=
  ((32 * fineOuterCorridorError t * N : ℝ≥0) : ℝ)

/-- With slope exactly three, the affine clock is the actual eligible-pair
count at every time before exhaustion. -/
lemma exactOuterEnvelope_eq_eligiblePairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (i : ℕ)
    (hi : 3 * i ≤ outerSharpEligiblePairs H X 0) :
    affineSurvivalEnvelope (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 i =
      (outerSharpEligiblePairs H X i : ℕ) := by
  simpa [perturbedOuterUpperR0, perturbedOuterUpperSlope] using
    perturbedOuterUpperEnvelope_eq H X 0 i (by norm_num) hi

/-- Consequently the exact-clock quadratic barrier has a closed form in
the live eligible-pair count. -/
lemma exactClockQuadraticPairBarrier_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (N coefficient : ℝ≥0) (i : ℕ)
    (hi : 3 * i ≤ outerSharpEligiblePairs H X 0) :
    quadraticPairBarrier N coefficient
        (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 i =
      ((coefficient * (outerSharpEligiblePairs H X i : ℕ) ^ 2 *
        N⁻¹ ^ 3 : ℝ≥0) : ℝ) := by
  unfold quadraticPairBarrier
  rw [exactOuterEnvelope_eq_eligiblePairs H X i hi]

/-- The rounded constant-offset barriers differ from their exact live-clock
quadratics by only the supplied offset, buffer, and one rounding unit. -/
lemma offsetQuadratic_rounded_exactClock_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (N upperCoefficient lowerCoefficient : ℝ≥0)
    (offset buffer : ℝ) (i : ℕ)
    (hi : 3 * i ≤ outerSharpEligiblePairs H X 0)
    (hoffsetBuffer : 0 ≤ offset + buffer)
    (hlowerOne : 1 ≤
      quadraticPairBarrier N lowerCoefficient
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 i - offset - buffer) :
    (offsetQuadraticUpper N upperCoefficient
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 offset buffer i : ℝ) <
        ((upperCoefficient * (outerSharpEligiblePairs H X i : ℕ) ^ 2 *
          N⁻¹ ^ 3 : ℝ≥0) : ℝ) + offset + buffer + 1 ∧
      ((lowerCoefficient * (outerSharpEligiblePairs H X i : ℕ) ^ 2 *
          N⁻¹ ^ 3 : ℝ≥0) : ℝ) - offset - buffer - 1 <
        offsetQuadraticLower N lowerCoefficient
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 offset buffer i := by
  constructor
  · unfold offsetQuadraticUpper
    have hbar := exactClockQuadraticPairBarrier_eq
      H X N upperCoefficient i hi
    have hround := nonnegativeNatCeil_lt_add_one
      (add_nonneg (quadraticPairBarrier_nonneg N upperCoefficient
        (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 i) hoffsetBuffer)
    simpa only [hbar, add_assoc] using hround
  · unfold offsetQuadraticLower
    have hbar := exactClockQuadraticPairBarrier_eq
      H X N lowerCoefficient i hi
    have hround := sub_one_lt_nonnegativeNatFloor hlowerOne
    simpa only [hbar] using hround

lemma fineOffsetUpperCoefficient_coe
    {t : ℕ} (he : fineOuterCorridorError t ≤ 4) :
    (fineOffsetUpperCoefficient t : ℝ) =
      4 - (fineOuterCorridorError t : ℝ) := by
  exact NNReal.coe_sub he

/-- Coercing the fine upper live-clock quadratic to `ℝ` gives the expected
coefficient-times-scale expression.  Keeping this cast normalization in one
place avoids duplicating a large `NNReal` coercion calculation in every
endpoint obligation. -/
lemma fineOffsetUpper_liveQuadratic_eq
    {t : ℕ} (he : fineOuterCorridorError t ≤ 4) (E N : ℝ≥0) :
    ((fineOffsetUpperCoefficient t * E ^ 2 * N⁻¹ ^ 3 : ℝ≥0) : ℝ) =
      (4 - (fineOuterCorridorError t : ℝ)) *
        ((E ^ 2 * N⁻¹ ^ 3 : ℝ≥0) : ℝ) := by
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv,
    fineOffsetUpperCoefficient_coe he]
  ring

/-- Coercing the fine lower live-clock quadratic to `ℝ` gives the expected
coefficient-times-scale expression. -/
lemma fineOffsetLower_liveQuadratic_eq (t : ℕ) (E N : ℝ≥0) :
    ((fineOffsetLowerCoefficient t * E ^ 2 * N⁻¹ ^ 3 : ℝ≥0) : ℝ) =
      (4 + (fineOuterCorridorError t : ℝ)) *
        ((E ^ 2 * N⁻¹ ^ 3 : ℝ≥0) : ℝ) := by
  simp only [fineOffsetLowerCoefficient, NNReal.coe_mul, NNReal.coe_add,
    NNReal.coe_ofNat, NNReal.coe_pow, NNReal.coe_inv]
  ring

/-- If the real argument of the rounded lower barrier is at least one, the
resulting natural endpoint is positive. -/
lemma offsetQuadraticLower_pos_of_one
    {N coefficient R0 slope : ℝ≥0} {offset buffer : ℝ} {i : ℕ}
    (h : 1 ≤ quadraticPairBarrier N coefficient R0 slope i - offset - buffer) :
    0 < offsetQuadraticLower N coefficient R0 slope offset buffer i := by
  unfold offsetQuadraticLower nonnegativeNatFloor
  rw [max_eq_right (by linarith :
    0 ≤ quadraticPairBarrier N coefficient R0 slope i - offset - buffer)]
  exact Nat.floor_pos.mpr h

/-- The same near-complete eligible-pair estimate used at time zero places
the exact initial degree between the two offset barriers. -/
theorem fineOuter_initial_offset_barrier_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V) (outside lower₀ t : ℕ)
    (houtside : 0 < outside)
    (hsmall : ((fineOuterCorridorError t : ℝ≥0) : ℝ) ≤ 1 / 100)
    (hpairLower : (outside : ℝ) ^ 2 *
        (1 - 3 * (fineOuterCorridorError t : ℝ≥0)) ≤
      2 * (outerSharpEligiblePairs H X 0 : ℕ))
    (hpairUpper : 2 * (outerSharpEligiblePairs H X 0 : ℕ) ≤
      (outside : ℝ) ^ 2)
    (hlower₀ : (1 - 16 * (fineOuterCorridorError t : ℝ≥0)) * outside ≤
      (lower₀ : ℝ)) :
    (outside : ℝ) ≤
        quadraticPairBarrier (outside : ℝ≥0)
          (fineOffsetUpperCoefficient t)
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 +
            fineOuterInitialOffset outside t ∧
      quadraticPairBarrier (outside : ℝ≥0)
          (fineOffsetLowerCoefficient t)
          (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 -
            fineOuterInitialOffset outside t ≤ (lower₀ : ℝ) := by
  let epsilon : ℝ := (fineOuterCorridorError t : ℝ≥0)
  let E : ℝ := outerSharpEligiblePairs H X 0
  let N : ℝ := outside
  have hepsilon : 0 ≤ epsilon := by positivity
  have hE : 0 ≤ E := by positivity
  have hN : 0 < N := by
    have : (0 : ℝ) < (outside : ℝ) := by exact_mod_cast houtside
    simpa only [N] using this
  have he4NN : fineOuterCorridorError t ≤ (4 : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    change epsilon ≤ 4
    linarith
  have hfactor : 0 ≤ 1 - 3 * epsilon := by linarith
  have hpairUpper' : E ≤ N ^ 2 / 2 := by
    dsimp only [N, E]
    linarith [hpairUpper]
  have hEsquare : 4 * E ^ 2 ≤ N ^ 4 := by
    nlinarith [sq_nonneg (N ^ 2 - 2 * E)]
  have hsquare : N ^ 4 * (1 - 3 * epsilon) ^ 2 ≤ 4 * E ^ 2 := by
    have h2E : 0 ≤ 2 * E := by positivity
    have hs := (sq_le_sq₀ (mul_nonneg (sq_nonneg N) hfactor)
      h2E).2
        (by simpa only [N, E, epsilon] using hpairLower)
    nlinarith
  have hupperCross : (1 - 32 * epsilon) * N ^ 4 ≤
      (4 - epsilon) * E ^ 2 := by
    have hmul : 0 ≤ epsilon * (N ^ 4 - 4 * E ^ 2) :=
      mul_nonneg hepsilon (sub_nonneg.mpr hEsquare)
    nlinarith [sq_nonneg epsilon, sq_nonneg (1 - 3 * epsilon)]
  have hupperScaled : (1 - 32 * epsilon) * N ≤
      (4 - epsilon) * E ^ 2 * N⁻¹ ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_right hupperCross
      (show 0 ≤ N⁻¹ ^ 3 by positivity)
    calc
      (1 - 32 * epsilon) * N =
          ((1 - 32 * epsilon) * N ^ 4) * N⁻¹ ^ 3 := by
        field_simp
      _ ≤ ((4 - epsilon) * E ^ 2) * N⁻¹ ^ 3 := hmul
      _ = (4 - epsilon) * E ^ 2 * N⁻¹ ^ 3 := rfl
  have hupper : N ≤
      (4 - epsilon) * E ^ 2 * N⁻¹ ^ 3 + 32 * epsilon * N := by
    linarith
  have hlowerCross : (4 + epsilon) * E ^ 2 ≤
      (1 + 16 * epsilon) * N ^ 4 := by
    nlinarith [sq_nonneg E, sq_nonneg N]
  have hlowerScaled : (4 + epsilon) * E ^ 2 * N⁻¹ ^ 3 ≤
      (1 + 16 * epsilon) * N :=
    mul_inv_cube_le_of_crossmul hN hlowerCross
  have hlower : (4 + epsilon) * E ^ 2 * N⁻¹ ^ 3 -
      32 * epsilon * N ≤ (1 - 16 * epsilon) * N := by
    linarith
  constructor
  · simpa [quadraticPairBarrier, affineSurvivalEnvelope,
      fineOffsetUpperCoefficient_coe he4NN, fineOuterInitialOffset,
      N, E, epsilon] using hupper
  · apply (show quadraticPairBarrier (outside : ℝ≥0)
        (fineOffsetLowerCoefficient t)
        (outerSharpEligiblePairs H X 0 : ℝ≥0) 3 0 -
          fineOuterInitialOffset outside t ≤
      (1 - 16 * epsilon) * N by
        simpa [quadraticPairBarrier, affineSurvivalEnvelope,
          fineOffsetLowerCoefficient, fineOuterInitialOffset,
          N, E, epsilon] using hlower).trans
    simpa only [N, epsilon] using hlower₀

/-- Power-vortex specialization of the constant-offset initial corridor. -/
theorem FineInitialPowerVortexPackage.initialOuter_offset_barrier_bounds
    {q h n ell t T rootPower step : ℕ}
    (P : FineInitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell)
    (houtside : 0 <
      (Finset.univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card)
    (hsmall : ((fineOuterCorridorError T : ℝ≥0) : ℝ) ≤ 1 / 100)
    (habsorberFits :
      (highGirthAbsorberCardCoefficient (q + 2) *
          (2 * t ^ rootPower) ^ 156) ^ 2 ≤
        Nat.choose
          (Finset.univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card 2)
    (hdefect :
      let outside :=
        (Finset.univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      let absorberBound := highGirthAbsorberCardCoefficient (q + 2) *
        (2 * t ^ rootPower) ^ 156
      ((outside + 2 * absorberBound ^ 2 : ℕ) : ℝ) ≤
        3 * (fineOuterCorridorError T : ℝ≥0) * outside ^ 2)
    (hlower₀ :
      let outside :=
        (Finset.univ \ P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card
      let lower₀ :=
        outside - 2 * (n / t ^ fineInitialExponent) - 4 + 1
      (1 - 16 * (fineOuterCorridorError T : ℝ≥0)) * outside ≤
        (lower₀ : ℝ)) :
    let i : Fin ell := ⟨0, hell⟩
    let U := P.W.U i.succ
    let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
    let Hout := (internalOuterGraph G U)ᶜ
    let outside := (Finset.univ \ U).card
    let lower₀ := outside - 2 * (n / t ^ fineInitialExponent) - 4 + 1
    (outside : ℝ) ≤
        quadraticPairBarrier (outside : ℝ≥0)
          (fineOffsetUpperCoefficient T)
          (outerSharpEligiblePairs Hout U 0 : ℝ≥0) 3 0 +
            fineOuterInitialOffset outside T ∧
      quadraticPairBarrier (outside : ℝ≥0)
          (fineOffsetLowerCoefficient T)
          (outerSharpEligiblePairs Hout U 0 : ℝ≥0) 3 0 -
            fineOuterInitialOffset outside T ≤ (lower₀ : ℝ) := by
  dsimp only
  let i : Fin ell := ⟨0, hell⟩
  let U := P.W.U i.succ
  let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let Hout := (internalOuterGraph G U)ᶜ
  let outside := (Finset.univ \ U).card
  let lower₀ := outside - 2 * (n / t ^ fineInitialExponent) - 4 + 1
  have hpairs := P.initialOuter_eligiblePair_bounds (T := T) hell habsorberFits hdefect
  apply fineOuter_initial_offset_barrier_bounds Hout U outside lower₀ T
    (by simpa only [outside, U, i] using houtside) hsmall
  · simpa only [Hout, U, G, i, outside] using hpairs.1
  · simpa only [Hout, U, G, i, outside] using hpairs.2
  · simpa only [lower₀, outside, U, i] using hlower₀

end

end Erdos207
