/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineOuterCanonicalProcessBounds

/-!
# A zero-slope survival envelope for the canonical outer corridor

The probabilistic product theorem does not require its auxiliary affine
envelope to follow the eligible-pair clock sharply.  For the first compressed
transition it is enough to take the constant envelope `R i = E₀`.  This gives
the harmless product parameter `p = 1`; the already proved clock comparison
still bounds the retrospective point term by only polynomial powers of the
dyadic scale.

This file packages all six envelope hypotheses.  Only two transparent scale
inequalities remain for the eventual power hierarchy: a quadratic lower
bound for `E₀`, and the local cubic comparison at the uniform degree floor.
-/

namespace Erdos207

open scoped NNReal

noncomputable section

/-- The complete affine-envelope certificate consumed by
`outerSharpRecursive_absorberInitialProductLaw`, specialized to slope zero. -/
structure FineOuterZeroEnvelopeBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc K fuel dmin : ℕ)
    (Aenv Bscale Q : ℝ≥0) : Prop where
  envelope_pos : (fuel : ℝ≥0) * 0 <
    (outerSharpEligiblePairs H X 0 : ℕ)
  all_envelope : ∀ i, i < fuel →
    (outerSharpEligiblePairs H X i : ℝ≥0) ≤
      affineSurvivalEnvelope
        (outerSharpEligiblePairs H X 0 : ℕ) 0 i
  envelope_ratio :
    affineSurvivalEnvelope
        (outerSharpEligiblePairs H X 0 : ℕ) 0 fuel /
          (outerSharpEligiblePairs H X 0 : ℕ) ≤ 1
  envelope_loss : ∀ i, i < fuel →
    (0 : ℝ≥0) *
        (outerSharpUpperSchedule H X upper₀ lower₀ buffer Kinc i : ℕ) ≤
      3 * (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i -
        3 * K : ℕ)
  envelope_eligible : ∀ i, i < fuel →
    affineSurvivalEnvelope
        (outerSharpEligiblePairs H X 0 : ℕ) 0 i ≤
      Aenv * (outerSharpEligiblePairs H X i : ℕ)
  pair_scale : ∀ i, i < fuel →
    ((outerSharpEligiblePairs H X i : ℕ) : ℝ≥0) ^ 2 ≤
      Bscale * (Fintype.card V : ℝ≥0) ^ 3 *
        (outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i : ℕ)
  quadratic : (Fintype.card V : ℝ≥0) ^ 2 ≤
    Q * (outerSharpEligiblePairs H X 0 : ℕ)

/-- A uniform schedule floor and the canonical clock comparison imply the
zero-slope envelope certificate. -/
theorem fineOuterZeroEnvelopeBounds_of_uniform
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (X : Finset V)
    (upper₀ lower₀ buffer : ℝ) (Kinc K fuel dmin : ℕ)
    (Aenv Bscale Q : ℝ≥0)
    (hE0 : 0 < outerSharpEligiblePairs H X 0)
    (hfloor : ∀ i, i ≤ fuel →
      dmin ≤ outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i)
    (hclock : ∀ i, i ≤ fuel →
      (outerSharpEligiblePairs H X 0 : ℝ≥0) ≤
        Aenv * (outerSharpEligiblePairs H X i : ℕ))
    (hpairScalar :
      ((outerSharpEligiblePairs H X 0 : ℕ) : ℝ≥0) ^ 2 ≤
        Bscale * (Fintype.card V : ℝ≥0) ^ 3 * dmin)
    (hquadratic : (Fintype.card V : ℝ≥0) ^ 2 ≤
      Q * (outerSharpEligiblePairs H X 0 : ℕ)) :
    FineOuterZeroEnvelopeBounds H X upper₀ lower₀ buffer Kinc K fuel dmin
      Aenv Bscale Q := by
  have hmono : ∀ i,
      outerSharpEligiblePairs H X i ≤ outerSharpEligiblePairs H X 0 := by
    intro i
    unfold outerSharpEligiblePairs
    omega
  have hE0nn : (outerSharpEligiblePairs H X 0 : ℝ≥0) ≠ 0 := by
    exact_mod_cast hE0.ne'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hquadratic⟩
  · simpa only [mul_zero] using (show
      (0 : ℝ≥0) < (outerSharpEligiblePairs H X 0 : ℕ) by
        exact_mod_cast hE0)
  · intro i _hi
    simp only [affineSurvivalEnvelope, mul_zero, tsub_zero]
    exact_mod_cast hmono i
  · simp only [affineSurvivalEnvelope, mul_zero, tsub_zero]
    rw [div_self hE0nn]
  · intro i _hi
    simp only [zero_mul]
    positivity
  · intro i hi
    simpa only [affineSurvivalEnvelope, mul_zero, tsub_zero] using
      hclock i hi.le
  · intro i hi
    have hEi :
        (outerSharpEligiblePairs H X i : ℝ≥0) ≤
          outerSharpEligiblePairs H X 0 := by
      exact_mod_cast hmono i
    have hd : (dmin : ℝ≥0) ≤
        outerSharpLowerSchedule H X upper₀ lower₀ buffer Kinc i := by
      exact_mod_cast hfloor i hi.le
    exact (pow_le_pow_left' hEi 2).trans <|
      hpairScalar.trans <| by gcongr

end

end Erdos207
