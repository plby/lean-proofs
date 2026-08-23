/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerLemma3Concrete
import ErdosProblems.Erdos240.BakerSourceState
import ErdosProblems.Erdos240.RationalPrimeBaker

/-!
# Normalizing the source logarithmic form

This file contains the exact algebraic glue between the source's complex
logarithmic form and the real rational-prime form used by the project-facing
Baker theorem.  It also records the equality between the normalized source
exponent and the `smallLinearFormBound` exponent consumed by concrete
Lemma 3.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerSourceLogFormNormalization

open Erdos240
open Erdos240.BakerLemma3
open Erdos240.BakerLemma3Concrete
open Erdos240.BakerSourceState
open Erdos240.RationalPrimeBaker

/-- Choosing the Lemma-3 source constant `C₀ log Ω'` gives exactly the
unabsorbed exponent used by the normalized source theorem. -/
theorem sourceExponent_eq_normalized {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (C₀ : ℝ) :
    sourceExponent P (C₀ * Real.log P.OmegaOld) =
      C₀ * P.OmegaOld * Real.log P.OmegaOld *
        Real.log P.newHeight * Real.log (P.Bsrc : ℝ) := by
  unfold sourceExponent
  ring

/-- The complex source form is the coercion of the real indexed
rational-prime logarithmic form. -/
theorem logForm_eq_indexedRationalLogForm {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ) :
    logForm b bLast (oldLog P) (lastLog P) =
      (indexedRationalLogForm P.old P.newPrime b bLast : ℂ) := by
  simp only [logForm, oldLog, lastLog, indexedRationalLogForm]
  push_cast
  rfl

/-- Consequently the complex norm appearing in Lemma 3 is literally the
real absolute value appearing in the final theorem. -/
theorem norm_logForm_eq_abs_indexedRationalLogForm {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ) :
    ‖logForm b bLast (oldLog P) (lastLog P)‖ =
      |indexedRationalLogForm P.old P.newPrime b bLast| := by
  rw [logForm_eq_indexedRationalLogForm]
  exact Complex.norm_real _

/-- A strict failure of the normalized source lower bound supplies the
nonstrict small-form hypothesis required by every concrete Lemma-3 call. -/
theorem norm_logForm_le_smallLinearFormBound_of_normalized {oldRank : ℕ}
    (P : VDPLParameters (Fin oldRank)) (C₀ : ℝ)
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hsmall :
      |indexedRationalLogForm P.old P.newPrime b bLast| <
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (P.Bsrc : ℝ)))) :
    ‖logForm b bLast (oldLog P) (lastLog P)‖ ≤
      smallLinearFormBound P (C₀ * Real.log P.OmegaOld) := by
  rw [norm_logForm_eq_abs_indexedRationalLogForm,
    smallLinearFormBound, sourceExponent_eq_normalized]
  exact hsmall.le

#print axioms sourceExponent_eq_normalized
#print axioms logForm_eq_indexedRationalLogForm
#print axioms norm_logForm_eq_abs_indexedRationalLogForm
#print axioms norm_logForm_le_smallLinearFormBound_of_normalized

end Erdos240.BakerSourceLogFormNormalization
