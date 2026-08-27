/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceRandomBadEvents

/-! # A simultaneous source-preserving random augmentation on the actual product law -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def sourceRandomFailureCoefficient
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (j : ℕ) : ℕ :=
  (sourceRandomRootIndex W j).card + 3 * Fintype.card (TripleOn V × TripleOn V) +
    Fintype.card (TripleOn V × VortexPairOn V)

namespace SourceRandomConfigurationParameters

variable {V : Type*} [Fintype V] [DecidableEq V] {ell j s : ℕ}
  {W : Vortex V ell} {delta a : ℝ≥0}

theorem goodCounts_failure_probability (P : SourceRandomConfigurationParameters W j delta a s)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) :
    P.law.probability (fun ω ↦ ¬ SourceRandomCountsGood W j F a ω) ≤
      sourceRandomFailureCoefficient W j * ((2 : ℝ≥0) ^ s)⁻¹ := by
  have hcover : P.law.probability (fun ω ↦ ¬ SourceRandomCountsGood W j F a ω) ≤
      P.law.probability (fun ω ↦ SourceRandomRootBad W j a ω ∨ SourceRandomPairBad W j F a ω ∨
        SourceRandomOrderFourBad W j a ω) :=
    P.law.probability_mono (fun ω h ↦ not_sourceRandomCountsGood_covered W F a ω h)
  apply hcover.trans
  apply (P.law.probability_or_le _ _).trans
  apply (add_le_add le_rfl (P.law.probability_or_le _ _)).trans
  apply (add_le_add P.rootBad_probability_le
    (add_le_add (P.pairBad_probability_le F y z hF hdeltaY) P.orderFourBad_probability_le)).trans_eq
  simp only [sourceRandomFailureCoefficient, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem augmentation_failure_probability (P : SourceRandomConfigurationParameters W j delta a s)
    (F : ForbiddenFamilyOn V) (y z : ℝ≥0) (hF : SourceVortexWellSpread W j F y z)
    (hdeltaY : delta * y ≤ W.terminalSize) :
    P.law.probability (fun ω ↦ ¬ SourceVortexWellSpread W j
      (F ∪ sampleTerminalConfigurations W j ω) (y + a) (z + 3 * a)) ≤
        sourceRandomFailureCoefficient W j * ((2 : ℝ≥0) ^ s)⁻¹ := by
  have hmono : P.law.probability (fun ω ↦ ¬ SourceVortexWellSpread W j
      (F ∪ sampleTerminalConfigurations W j ω) (y + a) (z + 3 * a)) ≤
        P.law.probability (fun ω ↦ ¬ SourceRandomCountsGood W j F a ω) := by
    apply P.law.probability_mono
    intro ω hbad hgood
    exact hbad (hgood.sourceWellSpread hF)
  exact hmono.trans (P.goodCounts_failure_probability F y z hF hdeltaY)

end SourceRandomConfigurationParameters

end

end Erdos207
