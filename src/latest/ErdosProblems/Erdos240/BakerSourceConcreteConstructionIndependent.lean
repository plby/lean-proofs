/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerSourceAssemblyIndependent
import ErdosProblems.Erdos240.BakerSourceNumericalAssemblyIndependent
import ErdosProblems.Erdos240.BakerLemma6Descent
import ErdosProblems.Erdos240.BakerSourceInnerStepAssemblyIndependent
import ErdosProblems.Erdos240.BakerSourceRationalAlternativeIndependent

/-!
# Concrete source construction for the independent Baker assembly

This module removes the algebraic and terminal glue from the construction of
`ConcreteSourceContinuation`.  Radical residue extraction is supplied by the
checked source-state descent theorem, and the terminal equation is already
invoked internally by `ConcreteSourceChain.false`.  The remaining fields are
exactly the three analytic extrapolation inputs and the second, coprime-node
Hermite completion.
-/

open scoped BigOperators NumberField Polynomial

noncomputable section

namespace Erdos240.BakerSourceConcreteConstructionIndependent

open BakerInduction
open BakerLemma3Instantiation
open BakerLemma6Descent
open BakerSourceState
open BakerSourceAssemblyIndependent
open BakerSourceNumericalAssemblyIndependent
open BakerSourceInnerStepAssemblyIndependent
open BakerSourceRationalAlternativeIndependent

/-- Analytic data remaining after the checked algebraic residue extraction
and terminal zero count have been installed.

The lower function is fixed to the sharp rational Liouville threshold.  The
lower alternative is supplied by the level-scaled algebraic comparison, so
the obsolete unscaled `RationalLowerInputs` route does not occur here.  This
also makes the upper and lower sides of Lemma 5 definitionally share the
same comparison value. -/
structure ConcreteAnalyticSourceData {oldRank : ℕ}
    [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ) where
  last_ne_zero : bLast ≠ 0
  integral : ∀ J (state : LevelState P J), P.LevelOK J →
    IntegralStepInputs P state b bLast
  rationalLower : ∀ J (state : LevelState P J), P.LevelOK J →
    AlgebraicRationalLowerInputs P state b bLast
  upper : ∀ J (state : LevelState P J) (hJ : P.LevelOK J),
    IntegralExtrapolatedAtLevel P (g state b bLast) J →
    RationalInterpolationUpperAtLevel P (f state b bLast)
      (BakerSourceRationalAlternativeIndependent.lower P state b bLast) J
  completeCoprime : ∀ J (state : LevelState P (J + 1)),
    P.LevelOK (J + 1) → CoprimeCompletionAtLevel P (g state b bLast) J

namespace ConcreteAnalyticSourceData

variable {oldRank : ℕ} [Nonempty (Fin oldRank)]
  {P : VDPLParameters (Fin oldRank)}
  {b : Fin oldRank → ℤ} {bLast : ℤ}

/-- Install the checked numerical Lemma-3/4 adapters and the concrete
radical residue extraction into the global continuation state machine. -/
def continuation (data : ConcreteAnalyticSourceData P b bLast) :
    ConcreteSourceContinuation P b bLast where
  last_ne_zero := data.last_ne_zero
  lower := fun _J state ↦
    BakerSourceRationalAlternativeIndependent.lower P state b bLast
  integralStep := fun J state hJ _hseed ↦
    (data.integral J state hJ).integralStep _hseed
  upperStep := fun J state hJ hint ↦ data.upper J state hJ hint
  lowerStep := fun J state hJ _hint ↦
    (data.rationalLower J state hJ).lowerStep
  descend := fun J state _hnext hrat ↦ by
    obtain ⟨rho, hrestrict, hcoprime⟩ :=
      exists_successor_coprimeSeed_of_rationalExtrapolated
        state b bLast hrat
    exact ⟨nextState state rho hrestrict, hcoprime⟩
  completeCoprime := fun J state hnext ↦
    data.completeCoprime J state hnext

end ConcreteAnalyticSourceData

/-- Package the exact pointwise local-circle conclusion as the per-level
integral input consumed by `ConcreteAnalyticSourceData`. -/
theorem integralStepInputsOfPointwise {oldRank : ℕ}
    {P : VDPLParameters (Fin oldRank)} {J : ℕ}
    (state : LevelState P J) (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hpoint : ∀ t, t < Erdos240.BakerLemma4InnerInduction.terminalStage P →
      Erdos240.BakerLemma4InnerInduction.InnerInvariant
          P (g state b bLast) J t →
        ∀ l, 1 ≤ l → l ≤ P.lemmaFourRadius J (t + 1) →
          ∀ m, VDPLMultiIndex.weight m ≤
              P.lemmaFourBudget J (t + 1) →
            g state b bLast (l : ℂ) m = 0) :
    IntegralStepInputs P state b bLast where
  innerStep := innerStepCallback_of_pointwise P (g state b bLast) J hpoint

end Erdos240.BakerSourceConcreteConstructionIndependent

#print axioms Erdos240.BakerSourceConcreteConstructionIndependent.ConcreteAnalyticSourceData.continuation
#print axioms Erdos240.BakerSourceConcreteConstructionIndependent.integralStepInputsOfPointwise
