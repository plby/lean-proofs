/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularSplitCanonicalExtension
import ErdosProblems.Erdos599.RegularWeakSelectedProviderAssembly

/-!
# Final assembly from weak selected coordinates

This module composes the enhanced causal row, the certified-history
source-9.15 coordinate selector, and the canonical split recursion.  It is
the last bookkeeping layer before the two geometric theorems: grounding a
ladder hindrance, and producing one selected weak annular coordinate.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularExtension

universe u

variable {V : Type u}

/-- The exact split Section 8 boundary for an ordinary canonical ladder.  It is
independent of the row which produced the preferred-vertex function. -/
def HasCanonicalLadderGrounding
    (G : DWeb V) (kappa : Cardinal.{u})
    (preferred : Ladder.Stage kappa → Option V) : Prop :=
  let L := DWeb.KappaLadder.canonicalLadder G kappa preferred
  L.IsSplitKappaHindrance → ∃ W : Set G.DPath, G.IsHindrance W

/-- The coordinate provider and split-ladder grounding implication close the
regular extension step.  All row closure, diagonal request capture,
certified-history recursion, and final normalized transport are internal. -/
theorem regularExtensionClauseStep_of_weakSelectedCoordinateProviders
    (kappa : Cardinal.{u})
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (hkappa : aleph0 < kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hground :
      ∀ (A₀ : Set V), A₀ ⊆ Gamma.normalized.source →
      ∀ (hcard : #A₀ = kappa),
      ∀ (F : Set Gamma.normalized.DPath),
      ∀ (hF : IsLinkageBetween Gamma.normalized
          (Gamma.normalized.source \ A₀) Gamma.normalized.target F),
        let Q := RegularRows.CausalRegular.weakSplitRowRule
          Gamma.normalized hregular hkappa Gamma.normalized_isNormalized
            hlower F hF.isWarp A₀ hcard.le
        HasCanonicalLadderGrounding Gamma.normalized kappa
          (Q.preferred hregular.aleph0_le))
    (hcoordinate :
      ∀ (A₀ : Set V), A₀ ⊆ Gamma.normalized.source →
      ∀ (hcard : #A₀ = kappa),
      ∀ (F : Set Gamma.normalized.DPath),
      ∀ (hF : IsLinkageBetween Gamma.normalized
          (Gamma.normalized.source \ A₀) Gamma.normalized.target F),
        HasWeakSelectedCoordinateProvider Gamma.normalized hregular hkappa
          Gamma.normalized_isNormalized hlower F hF.isWarp A₀ hcard.le) :
    ExtensionClauseAt Gamma kappa := by
  apply regularExtensionClauseStep_of_weakSplitSource915Provider
    kappa hlower hregular hkappa Gamma hGamma
  intro A₀ hA₀ hcard F hF
  refine ⟨hground A₀ hA₀ hcard F hF, ?_⟩
  intro Sigma hSigma havoid request
  apply
    RegularWeakSelectedProviderAssembly.hasSelectedRoofedSource915Provider_of_coordinateProvider
      Gamma.normalized hregular hkappa Gamma.normalized_isNormalized
        hlower F hF.isWarp A₀ hcard.le Sigma hSigma havoid request
  exact hcoordinate A₀ hA₀ hcard F hF Sigma hSigma havoid request

end RegularExtension
end CardinalInduction
end Erdos599
