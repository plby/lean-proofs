/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularEnrichedExactCandidate

/-!
# Exact-frontier regular extension from grounding

The exact half-way construction now supplies every annular coordinate
which the source-faithful splice actually reaches.  The only remaining
input of the regular branch is therefore the grounding of a canonical
ladder hindrance in the ambient normalized web.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularExtension

universe u

variable {V : Type u}

/-- Exact-frontier regular extension with the source-9.15 coordinate
provider discharged.  This is the final regular assembly boundary before
the Section 8 grounding theorem. -/
theorem regularExtensionClauseStep_of_exactGrounding
    (kappa : Cardinal.{u})
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (hkappa : aleph0 < kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hground :
      ∀ (A₀ : Set V), A₀ ⊆ Gamma.normalized.source →
      ∀ (hcard : #A₀ = kappa),
      ∀ (F : Set Gamma.normalized.DPath),
      ∀ (hF : IsLinkageBetween Gamma.normalized
          (Gamma.normalized.source \ A₀) Gamma.normalized.target F),
        let lower := hlower.toUniversalCardinalInductionBelow
        let Q := RegularRows.CausalRegular.weakSplitRowRule
          Gamma.normalized hregular hkappa Gamma.normalized_isNormalized
            lower F hF.isWarp A₀ hcard.le
        let L := DWeb.KappaLadder.canonicalLadder Gamma.normalized kappa
          (Q.preferred hregular.aleph0_le)
        L.IsKappaHindrance →
          ∃ W : Set Gamma.normalized.DPath,
            Gamma.normalized.IsHindrance W) :
    ExtensionClauseAt Gamma kappa := by
  apply regularExtensionClauseStep_of_exactCandidateProviders kappa
    hlower hregular hkappa Gamma hGamma hground
  intro A₀ hA₀ hcard F hF
  exact RegularEnrichedExactCandidate.hasExactAnnularCoordinateProvider
    Gamma.normalized hregular hkappa Gamma.normalized_isNormalized
      hlower F hF.isWarp A₀ hcard.le

#print axioms regularExtensionClauseStep_of_exactGrounding

end RegularExtension
end CardinalInduction
end Erdos599
