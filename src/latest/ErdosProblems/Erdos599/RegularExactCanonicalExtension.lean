/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCanonicalExtensionFinal
import ErdosProblems.Erdos599.HalfwayExactFrontierInduction

/-!
# Exact-frontier regular canonical assembly

The regular source construction uses the exact lower-cardinal half-way
frontier to obtain a terminal-clean stop-over.  The canonical row and splice
machinery only need the ordinary projection of that lower hypothesis.  This
module records the precise seam between those two parts of the proof.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularExtension

open DirectedPath

universe u

variable {V : Type u}

/-- Exact-frontier version of the final tracked-table assembly.  The source
provider is allowed to use the stronger lower hypothesis, while the already
proved canonical recursion consumes its ordinary projection. -/
theorem regularExtensionClauseStep_of_exactCanonicalTrackedTables
    (kappa : Cardinal.{u})
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (hkappa : aleph0 < kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hall :
      let hlowerOrdinary := hlower.toUniversalCardinalInductionBelow
      ∀ (A₀ : Set V), A₀ ⊆ Gamma.normalized.source →
      ∀ (hcard : #A₀ = kappa),
      ∀ (F : Set Gamma.normalized.DPath),
      ∀ (hF : IsLinkageBetween Gamma.normalized
          (Gamma.normalized.source \ A₀) Gamma.normalized.target F),
        let Q := RegularRows.CausalRegular.rowRule Gamma.normalized hregular
          hkappa Gamma.normalized_isNormalized hlowerOrdinary F hF.isWarp
            A₀ hcard.le
        let R := Q.rowSystem hregular.aleph0_le
        let L := DWeb.KappaLadder.canonicalLadder Gamma.normalized kappa
          (Q.preferred hregular.aleph0_le)
        (L.IsKappaHindrance →
            ∃ W : Set Gamma.normalized.DPath,
              Gamma.normalized.IsHindrance W) ∧
          (∀ (Sigma : Set (Ladder.Stage kappa)),
            Stationary.IsClubBelow kappa Sigma →
            Disjoint Sigma L.phi →
            SliceCandidate.HasTrackedTightAnnularControlledSlices
                Gamma.normalized L Sigma R.carrier ∧
              (∀ U : Set V,
                U ⊆ L.frontier ⟨0, hregular.ord_pos⟩ ∩ R.carrier →
                #U < kappa →
                  ∃ beta ∈ Sigma,
                    ⟨0, hregular.ord_pos⟩ < beta ∧
                    ∃ T,
                      SliceCandidate.IsTrackedTightAnnularControlledSlice
                        Gamma.normalized L R.carrier
                          ⟨0, hregular.ord_pos⟩ beta U T))) :
    ExtensionClauseAt Gamma kappa := by
  exact regularExtensionClauseStep_of_canonicalTrackedTables kappa
    hlower.toUniversalCardinalInductionBelow hregular hkappa Gamma hGamma hall

end RegularExtension
end CardinalInduction
end Erdos599
