/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCanonicalExtension
import ErdosProblems.Erdos599.RegularCanonicalProviderFinal

/-!
# Final regular assembly from source-9.15 tracked tables

This module discharges the complete canonical history recursion and leaves
only the two independent source inputs: grounding a ladder obstruction and
constructing the tracked 9.15 tables from the lower induction hypothesis.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularExtension

open DirectedPath

universe u

variable {V : Type u}

/-- Once the exact source-9.15 tracked tables are available, the strong
canonical recursion supplies the required internal linkage. -/
theorem isLinkable_of_regularCanonicalTrackedTables
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (A₀ : Set V) (hA₀source : A₀ ⊆ G.source)
    (hA₀card : #A₀ = kappa)
    (F : Set G.DPath)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hground :
      let Q := RegularRows.CausalRegular.rowRule G hkappa
        hkappaUncountable hG hlower F hF.isWarp A₀ hA₀card.le
      let L := DWeb.KappaLadder.canonicalLadder G kappa
        (Q.preferred hkappa.aleph0_le)
      L.IsKappaHindrance → ∃ W : Set G.DPath, G.IsHindrance W)
    (htracked :
      let Q := RegularRows.CausalRegular.rowRule G hkappa
        hkappaUncountable hG hlower F hF.isWarp A₀ hA₀card.le
      let R := Q.rowSystem hkappa.aleph0_le
      let L := DWeb.KappaLadder.canonicalLadder G kappa
        (Q.preferred hkappa.aleph0_le)
      ∀ (Sigma : Set (Ladder.Stage kappa)),
        Stationary.IsClubBelow kappa Sigma →
        Disjoint Sigma L.phi →
        SliceCandidate.HasTrackedTightAnnularControlledSlices
            G L Sigma R.carrier ∧
          (∀ U : Set V,
            U ⊆ L.frontier ⟨0, hkappa.ord_pos⟩ ∩ R.carrier →
            #U < kappa →
              ∃ beta ∈ Sigma, ⟨0, hkappa.ord_pos⟩ < beta ∧
                ∃ T, SliceCandidate.IsTrackedTightAnnularControlledSlice
                  G L R.carrier ⟨0, hkappa.ord_pos⟩ beta U T)) :
    IsLinkable G := by
  let Q := RegularRows.CausalRegular.rowRule G hkappa
    hkappaUncountable hG hlower F hF.isWarp A₀ hA₀card.le
  let R := Q.rowSystem hkappa.aleph0_le
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hkappa.aleph0_le)
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hG hxy).1 hy
  have hL : L.IsLegal :=
    DWeb.KappaLadder.canonicalLadderWithBookkeeping_isLegal
      (Q.preferred hkappa.aleph0_le) hkappa hkappaUncountable hNoEnter
  have hclosed : SliceSplice.IsLimitWarpClosed G L R.carrier :=
    causalRowCarrier_isLimitWarpClosed G hkappa hkappaUncountable
      hG hlower F hF.isWarp A₀ hA₀card.le
  apply isLinkable_of_regularCanonicalAdmissibleProvider G hkappa
    hkappaUncountable hG hUnhindered hlower A₀ hA₀source hA₀card F hF
      hground
  dsimp only
  intro Sigma hSigma havoid request
  obtain ⟨hslices, hfirst⟩ := htracked Sigma hSigma havoid
  exact RegularCanonicalProviderFinal.hasCanonicalStageProvider
    hG hUnhindered hL hSigma havoid hclosed hslices hfirst request

/-- Normalized extension-clause transport from the exact grounding and
tracked-table source theorems. -/
theorem regularExtensionClauseStep_of_canonicalTrackedTables
    (kappa : Cardinal.{u})
    (hlower : UniversalCardinalInductionBelow V kappa)
    (hregular : kappa.IsRegular) (hkappa : aleph0 < kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered)
    (hall :
      ∀ (A₀ : Set V), A₀ ⊆ Gamma.normalized.source →
      ∀ (hcard : #A₀ = kappa),
      ∀ (F : Set Gamma.normalized.DPath),
      ∀ (hF : IsLinkageBetween Gamma.normalized
          (Gamma.normalized.source \ A₀) Gamma.normalized.target F),
        let Q := RegularRows.CausalRegular.rowRule Gamma.normalized hregular
          hkappa Gamma.normalized_isNormalized hlower F hF.isWarp A₀ hcard.le
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
  apply RegularNormalization.extensionClauseAt_of_normalized kappa hkappa.le
  intro A₀ hA₀ hcard hcomplement
  obtain ⟨F, hF⟩ := hcomplement
  have hproviders := hall A₀ hA₀ hcard F hF
  exact isLinkable_of_regularCanonicalTrackedTables Gamma.normalized
    hregular hkappa Gamma.normalized_isNormalized hGamma.normalized hlower
      A₀ hA₀ hcard F hF hproviders.1 hproviders.2

end RegularExtension
end CardinalInduction
end Erdos599
