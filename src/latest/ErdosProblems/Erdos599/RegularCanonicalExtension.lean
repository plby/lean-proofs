/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularExtension
import ErdosProblems.Erdos599.RegularCanonicalAdmissibleProvider

/-!
# Regular extension from the canonical source-9.15 recursion

This is the direct extension-clause consumer for
`RegularCanonicalAdmissibleProvider`.  It has the same final scheduling,
closure, and untouched-linkage conclusion as the older completed/pending
wrapper, but it never broadens the stage selector to arbitrary payload
histories.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularExtension

open DirectedPath

universe u

variable {V : Type u}

/-- Regular linkability from canonical targeted-comparison stages.  The
history passed to the stage provider retains the comparison and maverick
provenance of every actual earlier stage. -/
theorem isLinkable_of_regularCanonicalAdmissibleProvider
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
    (hprovider :
      let Q := RegularRows.CausalRegular.rowRule G hkappa
        hkappaUncountable hG hlower F hF.isWarp A₀ hA₀card.le
      let R := Q.rowSystem hkappa.aleph0_le
      let L := DWeb.KappaLadder.canonicalLadder G kappa
        (Q.preferred hkappa.aleph0_le)
      ∀ (Sigma : Set (Ladder.Stage kappa)),
        Stationary.IsClubBelow kappa Sigma →
        Disjoint Sigma L.phi →
        ∀ request : Ladder.Stage kappa →
          Option ↑(G.source ∩ R.carrier),
          RegularCanonicalAdmissibleProvider.HasCanonicalStageProvider
            G hG L Sigma R.carrier (G.source ∩ R.carrier) request) :
    IsLinkable G := by
  let Q := RegularRows.CausalRegular.rowRule G hkappa
    hkappaUncountable hG hlower F hF.isWarp A₀ hA₀card.le
  let R := Q.rowSystem hkappa.aleph0_le
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hkappa.aleph0_le)
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hG hxy).1 hy
  have hL : L.IsLegal := by
    exact DWeb.KappaLadder.canonicalLadderWithBookkeeping_isLegal
      (Q.preferred hkappa.aleph0_le) hkappa hkappaUncountable hNoEnter
  obtain ⟨Sigma, hSigma, havoid⟩ :=
    exists_club_avoiding_phi_of_grounding G hUnhindered hL hground
  have hsourceCard : #↑(G.source ∩ R.carrier) ≤ kappa :=
    mk_source_inter_rowCarrier_le G R hkappa.aleph0_le
  let zero : Ladder.Stage kappa := ⟨0, hkappa.ord_pos⟩
  have hzero : ∀ j : Ladder.Stage kappa, ¬ j < zero := by
    intro j hj
    exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1)) hj
  obtain ⟨P, hP, hPclosed⟩ :=
    RegularCanonicalAdmissibleProvider.exists_internal_linkage_of_canonicalStageProvider
      hG hsourceCard zero hzero (hprovider Sigma hSigma havoid)
  have hA₀carrier : A₀ ⊆ R.carrier := by
    exact RegularRows.CausalRegular.base_subset_rowRule_carrier
      G hkappa hkappaUncountable hG hlower F hF.isWarp A₀ hA₀card.le
  have hregister : ∀ i,
      G.vertexSet (pathsMeeting G F (R.row i)) ⊆ R.carrier := by
    exact causalRowCarrier_registersOldLinkage G hkappa hkappaUncountable
      hG hlower F hF.isWarp A₀ hA₀card.le
  exact isLinkable_of_internal_linkage_on_rowCarrier
    G A₀ R F P hA₀carrier hP hPclosed hF hregister

/-- Normalized public-order wrapper for the canonical source-9.15
construction.  Unlike
`regularExtensionClauseStep_of_globalAdmissibleProviders`, its selector is
called only on canonical histories retaining the witnesses used to justify
later avoidance. -/
theorem regularExtensionClauseStep_of_canonicalAdmissibleProviders
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
            ∀ request : Ladder.Stage kappa →
              Option ↑(Gamma.normalized.source ∩ R.carrier),
              RegularCanonicalAdmissibleProvider.HasCanonicalStageProvider
                Gamma.normalized Gamma.normalized_isNormalized L Sigma
                  R.carrier (Gamma.normalized.source ∩ R.carrier)
                    request)) :
    ExtensionClauseAt Gamma kappa := by
  apply RegularNormalization.extensionClauseAt_of_normalized kappa hkappa.le
  intro A₀ hA₀ hcard hcomplement
  obtain ⟨F, hF⟩ := hcomplement
  have hproviders := hall A₀ hA₀ hcard F hF
  exact isLinkable_of_regularCanonicalAdmissibleProvider Gamma.normalized
    hregular hkappa Gamma.normalized_isNormalized hGamma.normalized hlower
    A₀ hA₀ hcard F hF hproviders.1 hproviders.2

end RegularExtension
end CardinalInduction
end Erdos599

