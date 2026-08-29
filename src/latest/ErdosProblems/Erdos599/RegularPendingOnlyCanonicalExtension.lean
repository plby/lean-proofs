/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCanonicalExtension
import ErdosProblems.Erdos599.RegularPendingOnlyCanonicalProvider
import ErdosProblems.Erdos599.RegularWeakSplitRows

/-!
# Regular extension from the pending-only canonical source-9.15 provider

This assembly uses the weak causal row but invokes source 9.15 only along
the recursively generated canonical history.  Completed target components
are not assumed to remain under later frontier roofs.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularExtension

open DirectedPath

universe u

variable {V : Type u}

theorem isLinkable_of_regularPendingOnlySource915Provider
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (A₀ : Set V) (hA₀source : A₀ ⊆ G.source)
    (hA₀card : #A₀ = kappa)
    (F : Set G.DPath)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hground :
      let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
        huncountable hNorm hlower F hF.isWarp A₀ hA₀card.le
      let L := DWeb.KappaLadder.canonicalLadder G kappa
        (Q.preferred hregular.aleph0_le)
      L.IsKappaHindrance → ∃ W : Set G.DPath, G.IsHindrance W)
    (hsource915 :
      let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
        huncountable hNorm hlower F hF.isWarp A₀ hA₀card.le
      let R := Q.rowSystem hregular.aleph0_le
      let L := DWeb.KappaLadder.canonicalLadder G kappa
        (Q.preferred hregular.aleph0_le)
      ∀ (Sigma : Set (Ladder.Stage kappa)),
        ∀ (hSigma : Stationary.IsClubBelow kappa Sigma),
        ∀ (havoid : Disjoint Sigma L.phi),
        ∀ request : Ladder.Stage kappa →
          Option ↑(G.source ∩ R.carrier),
          RegularPendingOnlyCanonicalProvider.HasSource915Provider
            G hNorm hUnhindered L Sigma
              (DWeb.KappaLadder.canonicalLadderWithBookkeeping_isLegal
                (Q.preferred hregular.aleph0_le) hregular huncountable
                (by
                  intro x y hxy hy
                  exact (hNorm hxy).1 hy))
              hSigma havoid R.carrier request) :
    IsLinkable G := by
  let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
    huncountable hNorm hlower F hF.isWarp A₀ hA₀card.le
  let R := Q.rowSystem hregular.aleph0_le
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hregular.aleph0_le)
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hL : L.IsLegal :=
    DWeb.KappaLadder.canonicalLadderWithBookkeeping_isLegal
      (Q.preferred hregular.aleph0_le) hregular huncountable hNoEnter
  obtain ⟨Sigma, hSigma, havoid⟩ :=
    exists_club_avoiding_phi_of_grounding G hUnhindered hL hground
  have hsourceCard : #↑(G.source ∩ R.carrier) ≤ kappa :=
    mk_source_inter_rowCarrier_le G R hregular.aleph0_le
  let zero : Ladder.Stage kappa := ⟨0, hregular.ord_pos⟩
  have hzero : ∀ j : Ladder.Stage kappa, ¬ j < zero := by
    intro j hj
    exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1)) hj
  obtain ⟨P, hP, hPclosed⟩ :=
    RegularPendingOnlyCanonicalRecursion.exists_internal_linkage_of_canonicalStageProvider
      hNorm hsourceCard zero hzero (by
        intro request
        exact
          RegularPendingOnlyCanonicalProvider.hasCanonicalStageProvider_of_source915
            hNorm hUnhindered hL hSigma havoid request
              (hsource915 Sigma hSigma havoid request))
  have hA₀carrier : A₀ ⊆ R.carrier :=
    RegularRows.CausalRegular.base_subset_weakSplitRowRule_carrier
      G hregular huncountable hNorm hlower F hF.isWarp A₀ hA₀card.le
  have hregister : ∀ i,
      G.vertexSet (pathsMeeting G F (R.row i)) ⊆ R.carrier :=
    RegularRows.CausalRegular.weakSplitRowCarrier_registersOldLinkage
      G hregular huncountable hNorm hlower F hF.isWarp A₀ hA₀card.le
  exact isLinkable_of_internal_linkage_on_rowCarrier
    G A₀ R F P hA₀carrier hP hPclosed hF hregister

/-- Exact normalized extension assembly over the canonical-only pending
source-9.15 boundary. -/
theorem regularExtensionClauseStep_of_pendingOnlySource915Providers
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
        let Q := RegularRows.CausalRegular.weakSplitRowRule
          Gamma.normalized hregular hkappa Gamma.normalized_isNormalized
            hlower F hF.isWarp A₀ hcard.le
        let R := Q.rowSystem hregular.aleph0_le
        let L := DWeb.KappaLadder.canonicalLadder Gamma.normalized kappa
          (Q.preferred hregular.aleph0_le)
        (L.IsKappaHindrance →
            ∃ W : Set Gamma.normalized.DPath,
              Gamma.normalized.IsHindrance W) ∧
          (∀ (Sigma : Set (Ladder.Stage kappa)),
            ∀ (hSigma : Stationary.IsClubBelow kappa Sigma),
            ∀ (havoid : Disjoint Sigma L.phi),
            ∀ request : Ladder.Stage kappa →
              Option ↑(Gamma.normalized.source ∩ R.carrier),
              RegularPendingOnlyCanonicalProvider.HasSource915Provider
                Gamma.normalized Gamma.normalized_isNormalized
                  hGamma.normalized L Sigma
                  (DWeb.KappaLadder.canonicalLadderWithBookkeeping_isLegal
                    (Q.preferred hregular.aleph0_le) hregular hkappa
                    (by
                      intro x y hxy hy
                      exact (Gamma.normalized_isNormalized hxy).1 hy))
                  hSigma havoid R.carrier request)) :
    ExtensionClauseAt Gamma kappa := by
  apply RegularNormalization.extensionClauseAt_of_normalized kappa hkappa.le
  intro A₀ hA₀ hcard hcomplement
  obtain ⟨F, hF⟩ := hcomplement
  obtain ⟨hground, hsource915⟩ := hall A₀ hA₀ hcard F hF
  exact isLinkable_of_regularPendingOnlySource915Provider Gamma.normalized
    hregular hkappa Gamma.normalized_isNormalized hGamma.normalized hlower
      A₀ hA₀ hcard F hF hground hsource915

end RegularExtension
end CardinalInduction
end Erdos599
