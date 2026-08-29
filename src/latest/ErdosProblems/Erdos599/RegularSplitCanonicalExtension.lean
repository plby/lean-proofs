/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularExtension
import ErdosProblems.Erdos599.RegularSplitCanonicalProvider
import ErdosProblems.Erdos599.RegularWeakSplitRows
import ErdosProblems.Erdos599.SplitHindranceGrounding

/-!
# Regular extension from persistent/movable canonical stages

This is the final scheduling and row-carrier assembly for the sound split
successor.  Completed target tracks may cross later frontiers; only the
pending clean track is required to be tight.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularExtension

open DirectedPath

universe u

variable {V : Type u}

/-- Club avoidance from the sound split grounding implication.  This is the
split-legal analogue of the legacy club-avoidance reduction; it does not
discard the fresh same-stage obstruction branch. -/
theorem exists_club_avoiding_phi_of_splitGrounding
    {G : DWeb V} {kappa : Cardinal.{u}} {L : G.KappaLadder kappa}
    (hG : G.IsUnhindered) (hlegal : L.IsSplitLegal)
    (hground : L.IsSplitKappaHindrance →
      ∃ W : Set G.DPath, G.IsHindrance W) :
    ∃ Sigma : Set (Ladder.Stage kappa),
      Stationary.IsClubBelow kappa Sigma ∧ Disjoint Sigma L.phi := by
  have hnonstationary :
      ¬ Stationary.IsStationaryBelow kappa L.phi := by
    intro hstationary
    obtain ⟨W, hW⟩ := hground ⟨hlegal, hstationary⟩
    exact hG ⟨W, hW⟩
  obtain ⟨Sigma, hSigma, hdisjoint⟩ :=
    not_isStationary_iff.mp hnonstationary
  exact ⟨Sigma, hSigma, hdisjoint.symm⟩

/-- Final linkage assembly using the enhanced causal row which registers
the target carrier and clean mavericks of every weak split coordinate. -/
theorem isLinkable_of_regularWeakSplitSource915Provider
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hkappa : kappa.IsRegular) (hkappaUncountable : aleph0 < kappa)
    (hG : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (A₀ : Set V) (hA₀source : A₀ ⊆ G.source)
    (hA₀card : #A₀ = kappa)
    (F : Set G.DPath)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hground :
      let Q := RegularRows.CausalRegular.weakSplitRowRule G hkappa
        hkappaUncountable hG hlower F hF.isWarp A₀ hA₀card.le
      let L := DWeb.KappaLadder.canonicalLadder G kappa
        (Q.preferred hkappa.aleph0_le)
      L.IsSplitKappaHindrance → ∃ W : Set G.DPath, G.IsHindrance W)
    (hsource915 :
      let Q := RegularRows.CausalRegular.weakSplitRowRule G hkappa
        hkappaUncountable hG hlower F hF.isWarp A₀ hA₀card.le
      let R := Q.rowSystem hkappa.aleph0_le
      let L := DWeb.KappaLadder.canonicalLadder G kappa
        (Q.preferred hkappa.aleph0_le)
      ∀ (Sigma : Set (Ladder.Stage kappa)),
        Stationary.IsClubBelow kappa Sigma →
        Disjoint Sigma L.phi →
        ∀ request : Ladder.Stage kappa →
          Option ↑(G.source ∩ R.carrier),
          RegularSplitCanonicalProvider.HasSelectedRoofedSource915Provider
            G L Sigma R.carrier (G.source ∩ R.carrier) request) :
    IsLinkable G := by
  let Q := RegularRows.CausalRegular.weakSplitRowRule G hkappa
    hkappaUncountable hG hlower F hF.isWarp A₀ hA₀card.le
  let R := Q.rowSystem hkappa.aleph0_le
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hkappa.aleph0_le)
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hG hxy).1 hy
  have hL : L.IsSplitLegal :=
    DWeb.KappaLadder.canonicalLadder_isSplitLegal
      (Q.preferred hkappa.aleph0_le) hkappa hkappaUncountable hNoEnter
  obtain ⟨Sigma, hSigma, havoid⟩ :=
    exists_club_avoiding_phi_of_splitGrounding hUnhindered hL hground
  have hsourceCard : #↑(G.source ∩ R.carrier) ≤ kappa :=
    (Cardinal.mk_subtype_mono Set.inter_subset_right).trans
      (R.mk_carrier_le hkappa.aleph0_le)
  let zero : Ladder.Stage kappa := ⟨0, hkappa.ord_pos⟩
  have hzero : ∀ j : Ladder.Stage kappa, ¬ j < zero := by
    intro j hj
    exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1)) hj
  obtain ⟨P, hP, hPclosed⟩ :=
    RegularSplitCanonicalRecursion.exists_internal_linkage_of_canonicalStageProvider
      hG hsourceCard zero hzero (by
        intro request
        exact (hsource915 Sigma hSigma havoid request).hasCanonicalStageProvider
          hG hUnhindered hL hSigma havoid request)
  have hA₀carrier : A₀ ⊆ R.carrier :=
    RegularRows.CausalRegular.base_subset_weakSplitRowRule_carrier
      G hkappa hkappaUncountable hG hlower F hF.isWarp A₀ hA₀card.le
  have hregister : ∀ i,
      G.vertexSet (pathsMeeting G F (R.row i)) ⊆ R.carrier :=
    RegularRows.CausalRegular.weakSplitRowCarrier_registersOldLinkage
      G hkappa hkappaUncountable hG hlower F hF.isWarp A₀ hA₀card.le
  apply isLinkable_of_internal_linkage_on_closedCarrier
    G A₀ R.carrier F P hA₀carrier hP hPclosed hF
  intro p hp hpMeet
  exact support_subset_carrier_of_rowRegistrations G R F hregister hp hpMeet

/-- Exact extension-clause boundary for the enhanced weak-split causal
table.  Once its roofed-annular source-9.15 selector and the ladder
grounding implication are supplied, no further regular-case assumptions
remain. -/
theorem regularExtensionClauseStep_of_weakSplitSource915Provider
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
        (L.IsSplitKappaHindrance →
            ∃ W : Set Gamma.normalized.DPath,
              Gamma.normalized.IsHindrance W) ∧
          (∀ (Sigma : Set (Ladder.Stage kappa)),
            Stationary.IsClubBelow kappa Sigma →
            Disjoint Sigma L.phi →
            ∀ request : Ladder.Stage kappa →
              Option ↑(Gamma.normalized.source ∩ R.carrier),
              RegularSplitCanonicalProvider.HasSelectedRoofedSource915Provider
                Gamma.normalized L Sigma R.carrier
                  (Gamma.normalized.source ∩ R.carrier) request)) :
    ExtensionClauseAt Gamma kappa := by
  apply RegularNormalization.extensionClauseAt_of_normalized kappa hkappa.le
  intro A₀ hA₀ hcard hcomplement
  obtain ⟨F, hF⟩ := hcomplement
  have hproviders := hall A₀ hA₀ hcard F hF
  exact isLinkable_of_regularWeakSplitSource915Provider Gamma.normalized
    hregular hkappa Gamma.normalized_isNormalized hGamma.normalized hlower
      A₀ hA₀ hcard F hF hproviders.1 hproviders.2

end RegularExtension
end CardinalInduction
end Erdos599
