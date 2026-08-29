/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularLocalizedProtectedProviderAssembly

/-!
# Regular extension from truthful protected lower induction

The coordinate table, certified-history provider, and canonical recursion
are concrete in this module.  The only remaining interface is the sound
split-grounding implication for the particular canonical ladder generated
by each complementary linkage.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularLocalizedProtectedExtension

open DirectedPath
open RegularProtectedAmbientRebuild
open SingularProtectedLowerSelection

universe u

variable {V : Type u}

/-- Club avoidance from the sound split obstruction, stated locally so the
repaired assembly has no dependency on a legacy regular compositor. -/
private theorem exists_club_avoiding_phi_of_splitGrounding
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

/-- The exact remaining grounding interface for the repaired protected row.
It quantifies only the canonical ladders actually generated in the extension
clause, and uses the sound split obstruction. -/
def HasCanonicalSplitGrounding
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) : Prop :=
  ∀ (A₀ : Set V), ∀ (hA₀card : #A₀ = kappa),
    ∀ (F : Set G.DPath),
      ∀ (hF : IsLinkageBetween G (G.source \ A₀) G.target F),
      let Q := RegularLocalizedProtectedRows.rowRule G hregular
        huncountable hNorm F hF.isWarp A₀ hA₀card.le
      let L := DWeb.KappaLadder.canonicalLadder G kappa
        (Q.preferred hregular.aleph0_le)
      L.IsSplitKappaHindrance → ∃ W : Set G.DPath, G.IsHindrance W

/-- The repaired protected row yields a full linkage once its canonical
split ladder has the genuine grounding implication. -/
theorem isLinkable_of_protectedLower
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    (hext : ExtensionBelowFor G kappa)
    (hhalf : ProtectedHalfwayBelowFor G kappa)
    (A₀ : Set V) (hA₀card : #A₀ = kappa)
    (F : Set G.DPath)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hground :
      let Q := RegularLocalizedProtectedRows.rowRule G hregular
        huncountable hNorm F hF.isWarp A₀ hA₀card.le
      let L := DWeb.KappaLadder.canonicalLadder G kappa
        (Q.preferred hregular.aleph0_le)
      L.IsSplitKappaHindrance → ∃ W : Set G.DPath, G.IsHindrance W) :
    IsLinkable G := by
  let Q := RegularLocalizedProtectedRows.rowRule G hregular
    huncountable hNorm F hF.isWarp A₀ hA₀card.le
  let R := Q.rowSystem hregular.aleph0_le
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hregular.aleph0_le)
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hL : L.IsSplitLegal :=
    DWeb.KappaLadder.canonicalLadder_isSplitLegal
      (Q.preferred hregular.aleph0_le) hregular huncountable hNoEnter
  obtain ⟨Sigma, hSigma, havoid⟩ :=
    exists_club_avoiding_phi_of_splitGrounding hUnhindered hL hground
  have hsourceCard : #↑(G.source ∩ R.carrier) ≤ kappa :=
    (Cardinal.mk_subtype_mono Set.inter_subset_right).trans
      (R.mk_carrier_le hregular.aleph0_le)
  let zero : Ladder.Stage kappa := ⟨0, hregular.ord_pos⟩
  have hzero : ∀ j : Ladder.Stage kappa, ¬ j < zero := by
    intro j hj
    exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1)) hj
  have hsource915 :=
    RegularLocalizedProtectedProviderAssembly.hasSelectedRoofedSource915Provider
      G hregular huncountable hNorm hUnhindered hext hhalf F hF.isWarp
        A₀ hA₀card.le Sigma hSigma havoid
  obtain ⟨P, hP, hPclosed⟩ :=
    RegularSplitCanonicalRecursion.exists_internal_linkage_of_canonicalStageProvider
      hNorm hsourceCard zero hzero (by
        intro request
        exact (hsource915 request).hasCanonicalStageProvider
          hNorm hUnhindered hL hSigma havoid request)
  have hA₀carrier : A₀ ⊆ R.carrier :=
    RegularLocalizedProtectedRowClosure.base_subset_carrier G hregular
      huncountable hNorm F hF.isWarp A₀ hA₀card.le
  have hregister : ∀ i,
      G.vertexSet (RegularExtension.pathsMeeting G F (R.row i)) ⊆
        R.carrier :=
    RegularLocalizedProtectedRowClosure.carrier_registersOldLinkage
      G hregular huncountable hNorm F hF.isWarp A₀ hA₀card.le
  apply RegularExtension.isLinkable_of_internal_linkage_on_closedCarrier
    G A₀ R.carrier F P hA₀carrier hP hPclosed hF
  intro p hp hpMeet
  exact RegularExtension.support_subset_carrier_of_rowRegistrations
    G R F hregister hp hpMeet

/-- Exact extension-clause compositor.  All regular geometry and recursion
are discharged; only canonical split grounding remains named. -/
theorem extensionClauseAt_of_protectedLower_and_splitGrounding
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    (hext : ExtensionBelowFor G kappa)
    (hhalf : ProtectedHalfwayBelowFor G kappa)
    (hground : HasCanonicalSplitGrounding G hregular huncountable hNorm) :
    ExtensionClauseAt G kappa := by
  intro A₀ _hA₀source hA₀card hcomplement
  obtain ⟨F, hF⟩ := hcomplement
  exact isLinkable_of_protectedLower G hregular huncountable hNorm
    hUnhindered hext hhalf A₀ hA₀card F hF
      (hground A₀ hA₀card F hF)

#print axioms isLinkable_of_protectedLower
#print axioms extensionClauseAt_of_protectedLower_and_splitGrounding

end RegularLocalizedProtectedExtension
end CardinalInduction
end Erdos599
