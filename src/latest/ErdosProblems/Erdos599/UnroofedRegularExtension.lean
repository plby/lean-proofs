/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedRegularProvider
import ErdosProblems.Erdos599.ProtectedCardinalAssembly

/-!
# The actual protected regular extension engine

The unroofed ladder supplies its own proved avoiding club. Actual causal
rows, protected candidates, successor transactions and proper history limits
produce the internal linkage. Untouched complementary paths finish the
extension. There is no grounding or candidate-existence premise left here.
Only the genuine smaller-cardinal induction clauses are used.
-/

noncomputable section

namespace Erdos599.CardinalInduction.UnroofedRegularExtension

open Set Cardinal
open RegularProtectedAmbientRebuild SingularProtectedLowerSelection

universe u

variable {V : Type u}

theorem isLinkable_of_protectedLower (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hext : ExtensionBelowFor G kappa) (hhalf : ProtectedHalfwayBelowFor G kappa)
    (A₀ : Set V) (hA₀card : #A₀ = kappa) (F : Set G.DPath)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F) : IsLinkable G := by
  let Q := UnroofedRegularRows.rowRule G hregular huncountable hNorm F hF.isWarp A₀ hA₀card.le
  let R := Q.rowSystem hregular.aleph0_le
  let L := DWeb.UnroofedMarker.ladder G kappa (Q.preferred hregular.aleph0_le)
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hL : L.SliceGeometry := DWeb.UnroofedMarker.ladder_sliceGeometry G kappa
    (Q.preferred hregular.aleph0_le) hNoEnter hregular huncountable
  obtain ⟨Sigma, hSigma, havoid, _hstage⟩ :=
    DWeb.UnroofedMarker.exists_club_unhindered_stages G kappa
      (Q.preferred hregular.aleph0_le) hNoEnter hregular huncountable hNorm hG
  have hsourceCard : #↑(G.source ∩ R.carrier) ≤ kappa :=
    (Cardinal.mk_subtype_mono Set.inter_subset_right).trans
      (R.mk_carrier_le hregular.aleph0_le)
  let zero : Ladder.Stage kappa := ⟨0, hregular.ord_pos⟩
  have hzero : ∀ j : Ladder.Stage kappa, ¬ j < zero := by
    intro j hj
    exact (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ j.1)) hj
  have hsource915 := UnroofedRegularProvider.hasSelectedRoofedSource915Provider
    G hregular huncountable hNorm hG hext hhalf F hF.isWarp
      A₀ hA₀card.le Sigma hSigma havoid
  obtain ⟨P, hP, hPclosed⟩ :=
    RegularSplitCanonicalRecursion.exists_internal_linkage_of_canonicalStageProvider
      hNorm hsourceCard zero hzero (by
        intro request
        exact (hsource915 request).hasCanonicalStageProvider
          hNorm hG hL hSigma havoid request)
  have hA₀carrier : A₀ ⊆ R.carrier :=
    UnroofedRegularRows.base_subset_carrier G hregular huncountable hNorm F hF.isWarp A₀ hA₀card.le
  have hregister : ∀ i,
      G.vertexSet (RegularExtension.pathsMeeting G F (R.row i)) ⊆ R.carrier :=
    UnroofedRegularRows.carrier_registersOldLinkage
      G hregular huncountable hNorm F hF.isWarp A₀ hA₀card.le
  apply RegularExtension.isLinkable_of_internal_linkage_on_closedCarrier
    G A₀ R.carrier F P hA₀carrier hP hPclosed hF
  intro p hp hpMeet
  exact RegularExtension.support_subset_carrier_of_rowRegistrations G R F hregister hp hpMeet

theorem extensionClauseAt_of_protectedLower (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (hG : G.IsUnhindered)
    (hext : ExtensionBelowFor G kappa) (hhalf : ProtectedHalfwayBelowFor G kappa) :
    ExtensionClauseAt G kappa := by
  intro A₀ _hA₀source hA₀card hcomplement
  obtain ⟨F, hF⟩ := hcomplement
  exact isLinkable_of_protectedLower G hregular huncountable hNorm hG hext hhalf A₀ hA₀card F hF

/-- The regular engine is supplied outright, uniformly in the ambient base. -/
theorem regularEngineFor (Base : DWeb V) : ProtectedCardinalAssembly.RegularEngineFor Base := by
  intro kappa huncountable hregular G _hGBase hNorm hG hext hhalf
  exact extensionClauseAt_of_protectedLower G hregular huncountable hNorm hG hext hhalf

#print axioms isLinkable_of_protectedLower
#print axioms extensionClauseAt_of_protectedLower
#print axioms regularEngineFor

end Erdos599.CardinalInduction.UnroofedRegularExtension
