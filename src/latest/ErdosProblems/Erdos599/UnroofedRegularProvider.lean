/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.UnroofedRegularRoofCandidate
import ErdosProblems.Erdos599.RegularWeakSelectedSource915Adapter

/-!
# Actual unroofed selected source-9.15 provider

This is the concrete provider assembly for the actual unroofed causal row.  The
coordinate is produced from the truthful extension and protected-halfway
lower clauses; the rest is the existing certified-history diagonal and
selected-successor bookkeeping.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace UnroofedRegularProvider

open SingularExtension SliceSpliceSource
open RegularProtectedAmbientRebuild
open SingularProtectedLowerSelection

universe u

variable {V : Type u}

private theorem essentialPart_isUnhindered_of_isUnhindered
    (Q : DWeb V) (hQ : Q.IsUnhindered) :
    Q.essentialPart.IsUnhindered := by
  rw [Q.essentialPart.isUnhindered_iff]
  intro W hW
  let U : Set Q.DPath := Q.liftEssentialPartFamily W
  have hU : Q.IsWave U := Q.isWave_liftEssentialPartFamily hW
  have hfull : Q.initialSet U = Q.source :=
    Q.isUnhindered_iff.mp hQ U hU
  have hinitial : Q.essentialPart.initialSet W = Q.source := by
    simpa only [U, Q.initialSet_liftEssentialPartFamily] using hfull
  apply Set.Subset.antisymm hW.2.1
  intro x hx
  rw [hinitial]
  rw [DWeb.essentialPart_source] at hx
  exact hx.1

private theorem zeroStageWeb_isUnhindered
    {kappa : Cardinal.{u}} (G : DWeb V)
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    {L : G.KappaLadder kappa} (hL : L.SliceGeometry) :
    (L.stageWeb ⟨0, hL.regular.ord_pos⟩).IsUnhindered := by
  let zero : Ladder.Stage kappa := ⟨0, hL.regular.ord_pos⟩
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hquotient : (G.quotient G.source).IsUnhindered :=
    SingularQuotientReentry.quotient_source_isUnhindered
      G hNoEnter hUnhindered
  have hzeroWarp : L.warpAt zero = G.trivialWave := hL.initialStage
  have hstage : L.stageWeb zero = (G.quotient G.source).essentialPart := by
    simp only [DWeb.KappaLadder.stageWeb, DWeb.stageWebOf, hzeroWarp,
      G.terminalFrontier_trivialWave]
  rw [hstage]
  exact essentialPart_isUnhindered_of_isUnhindered _ hquotient

/-- The repaired row has a selected roofed source-9.15 output at every
certified history, with no exact-frontier induction hypothesis. -/
theorem hasSelectedRoofedSource915Provider
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    (hext : ExtensionBelowFor G kappa)
    (hhalf : ProtectedHalfwayBelowFor G kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := UnroofedRegularRows.rowRule G hregular
      huncountable hNorm F hF base hbase
    let R := Q.rowSystem hregular.aleph0_le
    let L := DWeb.UnroofedMarker.ladder G kappa
      (Q.preferred hregular.aleph0_le)
    ∀ (Sigma : Set (Ladder.Stage kappa)),
      Stationary.IsClubBelow kappa Sigma →
      Disjoint Sigma L.phi →
      ∀ request : Ladder.Stage kappa →
        Option ↑(G.source ∩ R.carrier),
        RegularSplitCanonicalProvider.HasSelectedRoofedSource915Provider
          G L Sigma R.carrier ↑(G.source ∩ R.carrier) request := by
  dsimp only
  let Q := UnroofedRegularRows.rowRule G hregular
    huncountable hNorm F hF base hbase
  let R := Q.rowSystem hregular.aleph0_le
  let L := DWeb.UnroofedMarker.ladder G kappa
    (Q.preferred hregular.aleph0_le)
  let tableRequest := UnroofedRegularRows.finalRequest G Q
    hregular.aleph0_le
  intro Sigma hSigma havoid request
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hL : L.SliceGeometry :=
    DWeb.UnroofedMarker.ladder_sliceGeometry G kappa
      (Q.preferred hregular.aleph0_le) hNoEnter hregular huncountable
  have hclosed : SliceSplice.IsLimitWarpClosed G L R.carrier :=
    UnroofedRegularRows.carrier_isLimitWarpClosed
      G hregular huncountable hNorm F hF base hbase
  intro i previous hprevious B
  let U := RegularGlobalAdmissibleProvider.requiredPendingTerminals
    G L Sigma R.carrier ↑(G.source ∩ R.carrier)
      request i previous B.base
  have hUfrontier : U ⊆ L.frontier B.baseStage := by
    intro x hx
    apply B.pending_tight.1.terminalFrontier_subset
    exact RegularGlobalAdmissibleProvider.requiredPendingTerminals_subset_terminalFrontier
      hx
  have hUcarrier : U ⊆ R.carrier := by
    intro x hx
    obtain ⟨p, hp, _hrequired, hpx⟩ := hx
    exact B.base_vertices_closed
      ⟨p, hp.1, G.terminal_mem_support hpx⟩
  have hUsmall : #U < kappa :=
    RegularGlobalAdmissibleProvider.mk_requiredPendingTerminals_lt
      hregular huncountable B.base_warp
  have henumerates : RegularCardinal.EnumeratesRows
      (fun theta ↦ (Q.state hregular.aleph0_le theta).row)
      (RegularRows.CausalRegular.actualEnumeration Q
        hregular.aleph0_le) := by
    intro theta x hx
    let xs : (Q.state hregular.aleph0_le theta).row := ⟨x, hx⟩
    exact ⟨(Q.state hregular.aleph0_le theta).rowEmbedding
        hregular.aleph0_le xs,
      RegularCardinal.enumerateAlong_apply
        ((Q.state hregular.aleph0_le theta).rowEmbedding
          hregular.aleph0_le) xs⟩
  have hUrows : U ⊆ RegularCardinal.rowUnion
      (fun theta ↦ (Q.state hregular.aleph0_le theta).row) := by
    intro x hx
    exact RegularCardinal.mem_rowUnion.mpr
      (RegularRows.RowSystem.mem_carrier.mp (hUcarrier hx))
  obtain ⟨gamma, hUdiag⟩ :=
    RegularCardinal.exists_diagonalSlice_superset hregular henumerates
      hUrows hUsmall
  have hUrequest : U ⊆ tableRequest B.baseStage gamma := by
    intro x hx
    exact ⟨hUfrontier hx, hUdiag hx⟩
  have hstage : (L.stageWeb B.baseStage).IsUnhindered := by
    rcases B.baseStage_admissible with hzero | hclub
    · have hbaseZero : B.baseStage = ⟨0, hregular.ord_pos⟩ := by
        apply Subtype.ext
        exact hzero
      rw [hbaseZero]
      exact zeroStageWeb_isUnhindered G hNorm hUnhindered hL
    · apply DWeb.UnroofedMarker.ladder_stage_unhindered_of_not_mem_phi
        G kappa (Q.preferred hregular.aleph0_le) hNoEnter hNorm
      exact fun hphi ↦ Set.disjoint_left.1 havoid hclub hphi
  obtain ⟨beta, hbeta, hab, P, hP⟩ :=
    UnroofedRegularRows.exists_later_candidate_of_lower
      G hregular huncountable hNorm hext hhalf F hF base hbase
        hSigma havoid B.baseStage gamma hstage
  have hchosen : RegularWeakSplitCandidate.IsWeakSplitAnnularCandidate
      G L tableRequest B.baseStage beta gamma
        (RegularWeakSplitCandidate.chosenWeakSplitCandidate G L
          tableRequest B.baseStage beta gamma) :=
    RegularWeakSplitCandidate.chosenWeakSplitCandidate_spec_of_exists
      L tableRequest ⟨P, hP⟩
  have hregistered : RegularWeakSplitCandidate.registeredVerticesAt G L
      tableRequest B.baseStage beta gamma ⊆ R.carrier :=
    UnroofedRegularRows.registeredVerticesAt_subset_carrier
      G hregular huncountable hNorm F hF base hbase
        B.baseStage beta gamma
  exact
    RegularWeakSelectedSource915Adapter.selectedRoofedSource915Output_of_chosenWeakCoordinate
      hNorm hL B tableRequest beta gamma hbeta hab hchosen hUrequest
        hregistered hclosed

#print axioms hasSelectedRoofedSource915Provider

end UnroofedRegularProvider
end CardinalInduction
end Erdos599
