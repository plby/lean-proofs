/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularWeakSelectedCoordinateProvider
import ErdosProblems.Erdos599.RegularWeakSelectedSource915Adapter
import ErdosProblems.Erdos599.RegularWeakSplitRowClosure

/-!
# Causal assembly of the selected weak source-9.15 provider

This file discharges the bookkeeping around the genuine geometric step.
For every certified history, the required pending-terminal set is small and
belongs to the current ladder frontier and causal carrier.  Assertion 9.13
therefore places it in one diagonal table request.  A supplied weak-candidate
coordinate at that request is then the canonical chosen coordinate, whose
registered vertices and limit-warp closure feed the selected successor
adapter.

The only hypothesis left by the main theorem is the mathematical content of
the fixed-stage weak split construction: existence of a later club coordinate
carrying a weak annular candidate.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

namespace RegularWeakSelectedProviderAssembly

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- A weak split coordinate for each diagonal request on every certified
history is enough to construct the full selected source-9.15 provider for the
enhanced causal row rule. -/
theorem hasSelectedRoofedSource915Provider_of_coordinateProvider
    {kappa : Cardinal.{u}} (G : DWeb V)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
      huncountable hNorm hlower F hF base hbase
    let R := Q.rowSystem hregular.aleph0_le
    let L := DWeb.KappaLadder.canonicalLadder G kappa
      (Q.preferred hregular.aleph0_le)
    ∀ (Sigma : Set (Ladder.Stage kappa)),
      Stationary.IsClubBelow kappa Sigma →
      Disjoint Sigma L.phi →
      ∀ request : Ladder.Stage kappa →
        Option ↑(G.source ∩ R.carrier),
      (∀ (i : Ladder.Stage kappa)
          (previous : ∀ j : Ladder.Stage kappa, j < i →
            RegularCompletedPendingSplice.RecursivePayload
              G L Sigma (R.carrier) ↑(G.source ∩ R.carrier))
          (hprevious : ∀ j (hji : j < i),
            RegularCompletedPendingSplice.IsValidRecursiveStage request j
              (fun l hlj ↦ previous l (lt_trans hlj hji))
              (previous j hji))
          (B : RegularSplitCanonicalHistoryBase.HistoryBase
            G L Sigma R.carrier ↑(G.source ∩ R.carrier)
              request i previous)
          (gamma : Ladder.Stage kappa),
        RegularGlobalAdmissibleProvider.requiredPendingTerminals
            G L Sigma R.carrier ↑(G.source ∩ R.carrier)
              request i previous B.base ⊆
            RegularRows.CausalRegular.finalRequest G Q
              hregular.aleph0_le B.baseStage gamma →
        ∃ beta : Ladder.Stage kappa,
          beta ∈ Sigma ∧ B.baseStage < beta ∧
          ∃ P : RegularWeakSplitCandidate.WeakSplitFamilies G,
            RegularWeakSplitCandidate.IsWeakSplitAnnularCandidate G L
              (RegularRows.CausalRegular.finalRequest G Q
                hregular.aleph0_le) B.baseStage beta gamma P) →
      RegularSplitCanonicalProvider.HasSelectedRoofedSource915Provider
        G L Sigma R.carrier ↑(G.source ∩ R.carrier) request := by
  dsimp only
  let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
    huncountable hNorm hlower F hF base hbase
  let R := Q.rowSystem hregular.aleph0_le
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hregular.aleph0_le)
  intro Sigma _hSigma _havoid request hcoordinate
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hL : L.IsSplitLegal :=
    DWeb.KappaLadder.canonicalLadder_isSplitLegal
      (Q.preferred hregular.aleph0_le) hregular huncountable hNoEnter
  have hclosed : SliceSplice.IsLimitWarpClosed G L R.carrier :=
    RegularWeakSplitRowClosure.carrier_isLimitWarpClosed G hregular
      huncountable hNorm hlower F hF base hbase
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
  have hUboth : U ⊆ L.frontier B.baseStage ∩ R.carrier :=
    fun x hx ↦ ⟨hUfrontier hx, hUcarrier hx⟩
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
  have hUrequest : U ⊆ RegularRows.CausalRegular.finalRequest G Q
      hregular.aleph0_le B.baseStage gamma := by
    intro x hx
    exact ⟨hUfrontier hx, hUdiag hx⟩
  obtain ⟨beta, hbeta, hab, P, hP⟩ :=
    hcoordinate i previous hprevious B gamma hUrequest
  have hchosen : RegularWeakSplitCandidate.IsWeakSplitAnnularCandidate
      G L (RegularRows.CausalRegular.finalRequest G Q
        hregular.aleph0_le) B.baseStage beta gamma
        (RegularWeakSplitCandidate.chosenWeakSplitCandidate G L
          (RegularRows.CausalRegular.finalRequest G Q
            hregular.aleph0_le) B.baseStage beta gamma) :=
    RegularWeakSplitCandidate.chosenWeakSplitCandidate_spec_of_exists
      L (RegularRows.CausalRegular.finalRequest G Q hregular.aleph0_le)
        ⟨P, hP⟩
  have hregistered : RegularWeakSplitCandidate.registeredVerticesAt G L
      (RegularRows.CausalRegular.finalRequest G Q hregular.aleph0_le)
        B.baseStage beta gamma ⊆ R.carrier :=
    RegularRows.CausalRegular.registeredVerticesAt_subset_weakSplitRowRule_carrier
      G hregular huncountable hNorm hlower F hF base hbase
        B.baseStage beta gamma
  exact
    RegularWeakSelectedSource915Adapter.selectedRoofedSource915Output_of_chosenWeakCoordinate
        hNorm hL B (RegularRows.CausalRegular.finalRequest G Q
          hregular.aleph0_le) beta gamma hbeta hab hchosen hUrequest
            hregistered hclosed

end RegularWeakSelectedProviderAssembly
end CardinalInduction
end Erdos599
