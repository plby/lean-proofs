/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularWeakSplitRowClosure
import ErdosProblems.Erdos599.RegularExactHalfwayCoordinate

/-!
# Exact-frontier regular assembly on the enhanced causal row

The enhanced row is used only for its exact-preferred half-way registration.
The completed slice is again one ordinary tight annular slice, so the original
tracked splice constructor applies without a selected/completed split.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularExtension

universe u

variable {V : Type u}

/-- The ordinary annular candidate registration is retained by the enhanced
row rule as the left summand of every triple entry. -/
theorem candidateVerticesAt_subset_weakSplitRowRule_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa)
    (delta beta gamma : Ladder.Stage kappa) :
    let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
      huncountable hNorm hlower F hF base hbase
    let L := G.canonicalLadderCore kappa
      (Q.preferred hregular.aleph0_le)
    SliceCandidate.candidateVerticesAt G L
        (RegularRows.CausalRegular.finalRequest G Q hregular.aleph0_le)
        delta beta gamma ⊆
      (Q.rowSystem hregular.aleph0_le).carrier := by
  dsimp only
  let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
    huncountable hNorm hlower F hF base hbase
  let middle := RegularRows.CausalRegular.ownerStage
    hregular.aleph0_le delta beta
  let owner := RegularRows.CausalRegular.ownerStage
    hregular.aleph0_le middle gamma
  have hmiddle : middle < owner :=
    RegularRows.CausalRegular.left_lt_ownerStage
      hregular.aleph0_le middle gamma
  have hdelta : delta < owner :=
    (RegularRows.CausalRegular.left_lt_ownerStage
      hregular.aleph0_le delta beta).trans hmiddle
  have hbeta : beta < owner :=
    (RegularRows.CausalRegular.right_lt_ownerStage
      hregular.aleph0_le delta beta).trans hmiddle
  have hgamma : gamma < owner :=
    RegularRows.CausalRegular.right_lt_ownerStage
      hregular.aleph0_le middle gamma
  let prior := fun c (_hc : c < owner) ↦ Q.state hregular.aleph0_le c
  let Lprior := RegularRows.CausalRegular.priorLadder G owner prior
  let Lfinal := G.canonicalLadderCore kappa
    (Q.preferred hregular.aleph0_le)
  have hpref (a : Ladder.Stage kappa) (ha : a < owner) :
      ∀ b, b < a →
        RegularRows.CausalRegular.preferredOfPrior owner prior b =
          Q.preferred hregular.aleph0_le b := by
    intro b hb
    simp only [RegularRows.CausalRegular.preferredOfPrior, prior,
      dif_pos (hb.trans ha), RegularRows.CausalRowRule.preferred]
  have hwarpDelta : Lprior.warpAt delta = Lfinal.warpAt delta :=
    RegularRows.LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
      G _ _ delta (hpref delta hdelta)
  have hwarpBeta : Lprior.warpAt beta = Lfinal.warpAt beta :=
    RegularRows.LadderPrefix.canonicalLadderCore_warpAt_eq_of_forall_lt
      G _ _ beta (hpref beta hbeta)
  have hfrontierDelta : Lprior.frontier delta = Lfinal.frontier delta :=
    RegularRows.LadderPrefix.canonicalLadderCore_frontier_eq_of_forall_lt
      G _ _ delta (hpref delta hdelta)
  have hfrontierBeta : Lprior.frontier beta = Lfinal.frontier beta :=
    RegularRows.LadderPrefix.canonicalLadderCore_frontier_eq_of_forall_lt
      G _ _ beta (hpref beta hbeta)
  have hrequest :
      RegularRows.CausalRegular.priorRequest G hregular.aleph0_le owner prior
          delta gamma =
        RegularRows.CausalRegular.finalRequest G Q hregular.aleph0_le
          delta gamma :=
    RegularRows.CausalRegular.priorRequest_eq_finalRequest_of_lt
      G Q hregular.aleph0_le hdelta hgamma
  have hcoordinate := SliceCandidate.candidateVerticesAt_congr_stageData
    hwarpDelta hwarpBeta hfrontierDelta hfrontierBeta hrequest
  have hentry : RegularRows.CausalRegular.weakSplitTripleEntry G
      hregular.aleph0_le owner prior
        (⟨delta, hdelta⟩ : Set.Iio owner)
        (⟨beta, hbeta⟩ : Set.Iio owner)
        (⟨gamma, hgamma⟩ : Set.Iio owner) ⊆
      (Q.rowSystem hregular.aleph0_le).carrier := by
    have hregistered : RegularRows.CausalRegular.weakSplitTripleEntry G
        hregular.aleph0_le owner prior
          (⟨delta, hdelta⟩ : Set.Iio owner)
          (⟨beta, hbeta⟩ : Set.Iio owner)
          (⟨gamma, hgamma⟩ : Set.Iio owner) ⊆
        RegularRows.tripleRegistrations owner
          (RegularRows.CausalRegular.weakSplitTripleEntry G
            hregular.aleph0_le owner prior) :=
      RegularRows.triple_entry_subset_registrations owner _ _ _ _
    have hrow : RegularRows.CausalRegular.weakSplitTripleEntry G
        hregular.aleph0_le owner prior
          (⟨delta, hdelta⟩ : Set.Iio owner)
          (⟨beta, hbeta⟩ : Set.Iio owner)
          (⟨gamma, hgamma⟩ : Set.Iio owner) ⊆
        (Q.state hregular.aleph0_le owner).row := by
      intro x hx
      have hx' := hregistered hx
      have hx'' : x ∈ RegularRows.tripleRegistrations owner
          (RegularRows.CausalRegular.weakSplitTripleEntry G
            hregular.aleph0_le owner
              (fun c _hc ↦ Q.state hregular.aleph0_le c)) := by
        simpa only [prior] using hx'
      rw [RegularRows.CausalRowRule.state_row_eq]
      exact Set.mem_union_right _ hx''
    exact hrow.trans
      ((Q.rowSystem hregular.aleph0_le).row_subset_carrier owner)
  intro x hx
  apply hentry
  apply Set.mem_union_left
  change x ∈ SliceCandidate.candidateVerticesAt G Lprior
    (RegularRows.CausalRegular.priorRequest G hregular.aleph0_le owner
      prior) delta beta gamma
  rw [hcoordinate]
  exact hx

/-- Hence every ordinary annular-table maverick is closed in the enhanced
causal carrier. -/
theorem chosenAnnularMaverickVertices_subset_weakSplitRowRule_carrier
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) :
    let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
      huncountable hNorm hlower F hF base hbase
    let L := G.canonicalLadderCore kappa
      (Q.preferred hregular.aleph0_le)
    SliceCandidate.chosenAnnularMaverickVertices G L
        (RegularRows.CausalRegular.finalRequest G Q hregular.aleph0_le) ⊆
      (Q.rowSystem hregular.aleph0_le).carrier := by
  dsimp only
  intro x hx
  obtain ⟨delta, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨beta, hx⟩ := Set.mem_iUnion.mp hx
  obtain ⟨gamma, hx⟩ := Set.mem_iUnion.mp hx
  exact candidateVerticesAt_subset_weakSplitRowRule_carrier G hregular
    huncountable hNorm hlower F hF base hbase delta beta gamma hx

/-- The formerly used all-stage coordinate interface.  It is retained only
as the input of the already-checked conditional assembly below.  At a finite
frontier a further right-tight annular slice need not exist; the sound source
provider is `HasExactAnnularCoordinateProvider`, which is restricted to the
infinite-frontier branch. -/
def HasAllStageExactAnnularCoordinateProvider
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized)
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) : Prop :=
  let lower := hlower.toUniversalCardinalInductionBelow
  let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
    huncountable hNorm lower F hF base hbase
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hregular.aleph0_le)
  let request := RegularRows.CausalRegular.finalRequest G Q
    hregular.aleph0_le
  ∀ (Sigma : Set (Ladder.Stage kappa)),
    Stationary.IsClubBelow kappa Sigma →
    ∀ delta, (L.stageWeb delta).IsUnhindered → ∀ gamma,
      ∃ beta ∈ Sigma, delta < beta ∧ ∃ T,
        SliceCandidate.IsAnnularSliceCandidate
          G L request delta beta gamma T

/-- Exact source-9.15 coordinate provider on the branch where a half-way
payload is required.  Finite frontiers are handled by terminating the splice
with the lower-induction full stage linkage, rather than by requesting a
possibly nonexistent further right-tight slice. -/
def HasExactAnnularCoordinateProvider
    (G : DWeb V) {kappa : Cardinal.{u}}
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized)
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (F : Set G.DPath) (hF : G.IsWarp F)
    (base : Set V) (hbase : #base ≤ kappa) : Prop :=
  let lower := hlower.toUniversalCardinalInductionBelow
  let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
    huncountable hNorm lower F hF base hbase
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hregular.aleph0_le)
  let request := RegularRows.CausalRegular.finalRequest G Q
    hregular.aleph0_le
  ∀ (Sigma : Set (Ladder.Stage kappa)),
    Stationary.IsClubBelow kappa Sigma →
    Disjoint Sigma L.phi →
    ∀ delta, (L.stageWeb delta).IsUnhindered →
      aleph0 ≤ #(L.frontier delta) → ∀ gamma,
        ∃ beta ∈ Sigma, delta < beta ∧ ∃ T,
          SliceCandidate.IsAnnularSliceCandidate
            G L request delta beta gamma T

/-- The exact coordinate and grounding providers close regular linkability
on the enhanced causal row. -/
theorem isLinkable_of_exactRegularCandidateProvider
    {kappa : Cardinal.{u}} (G : DWeb V)
    (hregular : kappa.IsRegular) (huncountable : aleph0 < kappa)
    (hNorm : G.IsNormalized) (hUnhindered : G.IsUnhindered)
    (hlower : UniversalExactFrontierCardinalInductionBelow V kappa)
    (A₀ : Set V) (hA₀source : A₀ ⊆ G.source)
    (hA₀card : #A₀ = kappa)
    (F : Set G.DPath)
    (hF : IsLinkageBetween G (G.source \ A₀) G.target F)
    (hground :
      let lower := hlower.toUniversalCardinalInductionBelow
      let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
        huncountable hNorm lower F hF.isWarp A₀ hA₀card.le
      let L := DWeb.KappaLadder.canonicalLadder G kappa
        (Q.preferred hregular.aleph0_le)
      L.IsKappaHindrance → ∃ W : Set G.DPath, G.IsHindrance W)
    (hprovider : HasExactAnnularCoordinateProvider G hregular huncountable
      hNorm hlower F hF.isWarp A₀ hA₀card.le) :
    IsLinkable G := by
  let lower := hlower.toUniversalCardinalInductionBelow
  let Q := RegularRows.CausalRegular.weakSplitRowRule G hregular
    huncountable hNorm lower F hF.isWarp A₀ hA₀card.le
  let R := Q.rowSystem hregular.aleph0_le
  let L := DWeb.KappaLadder.canonicalLadder G kappa
    (Q.preferred hregular.aleph0_le)
  let request := RegularRows.CausalRegular.finalRequest G Q
    hregular.aleph0_le
  have hNoEnter : G.NoEdgeEnters G.source := by
    intro x y hxy hy
    exact (hNorm hxy).1 hy
  have hL : L.IsLegal :=
    DWeb.KappaLadder.canonicalLadderWithBookkeeping_isLegal
      (Q.preferred hregular.aleph0_le) hregular huncountable hNoEnter
  obtain ⟨Sigma, hSigma, havoid⟩ :=
    exists_club_avoiding_phi_of_grounding G hUnhindered hL hground
  have hstage : ∀ delta ∈ Sigma, (L.stageWeb delta).IsUnhindered := by
    intro delta hdelta
    exact stageWeb_isUnhindered_of_mem_avoiding_of_legal
      G hNorm hL havoid hdelta
  have hcapture : ∀ delta ∈ Sigma, ∀ U : Set V,
      U ⊆ L.frontier delta ∩ R.carrier → #U < kappa →
        ∃ gamma, U ⊆ request delta gamma := by
    intro delta _ U hU hUcard
    exact RegularRows.CausalRegular.exists_finalRequest_superset
      G Q hregular delta U hU hUcard
  have hregistered :
      SliceCandidate.chosenAnnularMaverickVertices G L request ⊆
        R.carrier :=
    chosenAnnularMaverickVertices_subset_weakSplitRowRule_carrier
      G hregular huncountable hNorm lower F hF.isWarp A₀ hA₀card.le
  have hnext : ∀ delta ∈ Sigma,
      aleph0 ≤ #(L.frontier delta) → ∀ U : Set V,
        U ⊆ L.frontier delta ∩ R.carrier → #U < kappa →
          ∃ beta ∈ Sigma, delta < beta ∧ ∃ T,
            SliceCandidate.IsTrackedTightAnnularControlledSlice
              G L R.carrier delta beta U T := by
    intro delta hdelta hinfinite U hU hUcard
    apply exists_trackedControlledSlice_of_chosenTable_at
      G Sigma R.carrier request delta
        (ControlledSlices.stagesEmbedInLimit_of_legal G L hL)
          (hcapture delta hdelta)
    · intro gamma
      exact hprovider Sigma hSigma havoid delta (hstage delta hdelta)
        hinfinite gamma
    · exact hregistered
    · exact hU
    · exact hUcard
  let zero : Ladder.Stage kappa := ⟨0, hregular.ord_pos⟩
  have hzero : (L.stageWeb zero).IsUnhindered :=
    zeroStageWeb_isUnhindered G hNorm hUnhindered hL
  have hzeroCapture : ∀ U : Set V,
      U ⊆ L.frontier zero ∩ R.carrier → #U < kappa →
        ∃ gamma, U ⊆ request zero gamma := by
    intro U hU hUcard
    exact RegularRows.CausalRegular.exists_finalRequest_superset
      G Q hregular zero U hU hUcard
  have hfirst : aleph0 ≤ #(L.frontier zero) → ∀ U : Set V,
      U ⊆ L.frontier zero ∩ R.carrier → #U < kappa →
        ∃ beta ∈ Sigma, zero < beta ∧ ∃ T,
          SliceCandidate.IsTrackedTightAnnularControlledSlice
            G L R.carrier zero beta U T :=
    fun hinfinite U hU hUcard ↦ by
      apply exists_trackedControlledSlice_of_chosenTable_at
        G Sigma R.carrier request zero
          (ControlledSlices.stagesEmbedInLimit_of_legal G L hL)
            hzeroCapture
      · intro gamma
        exact hprovider Sigma hSigma havoid zero hzero hinfinite gamma
      · exact hregistered
      · exact hU
      · exact hUcard
  have hroof : R.carrier ⊆ L.limitRoof :=
    RegularWeakSplitRowClosure.carrier_subset_limitRoof G hregular
      huncountable hNorm lower F hF.isWarp A₀ hA₀card.le
  have hclosed : SliceSplice.IsLimitWarpClosed G L R.carrier :=
    RegularWeakSplitRowClosure.carrier_isLimitWarpClosed G hregular
      huncountable hNorm lower F hF.isWarp A₀ hA₀card.le
  have hsourceCard : #(G.source ∩ R.carrier : Set V) ≤ kappa :=
    mk_source_inter_rowCarrier_le G R hregular.aleph0_le
  have hA₀carrier : A₀ ⊆ R.carrier :=
    RegularRows.CausalRegular.base_subset_weakSplitRowRule_carrier G
      hregular huncountable hNorm lower F hF.isWarp A₀ hA₀card.le
  have hsourceInfinite : aleph0 ≤ #(G.source ∩ R.carrier : Set V) := by
    calc
      aleph0 ≤ kappa := huncountable.le
      _ = #A₀ := hA₀card.symm
      _ ≤ #(G.source ∩ R.carrier : Set V) :=
        Cardinal.mk_subtype_mono (fun _ hx ↦
          ⟨hA₀source hx, hA₀carrier hx⟩)
  obtain ⟨P, hP, hPclosed⟩ :=
    SliceSpliceConstructor.exists_internal_linkage_of_infiniteTrackedControlledSlices
      hNorm hUnhindered hL hSigma havoid hroof hclosed hsourceCard
        hsourceInfinite hnext hfirst
  have hregister : ∀ i,
      G.vertexSet (pathsMeeting G F (R.row i)) ⊆ R.carrier :=
    RegularRows.CausalRegular.weakSplitRowCarrier_registersOldLinkage G
      hregular huncountable hNorm lower F hF.isWarp A₀ hA₀card.le
  exact isLinkable_of_internal_linkage_on_rowCarrier
    G A₀ R F P hA₀carrier hP hPclosed hF hregister

/-- Normalized exact-frontier regular extension step from only the remaining
grounding and one-coordinate source-9.15 theorems. -/
theorem regularExtensionClauseStep_of_exactCandidateProviders
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
            Gamma.normalized.IsHindrance W)
    (hcoordinate :
      ∀ (A₀ : Set V), A₀ ⊆ Gamma.normalized.source →
      ∀ (hcard : #A₀ = kappa),
      ∀ (F : Set Gamma.normalized.DPath),
      ∀ (hF : IsLinkageBetween Gamma.normalized
          (Gamma.normalized.source \ A₀) Gamma.normalized.target F),
        HasExactAnnularCoordinateProvider Gamma.normalized hregular hkappa
          Gamma.normalized_isNormalized hlower F hF.isWarp A₀ hcard.le) :
    ExtensionClauseAt Gamma kappa := by
  apply RegularNormalization.extensionClauseAt_of_normalized kappa hkappa.le
  intro A₀ hA₀ hcard hcomplement
  obtain ⟨F, hF⟩ := hcomplement
  exact isLinkable_of_exactRegularCandidateProvider Gamma.normalized
    hregular hkappa Gamma.normalized_isNormalized hGamma.normalized hlower
      A₀ hA₀ hcard F hF (hground A₀ hA₀ hcard F hF)
        (hcoordinate A₀ hA₀ hcard F hF)

end RegularExtension
end CardinalInduction
end Erdos599
