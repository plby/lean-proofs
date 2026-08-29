/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularCanonicalHistoryLimit
import ErdosProblems.Erdos599.RegularCanonicalSuccessor

/-!
# The exact regular source-9.15 successor

This module combines a canonical history base with the ordinary tracked
slice table.  The extra whole-row tight/roof hypotheses are provenance
invariants of the source-specific recursion; they are stronger than the
public completed/pending payload.  Under those invariants the full tracked
slice itself is the comparison warp, so no independent global comparison
choice or arbitrary history-dependent payload is needed.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularCanonicalSource915

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- The exact raw 9.15 input together with the whole-row invariant proved
by its tracked-slice provenance.  The result fields are indexed by the
literal compatibility proof stored in `input`, so packaging a canonical
stage requires no transport through an arbitrary payload. -/
structure StrongInput
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z A : Set V) (request : Ladder.Stage kappa → Option A)
    (i : Ladder.Stage kappa)
    (previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A) where
  input : RegularCanonicalSuccessor.Input
    G L Sigma Z A request i previous
  result_tight : TightLinkageBetween G A (L.frontier input.stageIndex)
    (RegularCompletedPendingSplice.freezeCompletedStar G input.base
      (input.slice.target ∪ input.slice.clean) input.compatible)
  result_below_roof : G.vertexSet
    (RegularCompletedPendingSplice.freezeCompletedStar G input.base
      (input.slice.target ∪ input.slice.clean) input.compatible) ⊆
    G.roof (L.frontier input.stageIndex)

namespace StrongInput

/-- Package the exact strong input as the canonical successor consumed by
the recursive provider. -/
def canonicalStage
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (S : StrongInput G L Sigma Z A request i previous)
    (hNorm : G.IsNormalized) (hL : L.IsLegal) (hA : A ⊆ G.source) :
    RegularCanonicalAdmissibleProvider.CanonicalStage
      G L Sigma Z A request i previous :=
  S.input.canonicalStage hNorm hL hA S.result_tight S.result_below_roof

end StrongInput

/-- One unconditional source-9.15 input over a roofed canonical history
base.  The club table is used at ordinary bases and the distinguished
zero-to-club table at the initial base. -/
theorem exists_strongInput
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized)
    {L : G.KappaLadder kappa} (hL : L.IsLegal)
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    (hA : A ⊆ G.source)
    {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (hclosed : SliceSplice.IsLimitWarpClosed G L Z)
    (hslices : SliceCandidate.HasTrackedTightAnnularControlledSlices
      G L Sigma Z)
    (hfirst : ∀ U : Set V,
      U ⊆ L.frontier ⟨0, hL.regular.ord_pos⟩ ∩ Z → #U < kappa →
        ∃ beta ∈ Sigma, ⟨0, hL.regular.ord_pos⟩ < beta ∧
          ∃ T, SliceCandidate.IsTrackedTightAnnularControlledSlice
            G L Z ⟨0, hL.regular.ord_pos⟩ beta U T)
    (B : RegularCanonicalHistoryLimit.HistoryBase
      G L Sigma Z A request i previous) :
    Nonempty (StrongInput
      G L Sigma Z A request i previous) := by
  let U := RegularGlobalAdmissibleProvider.requiredPendingTerminals
    G L Sigma Z A request i previous B.base
  have hUfrontier : U ⊆ L.frontier B.baseStage := by
    exact RegularGlobalAdmissibleProvider.requiredPendingTerminals_subset_terminalFrontier.trans
      B.pending_tight.1.terminalFrontier_subset
  have hUZ : U ⊆ Z := by
    rintro x ⟨p, hp, _hrequired, hpx⟩
    exact B.base_vertices_closed ⟨p, hp.1, G.terminal_mem_support hpx⟩
  have hU : U ⊆ L.frontier B.baseStage ∩ Z :=
    fun _ hx ↦ ⟨hUfrontier hx, hUZ hx⟩
  have hUsmall : #U < kappa :=
    RegularGlobalAdmissibleProvider.mk_requiredPendingTerminals_lt
      hL.regular hL.uncountable B.base_warp
  have hex : ∃ beta ∈ Sigma, B.baseStage < beta ∧
      ∃ T, SliceCandidate.IsTrackedTightAnnularControlledSlice
        G L Z B.baseStage beta U T := by
    rcases B.baseStage_admissible with hzero | hclub
    · have hbaseZero : B.baseStage = ⟨0, hL.regular.ord_pos⟩ := by
        apply Subtype.ext
        exact hzero
      have hUzero : U ⊆ L.frontier ⟨0, hL.regular.ord_pos⟩ ∩ Z := by
        simpa only [hbaseZero] using hU
      obtain ⟨beta, hbeta, hzeroBeta, T, hT⟩ :=
        hfirst U hUzero hUsmall
      exact ⟨beta, hbeta, hbaseZero ▸ hzeroBeta, T,
        hbaseZero ▸ hT⟩
    · exact hslices B.baseStage hclub U hU hUsmall
  obtain ⟨beta, hbeta, hbaseBeta, T, hT⟩ := hex
  have hindex : ∀ j (hji : j < i),
      (previous j hji).stageIndex < beta := by
    intro j hji
    exact (B.index_le_base j hji).trans_lt hbaseBeta
  have hshadow : ∀ f ∈ completedPart G B.base,
      ∃ t ∈ T,
        t ∉ initialRestriction G T
          (G.terminalFrontier (pendingPart G B.base)) ∧
        f.support \ G.strictRoof (L.frontier B.baseStage) ⊆ t.support :=
    RegularCanonicalSuccessor.completedShadow_of_roofedTightBase
      hL B.base_tight B.base_below_roof hT
  let S := RegularCanonicalSuccessor.inputOfProtectedTrackedSlice
    hL B.base_warp B.base_finite B.base_initial B.base_vertices_closed
      B.base_extends B.base_freezes B.pending_tight B.pending_below_roof
      hclosed B.old_pending_status hbeta hbaseBeta hindex hT
      hT.1.1.1.1.1.isWarp (fun _ hp ↦ hp.1) hshadow
  have hleft : G.terminalFrontier (pendingPart G B.base) ⊆
      L.frontier B.baseStage :=
    B.pending_tight.1.terminalFrontier_subset
  have hUleft : U ⊆ G.terminalFrontier (pendingPart G B.base) :=
    RegularGlobalAdmissibleProvider.requiredPendingTerminals_subset_terminalFrontier
  have hslice : S.slice =
      RegularCanonicalSuccessor.cleanTargetSliceOfTracked
        hT hleft hUleft := by
    rfl
  obtain ⟨hresultTight, hresultRoof⟩ :=
    RegularCanonicalSuccessor.freezeCompletedStar_roofedTight_of_cleanTarget
      (G := G) (L := L) (Z := Z) (A := A)
      (U := U) (alpha := B.baseStage) (beta := beta)
      (base := B.base) (T := T)
      hNorm hL hA
      hbaseBeta B.base_tight B.base_below_roof hT hleft hUleft
      S.slice hslice S.compatible
  exact ⟨⟨S, hresultTight, hresultRoof⟩⟩

/-- Forget only the whole-row conclusion, retaining the raw non-circular
successor geometry. -/
theorem exists_input
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized)
    {L : G.KappaLadder kappa} (hL : L.IsLegal)
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    (hA : A ⊆ G.source)
    {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (hclosed : SliceSplice.IsLimitWarpClosed G L Z)
    (hslices : SliceCandidate.HasTrackedTightAnnularControlledSlices
      G L Sigma Z)
    (hfirst : ∀ U : Set V,
      U ⊆ L.frontier ⟨0, hL.regular.ord_pos⟩ ∩ Z → #U < kappa →
        ∃ beta ∈ Sigma, ⟨0, hL.regular.ord_pos⟩ < beta ∧
          ∃ T, SliceCandidate.IsTrackedTightAnnularControlledSlice
            G L Z ⟨0, hL.regular.ord_pos⟩ beta U T)
    (B : RegularCanonicalHistoryLimit.HistoryBase
      G L Sigma Z A request i previous) :
    Nonempty (RegularCanonicalSuccessor.Input
      G L Sigma Z A request i previous) := by
  obtain ⟨S⟩ := exists_strongInput hNorm hL hA hclosed hslices hfirst B
  exact ⟨S.input⟩

/-- The actual source-9.15 successor over a canonical history base.  The
comparison is the full tracked slice, and the result invariant comes from
that same slice rather than from an arbitrary payload callback. -/
theorem exists_canonicalStage
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized)
    {L : G.KappaLadder kappa} (hL : L.IsLegal)
    {Sigma : Set (Ladder.Stage kappa)} {Z A : Set V}
    (hA : A ⊆ G.source)
    {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (hclosed : SliceSplice.IsLimitWarpClosed G L Z)
    (hslices : SliceCandidate.HasTrackedTightAnnularControlledSlices
      G L Sigma Z)
    (hfirst : ∀ U : Set V,
      U ⊆ L.frontier ⟨0, hL.regular.ord_pos⟩ ∩ Z → #U < kappa →
        ∃ beta ∈ Sigma, ⟨0, hL.regular.ord_pos⟩ < beta ∧
          ∃ T, SliceCandidate.IsTrackedTightAnnularControlledSlice
            G L Z ⟨0, hL.regular.ord_pos⟩ beta U T)
    (B : RegularCanonicalHistoryLimit.HistoryBase
      G L Sigma Z A request i previous) :
    Nonempty (RegularCanonicalAdmissibleProvider.CanonicalStage
      G L Sigma Z A request i previous) := by
  obtain ⟨S⟩ := exists_strongInput hNorm hL hA hclosed hslices hfirst B
  exact ⟨S.canonicalStage hNorm hL hA⟩

end RegularCanonicalSource915
end CardinalInduction
end Erdos599
