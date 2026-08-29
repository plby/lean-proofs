/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularPersistentCanonicalSuccessor
import ErdosProblems.Erdos599.RegularSplitTargetedComparison

/-!
# Producer adapter for the persistent/movable regular successor

The weak comparison supplied by source Assertion 9.15 is not required to be
right-tight at its later frontier.  Persistent non-target requests use its
completed target track; movable requests use the terminal-clean track.  This
module turns that local split geometry into the exact non-circular input used
by the canonical recursion.

The history-sensitive comparison information is explicit: the installed
family belongs to one comparison warp and every frozen completed component
has an unused suffix shadow there.  No whole-row frontier-tightness invariant
or arbitrary-payload reconstruction is used.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularPersistentSource915Producer

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-! ## The protected comparison provenance -/

/-- The exact residual datum from which the lower induction hypothesis can
construct a comparison warp disjoint from the frozen completed carrier.

The boundary equality is intentionally part of the record.  Without the
frame's residual unhinderedness, stage-clean annular completion alone gives
no protection against target components completed at earlier stages. -/
structure ProtectedComparisonInput
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (base : Set G.DPath)
    (alpha : Ladder.Stage kappa) where
  frame : RegularJointSafeReplacement.ProtectedRestorationFrame G base
  boundary_eq : frame.split.boundary = L.frontier alpha
  requests_small : #(frame.state.requests) < kappa

namespace ProtectedComparisonInput

/-- The lower-cardinal protected fill supplies exactly the comparison facts
used by `PersistentSplitInput`: a full warp, a used subwarp avoiding the old
strict roof and the completed carrier, and one unused suffix shadow for every
completed base component. -/
theorem exists_comparisonWarp
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    {L : G.KappaLadder kappa} {base : Set G.DPath}
    {alpha : Ladder.Stage kappa}
    (P : ProtectedComparisonInput G L base alpha) :
    ∃ Tused Tfull : Set G.DPath,
      G.IsWarp Tfull ∧
        Tused ⊆ Tfull ∧
        Disjoint (G.vertexSet (completedPart G base))
          (G.vertexSet Tused) ∧
        G.vertexSet Tused ⊆
          (G.strictRoof (L.frontier alpha))ᶜ ∧
        (∀ f ∈ completedPart G base, ∃ t ∈ Tfull,
          t ∉ Tused ∧
            f.support \ G.strictRoof (L.frontier alpha) ⊆ t.support) := by
  obtain ⟨Tused, Tfull, hfull, hused, hdisjoint, havoid, hshadow⟩ :=
    RegularEventualCompatibility.exists_protectedComparisonWarp_of_lower
      G hNorm hlower huncountable P.frame P.requests_small
  refine ⟨Tused, Tfull, hfull, hused, hdisjoint, ?_, ?_⟩
  · simpa only [P.boundary_eq] using havoid
  · intro f hf
    obtain ⟨t, ht, htUnused, hft⟩ := hshadow f hf
    exact ⟨t, ht, htUnused, by simpa only [P.boundary_eq] using hft⟩

end ProtectedComparisonInput

private theorem transport_slice_target
    {G : DWeb V} {left right U U' : Set V}
    (h : U = U')
    (S : RegularCompletedPendingSplice.CleanTargetSlice G left right U) :
    (h ▸ S).target = S.target := by
  subst U'
  rfl

private theorem transport_slice_clean
    {G : DWeb V} {left right U U' : Set V}
    (h : U = U')
    (S : RegularCompletedPendingSplice.CleanTargetSlice G left right U) :
    (h ▸ S).clean = S.clean := by
  subst U'
  rfl

private theorem transport_star_finite
    {G : DWeb V} {old T T' : Set G.DPath}
    (h : T = T') (hcompat : G.StarCompatible old T)
    (hfinite : G.HasFiniteCharacter (G.star hcompat)) :
    G.HasFiniteCharacter (G.star (h ▸ hcompat)) := by
  cases h
  exact hfinite

private theorem transport_freeze_vertices
    {G : DWeb V} {old T T' : Set G.DPath} {Z : Set V}
    (h : T = T') (hcompat : G.StarCompatible (pendingPart G old) T)
    (hclosed : G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G old T hcompat) ⊆
        Z) :
    G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G old T'
        (h ▸ hcompat)) ⊆ Z := by
  cases h
  exact hclosed

private theorem transport_freeze_pending_roof
    {G : DWeb V} {old T T' : Set G.DPath} {C : Set V}
    (h : T = T') (hcompat : G.StarCompatible (pendingPart G old) T)
    (hroof : G.vertexSet (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G old T hcompat)) ⊆
        G.roof C) :
    G.vertexSet (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G old T'
        (h ▸ hcompat))) ⊆ G.roof C := by
  cases h
  exact hroof

/-- Turn one source-faithful weak-annular split into the exact raw successor
input.  The base row and its pending invariant come from the canonical
history constructor.  The local split `S` supplies the later club stage,
both installed tracks, their protected comparison/suffix shadows, closure,
and the stage-relative maverick bounds.

`PersistentSplitInput.toInstalledComparisonStage` subsequently derives the
new pending tightness, request/status, and the completion of every required
coordinate. -/
def persistentSplitInput
    {kappa : Cardinal.{u}} {G : DWeb V}
    {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
    {Z A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    {baseStage : Ladder.Stage kappa} {base : Set G.DPath}
    (hL : L.SliceGeometry)
    (hbaseFinite : G.HasFiniteCharacter base)
    (hbaseInitial : G.initialSet base = A)
    (hbaseExtends : ∀ j (hji : j < i),
      G.ForwardExtension (previous j hji).row base)
    (hbaseFreezes : ∀ j (hji : j < i),
      completedPart G (previous j hji).row ⊆ completedPart G base)
    (hbasePendingTight : TightLinkageBetween G
      (G.initialSet (pendingPart G base)) (L.frontier baseStage)
        (pendingPart G base))
    (hbasePendingRoof : G.vertexSet (pendingPart G base) ⊆
      G.roof (L.frontier baseStage))
    (S : RegularSplitTargetedComparison.SplitTargetedComparisonStage
      G L Sigma Z base baseStage
        (RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma Z A request i previous base))
    (hindex : ∀ j (hji : j < i),
      (previous j hji).stageIndex < S.stageIndex)
    (hpersistent : S.persistent =
      RegularPersistentRequestSplit.persistentPart G L
        (RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma Z A request i previous base))
    (hmovable : S.movable =
      RegularPersistentRequestSplit.movablePart G L
        (RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma Z A request i previous base))
    (hOldStatus : ∀ p ∈ pendingPart G base,
      SliceSpliceConstructor.IsStagePrefix G L baseStage p ∨
        ∃ x ∈ RegularGlobalAdmissibleProvider.requiredPendingTerminals
            G L Sigma Z A request i previous base,
          G.terminal? p = some x) :
    RegularPersistentCanonicalSuccessor.PersistentSplitInput
      G L Sigma Z A request i previous := by
  let slice : RegularCompletedPendingSplice.CleanTargetSlice G
      (G.terminalFrontier (pendingPart G base))
      (L.frontier S.stageIndex)
      (RegularPersistentRequestSplit.persistentPart G L
        (RegularGlobalAdmissibleProvider.requiredPendingTerminals
          G L Sigma Z A request i previous base)) :=
    hpersistent ▸ S.slice
  have htarget : slice.target = S.slice.target :=
    transport_slice_target hpersistent S.slice
  have hclean : slice.clean = S.slice.clean :=
    transport_slice_clean hpersistent S.slice
  have hunion : slice.target ∪ slice.clean =
      S.slice.target ∪ S.slice.clean := by
    rw [htarget, hclean]
  have hOldBoundary : MeetsOnlyAtTerminal G (pendingPart G base)
      (L.frontier S.stageIndex) :=
    meetsOnlyAtTerminal_of_roof_of_disjoint_strictRoof
      (hL.frontiersEssential baseStage) hbasePendingRoof
        hbasePendingTight.2
        (hL.strictFrontierChronology S.index_lt_stageIndex)
  let hcompat : G.StarCompatible (pendingPart G base)
      (slice.target ∪ slice.clean) := hunion.symm ▸ S.compatible
  exact
    { baseStage := baseStage
      base := base
      base_warp := S.base_warp
      base_finite := hbaseFinite
      base_initial := hbaseInitial
      base_extends := hbaseExtends
      base_freezes := hbaseFreezes
      stageIndex := S.stageIndex
      stageIndex_mem := S.stageIndex_mem
      index_strict := hindex
      comparison := S.comparison
      comparison_warp := S.comparison_warp
      slice := slice
      installed_subset := by
        rw [hunion]
        exact S.installed_subset
      installed_avoids_old_strictRoof := by
        rw [hunion]
        exact S.installed_avoids_old_strictRoof
      completed_shadow := by
        intro f hf
        obtain ⟨t, ht, htNot, hft⟩ := S.completed_shadow f hf
        exact ⟨t, ht, hunion.symm ▸ htNot, hft⟩
      compatible := hcompat
      installed_star_finite := transport_star_finite hunion.symm
        S.compatible S.installed_star_finite
      vertices_closed := transport_freeze_vertices hunion.symm
        S.compatible S.vertices_closed
      pending_below_roof := transport_freeze_pending_roof hunion.symm
        S.compatible S.pending_below_roof
      old_pending_boundary := hOldBoundary
      old_pending_status := hOldStatus
      clean_links_movable := by
        rw [hclean, ← hmovable]
        exact S.clean_links_movable
      cleanIntervals := by
        rw [hclean]
        exact S.cleanIntervals
      cleanMavericks_small := by
        rw [hclean]
        exact S.cleanMavericks_small
      cleanMavericks_closed := by
        rw [hclean]
        exact S.cleanMavericks_closed }

end RegularPersistentSource915Producer
end CardinalInduction
end Erdos599
