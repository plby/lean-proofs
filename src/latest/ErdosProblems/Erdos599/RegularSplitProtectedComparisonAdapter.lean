/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.RegularPersistentSource915Producer
import ErdosProblems.Erdos599.RegularRoofSuffixCompatibility
import ErdosProblems.Erdos599.RegularRoofedAnnularSuccessor
import ErdosProblems.Erdos599.RegularDirectPersistentCanonicalSuccessor

/-!
# Protected-comparison adapter for the regular split successor

An annular comparison at stages `alpha < beta` starts at the ladder frontier
at `alpha`.  It is therefore not generally a forward extension of the
ambient source-rooted recursive row.  The correct history-sensitive
certificate is the one supplied by protected residual comparison: a used
subwarp avoiding the old strict roof and completed carrier, together with an
unused suffix shadow in the full comparison for every completed component.

This file records that certificate and connects
`exists_protectedComparisonWarp_of_lower` to the exact
`SplitTargetedComparisonStage` consumed by the regular recursion.  The
remaining fields are precisely the local source-9.15 stage geometry; no
deletion/quotient commutation or false full-row forward extension is used.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace RegularSplitProtectedComparisonAdapter

open SingularExtension SliceSpliceSource

universe u

variable {V : Type u}

/-- History-sensitive comparison data produced in a protected residual.
`used` is the family installed at the present successor, while `full`
retains the unused shadows which protect earlier completed components. -/
structure ProtectedComparisonWarp (G : DWeb V)
    (base : Set G.DPath) (oldBoundary : Set V) where
  used : Set G.DPath
  full : Set G.DPath
  full_warp : G.IsWarp full
  used_subset : used ⊆ full
  completed_disjoint :
    Disjoint (G.vertexSet (completedPart G base)) (G.vertexSet used)
  used_avoids_strictRoof :
    G.vertexSet used ⊆ (G.strictRoof oldBoundary)ᶜ
  completed_shadow : ∀ f ∈ completedPart G base,
    ∃ t ∈ full, t ∉ used ∧
      f.support \ G.strictRoof oldBoundary ⊆ t.support

namespace ProtectedComparisonWarp

/-- The lower-cardinal protected fill, presented as one reusable comparison
certificate.  This is a structure-valued restatement of the exact theorem in
`RegularEventualCompatibility`; the ladder-boundary rewrite is supplied by
`ProtectedComparisonInput`. -/
theorem exists_of_lower
    {kappa : Cardinal.{u}} {G : DWeb V}
    (hNorm : G.IsNormalized)
    (hlower : UniversalCardinalInductionBelow V kappa)
    (huncountable : aleph0 < kappa)
    {L : G.KappaLadder kappa} {base : Set G.DPath}
    {alpha : Ladder.Stage kappa}
    (P : RegularPersistentSource915Producer.ProtectedComparisonInput
      G L base alpha) :
    Nonempty (ProtectedComparisonWarp G base (L.frontier alpha)) := by
  obtain ⟨used, full, hfull, hused, hdisjoint, havoid, hshadow⟩ :=
    P.exists_comparisonWarp hNorm hlower huncountable
  exact ⟨
    { used := used
      full := full
      full_warp := hfull
      used_subset := hused
      completed_disjoint := hdisjoint
      used_avoids_strictRoof := havoid
      completed_shadow := hshadow }⟩

end ProtectedComparisonWarp

/-- Protected comparison data obtained from last-frontier suffixes of old
completed components.  A suffix covers the old component outside the old
roof.  Contacts on the essential frontier are excluded separately by the
pending-owner field. -/
structure RoofSuffixComparisonWarp (G : DWeb V)
    (base : Set G.DPath) (oldBoundary : Set V) where
  used : Set G.DPath
  full : Set G.DPath
  full_warp : G.IsWarp full
  used_subset : used ⊆ full
  used_avoids_strictRoof :
    G.vertexSet used ⊆ (G.strictRoof oldBoundary)ᶜ
  used_frontier_owner : G.vertexSet used ∩ oldBoundary ⊆
    G.vertexSet (pendingPart G base)
  completed_roofShadow : ∀ f ∈ completedPart G base,
    ∃ t ∈ full, t ∉ used ∧
      f.support \ G.roof oldBoundary ⊆ t.support

namespace RoofSuffixComparisonWarp

/-- Last-frontier roof suffixes imply literal completed/used carrier
disjointness. -/
theorem completed_disjoint
    {G : DWeb V} {base : Set G.DPath} {C : Set V}
    (P : RoofSuffixComparisonWarp G base C)
    (hbase : G.IsWarp base) (hessential : G.essential C = C) :
    Disjoint (G.vertexSet (completedPart G base)) (G.vertexSet P.used) := by
  exact RegularRoofSuffixCompatibility.disjoint_subfamily_of_roofSuffixShadow
    G hbase hessential P.full_warp P.used_subset
      P.used_avoids_strictRoof P.used_frontier_owner
      P.completed_roofShadow

/-- Provider-facing clean-step consequence of a last-frontier roof-suffix
comparison. -/
theorem cleanStep
    {G : DWeb V} {base : Set G.DPath} {C : Set V}
    (P : RoofSuffixComparisonWarp G base C)
    (hbase : G.IsWarp base) (hessential : G.essential C = C)
    (hcompat : G.StarCompatible (pendingPart G base) P.used) :
    RegularCompletedPendingSplice.IsCleanTargetStep G base P.used
      hcompat := by
  exact RegularRoofSuffixCompatibility.cleanTargetStep_of_roofSuffixShadow
    G hbase hessential P.full_warp P.used_subset
      P.used_avoids_strictRoof P.used_frontier_owner
      P.completed_roofShadow hcompat

end RoofSuffixComparisonWarp

/-- When the entire old row is already below the roof of the old boundary,
no suffix-shadow warp is needed.  Avoidance of the strict roof confines any
old/new intersection to the essential frontier, where ownership by the old
pending carrier contradicts the old warp. -/
structure RoofProtectedUsedFamily (G : DWeb V)
    (base : Set G.DPath) (oldBoundary : Set V) where
  used : Set G.DPath
  used_warp : G.IsWarp used
  used_avoids_strictRoof :
    G.vertexSet used ⊆ (G.strictRoof oldBoundary)ᶜ
  used_frontier_owner : G.vertexSet used ∩ oldBoundary ⊆
    G.vertexSet (pendingPart G base)

namespace RoofProtectedUsedFamily

/-- Whole-row roof containment and frontier ownership give the exact
carrier separation from old completed components. -/
theorem completed_disjoint
    {G : DWeb V} {base : Set G.DPath} {C : Set V}
    (P : RoofProtectedUsedFamily G base C)
    (hbase : G.IsWarp base)
    (hbaseRoof : G.vertexSet base ⊆ G.roof C)
    (hessential : G.essential C = C) :
    Disjoint (G.vertexSet (completedPart G base)) (G.vertexSet P.used) := by
  have hcompletedRoof : G.vertexSet (completedPart G base) ⊆ G.roof C := by
    rintro x ⟨p, hp, hxp⟩
    exact hbaseRoof ⟨p, hp.1, hxp⟩
  exact RegularRoofSuffixCompatibility.disjoint_subfamily_of_roofedCompleted
    G hbase hessential hcompletedRoof P.used_avoids_strictRoof
      P.used_frontier_owner

/-- Provider-facing direct clean-step certificate with no shadow family. -/
theorem cleanStep
    {G : DWeb V} {base : Set G.DPath} {C : Set V}
    (P : RoofProtectedUsedFamily G base C)
    (hbase : G.IsWarp base)
    (hbaseRoof : G.vertexSet base ⊆ G.roof C)
    (hessential : G.essential C = C)
    (hcompat : G.StarCompatible (pendingPart G base) P.used) :
    RegularCompletedPendingSplice.IsCleanTargetStep G base P.used
      hcompat := by
  have hcompletedRoof : G.vertexSet (completedPart G base) ⊆ G.roof C := by
    rintro x ⟨p, hp, hxp⟩
    exact hbaseRoof ⟨p, hp.1, hxp⟩
  exact RegularRoofSuffixCompatibility.cleanTargetStep_of_roofedCompleted
    G hbase hessential hcompletedRoof P.used_warp
      P.used_avoids_strictRoof P.used_frontier_owner hcompat

end RoofProtectedUsedFamily

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

/-- A source-9.15 split stage whose comparison provenance is explicitly the
protected certificate above.  The installed equality says that the two
actual tracks are exactly the used part of the protected comparison. -/
structure ProtectedSplitTargetedComparisonStage
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z : Set V) (base : Set G.DPath)
    (alpha : Ladder.Stage kappa) (U : Set V) where
  stageIndex : Ladder.Stage kappa
  stageIndex_mem : stageIndex ∈ Sigma
  index_lt_stageIndex : alpha < stageIndex

  base_warp : G.IsWarp base
  request_subset : U ⊆ G.terminalFrontier (pendingPart G base)
  persistent : Set V
  movable : Set V
  persistent_union_movable : persistent ∪ movable = U
  persistent_movable_disjoint : Disjoint persistent movable

  /-- The history-sensitive comparison.  Its full warp contains the old
  source-rooted completed components and is not itself annular. -/
  comparison : ProtectedComparisonWarp G base (L.frontier alpha)
  /-- The distinct stage-annular comparison which supplies the geometric
  provenance of the installed tracks. -/
  annularComparison : Set G.DPath
  annularComparison_annular : SliceSplice.IsAnnularSlice G L annularComparison
    alpha stageIndex U

  slice : RegularCompletedPendingSplice.CleanTargetSlice G
    (G.terminalFrontier (pendingPart G base))
      (L.frontier stageIndex) persistent
  target_small : #(slice.target) < kappa
  movable_subset_clean_initial : movable ⊆
    G.terminalFrontier (pendingPart G base) \ persistent
  clean_links_movable : LinksToTarget G slice.clean movable
  installed_eq : slice.target ∪ slice.clean = comparison.used
  installed_subset_annular : slice.target ∪ slice.clean ⊆ annularComparison

  compatible : G.StarCompatible (pendingPart G base)
    (slice.target ∪ slice.clean)
  installed_star_finite : G.HasFiniteCharacter (G.star compatible)
  vertices_closed :
    G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible) ⊆ Z
  pending_tight : TightLinkageBetween G
    (G.initialSet (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible)))
    (L.frontier stageIndex)
    (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible))
  pending_below_roof : G.vertexSet
    (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible)) ⊆
      G.roof (L.frontier stageIndex)

  cleanIntervals : SliceCandidate.HasStageIntervalSegments
    G L slice.clean alpha stageIndex
  cleanMavericks_small :
    #(ControlledSlices.sliceMavericks G (L.warpAt stageIndex)
      slice.clean) < kappa
  cleanMavericks_closed :
    G.vertexSet
      (ControlledSlices.sliceMavericks G (L.warpAt stageIndex)
        slice.clean) ⊆ Z

namespace ProtectedSplitTargetedComparisonStage

variable {kappa : Cardinal.{u}} {G : DWeb V}
  {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
  {Z : Set V} {base : Set G.DPath} {alpha : Ladder.Stage kappa}
  {U : Set V}

/-- The protected unused shadows discharge the completed/pending
cross-disjointness required by the sound splice. -/
theorem cleanStep
    (S : ProtectedSplitTargetedComparisonStage
      G L Sigma Z base alpha U) :
    RegularCompletedPendingSplice.IsCleanTargetStep G base
      (S.slice.target ∪ S.slice.clean) S.compatible := by
  apply RegularEventualCompatibility.cleanTargetStep_of_used_suffixShadow
    G S.base_warp S.comparison.full_warp
  · rw [S.installed_eq]
    exact S.comparison.used_subset
  · rw [S.installed_eq]
    exact S.comparison.used_avoids_strictRoof
  · intro f hf
    obtain ⟨t, ht, htUnused, hft⟩ := S.comparison.completed_shadow f hf
    exact ⟨t, ht, S.installed_eq.symm ▸ htUnused, hft⟩

/-- Feed a two-warp source-9.15 stage directly to the canonical successor.
The annular comparison records the local ladder geometry; the protected
comparison is the distinct warp used for completed-carrier safety. -/
def persistentSplitInput
    {A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (hL : L.SliceGeometry)
    (hbaseFinite : G.HasFiniteCharacter base)
    (hbaseInitial : G.initialSet base = A)
    (hbaseExtends : ∀ j (hji : j < i),
      G.ForwardExtension (previous j hji).row base)
    (hbaseFreezes : ∀ j (hji : j < i),
      completedPart G (previous j hji).row ⊆ completedPart G base)
    (hbasePendingTight : TightLinkageBetween G
      (G.initialSet (pendingPart G base)) (L.frontier alpha)
        (pendingPart G base))
    (hbasePendingRoof : G.vertexSet (pendingPart G base) ⊆
      G.roof (L.frontier alpha))
    (S : ProtectedSplitTargetedComparisonStage
      G L Sigma Z base alpha
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
      SliceSpliceConstructor.IsStagePrefix G L alpha p ∨
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
      (hL.frontiersEssential alpha) hbasePendingRoof
        hbasePendingTight.2
        (hL.strictFrontierChronology S.index_lt_stageIndex)
  let hcompat : G.StarCompatible (pendingPart G base)
      (slice.target ∪ slice.clean) := hunion.symm ▸ S.compatible
  exact
    { baseStage := alpha
      base := base
      base_warp := S.base_warp
      base_finite := hbaseFinite
      base_initial := hbaseInitial
      base_extends := hbaseExtends
      base_freezes := hbaseFreezes
      stageIndex := S.stageIndex
      stageIndex_mem := S.stageIndex_mem
      index_strict := hindex
      comparison := S.comparison.full
      comparison_warp := S.comparison.full_warp
      slice := slice
      installed_subset := by
        rw [hunion, S.installed_eq]
        exact S.comparison.used_subset
      installed_avoids_old_strictRoof := by
        rw [hunion, S.installed_eq]
        exact S.comparison.used_avoids_strictRoof
      completed_shadow := by
        intro f hf
        obtain ⟨t, ht, htNot, hft⟩ := S.comparison.completed_shadow f hf
        exact ⟨t, ht, hunion.symm ▸ S.installed_eq.symm ▸ htNot, hft⟩
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

end ProtectedSplitTargetedComparisonStage

/-- Two-warp split stage using last-frontier roof suffixes for history
protection.  The protected shadow warp and the annular geometry warp are
deliberately distinct. -/
structure RoofSuffixSplitTargetedComparisonStage
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z : Set V) (base : Set G.DPath)
    (alpha : Ladder.Stage kappa) (U : Set V) where
  stageIndex : Ladder.Stage kappa
  stageIndex_mem : stageIndex ∈ Sigma
  index_lt_stageIndex : alpha < stageIndex

  base_warp : G.IsWarp base
  request_subset : U ⊆ G.terminalFrontier (pendingPart G base)
  persistent : Set V
  movable : Set V
  persistent_union_movable : persistent ∪ movable = U
  persistent_movable_disjoint : Disjoint persistent movable

  comparison : RoofSuffixComparisonWarp G base (L.frontier alpha)
  annularComparison : Set G.DPath
  annularComparison_annular : SliceSplice.IsAnnularSlice G L annularComparison
    alpha stageIndex U

  slice : RegularCompletedPendingSplice.CleanTargetSlice G
    (G.terminalFrontier (pendingPart G base))
      (L.frontier stageIndex) persistent
  target_small : #(slice.target) < kappa
  movable_subset_clean_initial : movable ⊆
    G.terminalFrontier (pendingPart G base) \ persistent
  clean_links_movable : LinksToTarget G slice.clean movable
  installed_eq : slice.target ∪ slice.clean = comparison.used
  installed_subset_annular : slice.target ∪ slice.clean ⊆ annularComparison

  compatible : G.StarCompatible (pendingPart G base)
    (slice.target ∪ slice.clean)
  installed_star_finite : G.HasFiniteCharacter (G.star compatible)
  vertices_closed :
    G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible) ⊆ Z
  pending_tight : TightLinkageBetween G
    (G.initialSet (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible)))
    (L.frontier stageIndex)
    (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible))
  pending_below_roof : G.vertexSet
    (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible)) ⊆
      G.roof (L.frontier stageIndex)

  cleanIntervals : SliceCandidate.HasStageIntervalSegments
    G L slice.clean alpha stageIndex
  cleanMavericks_small :
    #(ControlledSlices.sliceMavericks G (L.warpAt stageIndex)
      slice.clean) < kappa
  cleanMavericks_closed :
    G.vertexSet
      (ControlledSlices.sliceMavericks G (L.warpAt stageIndex)
        slice.clean) ⊆ Z

namespace RoofSuffixSplitTargetedComparisonStage

variable {kappa : Cardinal.{u}} {G : DWeb V}
  {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
  {Z : Set V} {base : Set G.DPath} {alpha : Ladder.Stage kappa}
  {U : Set V}

/-- The last-frontier suffix comparison proves the exact clean-step
predicate without being converted into the stronger strict-roof shadow
format. -/
theorem cleanStep
    (S : RoofSuffixSplitTargetedComparisonStage
      G L Sigma Z base alpha U)
    (hL : L.SliceGeometry) :
    RegularCompletedPendingSplice.IsCleanTargetStep G base
      (S.slice.target ∪ S.slice.clean) S.compatible := by
  have hcompat : G.StarCompatible (pendingPart G base)
      S.comparison.used :=
    S.installed_eq ▸ S.compatible
  have hclean := S.comparison.cleanStep S.base_warp
    (hL.frontiersEssential alpha) hcompat
  simpa only [S.installed_eq] using hclean

end RoofSuffixSplitTargetedComparisonStage

/-- Comparison-free two-track stage for the canonical whole-row roof
invariant.  The annular family supplies stage geometry; `used` carries only
the facts needed to install its selected tracks safely. -/
structure RoofProtectedSplitTargetedComparisonStage
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z : Set V) (base : Set G.DPath)
    (alpha : Ladder.Stage kappa) (U : Set V) where
  stageIndex : Ladder.Stage kappa
  stageIndex_mem : stageIndex ∈ Sigma
  index_lt_stageIndex : alpha < stageIndex

  base_warp : G.IsWarp base
  base_below_roof : G.vertexSet base ⊆ G.roof (L.frontier alpha)
  request_subset : U ⊆ G.terminalFrontier (pendingPart G base)
  persistent : Set V
  movable : Set V
  persistent_union_movable : persistent ∪ movable = U
  persistent_movable_disjoint : Disjoint persistent movable

  protectedUsed : RoofProtectedUsedFamily G base (L.frontier alpha)
  annularComparison : Set G.DPath
  annularComparison_annular : SliceSplice.IsAnnularSlice G L annularComparison
    alpha stageIndex U

  slice : RegularCompletedPendingSplice.CleanTargetSlice G
    (G.terminalFrontier (pendingPart G base))
      (L.frontier stageIndex) persistent
  target_small : #(slice.target) < kappa
  movable_subset_clean_initial : movable ⊆
    G.terminalFrontier (pendingPart G base) \ persistent
  clean_links_movable : LinksToTarget G slice.clean movable
  installed_eq : slice.target ∪ slice.clean = protectedUsed.used
  installed_subset_annular : slice.target ∪ slice.clean ⊆ annularComparison

  compatible : G.StarCompatible (pendingPart G base)
    (slice.target ∪ slice.clean)
  installed_star_finite : G.HasFiniteCharacter (G.star compatible)
  vertices_closed :
    G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible) ⊆ Z
  pending_tight : TightLinkageBetween G
    (G.initialSet (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible)))
    (L.frontier stageIndex)
    (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible))
  pending_below_roof : G.vertexSet
    (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible)) ⊆
      G.roof (L.frontier stageIndex)

  cleanIntervals : SliceCandidate.HasStageIntervalSegments
    G L slice.clean alpha stageIndex
  cleanMavericks_small :
    #(ControlledSlices.sliceMavericks G (L.warpAt stageIndex)
      slice.clean) < kappa
  cleanMavericks_closed :
    G.vertexSet
      (ControlledSlices.sliceMavericks G (L.warpAt stageIndex)
        slice.clean) ⊆ Z

namespace RoofProtectedSplitTargetedComparisonStage

variable {kappa : Cardinal.{u}} {G : DWeb V}
  {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
  {Z : Set V} {base : Set G.DPath} {alpha : Ladder.Stage kappa}
  {U : Set V}

/-- Canonical whole-row roof containment directly proves safe installation;
there is no auxiliary shadow warp. -/
theorem cleanStep
    (S : RoofProtectedSplitTargetedComparisonStage
      G L Sigma Z base alpha U)
    (hL : L.SliceGeometry) :
    RegularCompletedPendingSplice.IsCleanTargetStep G base
      (S.slice.target ∪ S.slice.clean) S.compatible := by
  have hcompat : G.StarCompatible (pendingPart G base)
      S.protectedUsed.used :=
    S.installed_eq ▸ S.compatible
  have hclean := S.protectedUsed.cleanStep S.base_warp S.base_below_roof
    (hL.frontiersEssential alpha) hcompat
  simpa only [S.installed_eq] using hclean

/-- Retype the canonical whole-roof split as the proof-method-independent
persistent input.  This is the exact adapter consumed by
`DirectPersistentSplitInput.toDirectInstalledStage`. -/
def directPersistentSplitInput
    {A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (hL : L.SliceGeometry)
    (hbaseFinite : G.HasFiniteCharacter base)
    (hbaseInitial : G.initialSet base = A)
    (hbaseExtends : ∀ j (hji : j < i),
      G.ForwardExtension (previous j hji).row base)
    (hbaseFreezes : ∀ j (hji : j < i),
      completedPart G (previous j hji).row ⊆ completedPart G base)
    (hbasePendingTight : TightLinkageBetween G
      (G.initialSet (pendingPart G base)) (L.frontier alpha)
        (pendingPart G base))
    (hbasePendingRoof : G.vertexSet (pendingPart G base) ⊆
      G.roof (L.frontier alpha))
    (S : RoofProtectedSplitTargetedComparisonStage
      G L Sigma Z base alpha
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
      SliceSpliceConstructor.IsStagePrefix G L alpha p ∨
        ∃ x ∈ RegularGlobalAdmissibleProvider.requiredPendingTerminals
            G L Sigma Z A request i previous base,
          G.terminal? p = some x) :
    RegularDirectPersistentCanonicalSuccessor.DirectPersistentSplitInput
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
      (hL.frontiersEssential alpha) hbasePendingRoof
        hbasePendingTight.2
        (hL.strictFrontierChronology S.index_lt_stageIndex)
  let hcompat : G.StarCompatible (pendingPart G base)
      (slice.target ∪ slice.clean) := hunion.symm ▸ S.compatible
  have hstep : RegularCompletedPendingSplice.IsCleanTargetStep G base
      (slice.target ∪ slice.clean) hcompat := by
    have h := S.cleanStep hL
    simpa only [hunion] using h
  exact
    { baseStage := alpha
      base := base
      base_warp := S.base_warp
      base_finite := hbaseFinite
      base_initial := hbaseInitial
      base_extends := hbaseExtends
      base_freezes := hbaseFreezes
      stageIndex := S.stageIndex
      stageIndex_mem := S.stageIndex_mem
      index_strict := hindex
      slice := slice
      compatible := hcompat
      cleanStep := hstep
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

end RoofProtectedSplitTargetedComparisonStage

/-- Minimal source-9.15 successor certificate for the canonical whole-row
roof invariant.  The weak annular comparison itself proves both protection
from old completed components and preservation of the roof invariant, so no
auxiliary shadow warp or separately packaged used family is required. -/
structure RoofedAnnularSplitTargetedComparisonStage
    {kappa : Cardinal.{u}} (G : DWeb V)
    (L : G.KappaLadder kappa) (Sigma : Set (Ladder.Stage kappa))
    (Z : Set V) (base : Set G.DPath)
    (alpha : Ladder.Stage kappa) (U : Set V) where
  stageIndex : Ladder.Stage kappa
  stageIndex_mem : stageIndex ∈ Sigma
  index_lt_stageIndex : alpha < stageIndex

  base_warp : G.IsWarp base
  base_below_roof : G.vertexSet base ⊆ G.roof (L.frontier alpha)
  request_subset : U ⊆ G.terminalFrontier (pendingPart G base)
  persistent : Set V
  movable : Set V
  persistent_union_movable : persistent ∪ movable = U
  persistent_movable_disjoint : Disjoint persistent movable

  annularComparison : Set G.DPath
  annularComparison_annular : SliceSplice.IsAnnularSlice G L annularComparison
    alpha stageIndex U

  slice : RegularCompletedPendingSplice.CleanTargetSlice G
    (G.terminalFrontier (pendingPart G base))
      (L.frontier stageIndex) persistent
  target_small : #(slice.target) < kappa
  movable_subset_clean_initial : movable ⊆
    G.terminalFrontier (pendingPart G base) \ persistent
  clean_links_movable : LinksToTarget G slice.clean movable
  installed_subset_annular : slice.target ∪ slice.clean ⊆ annularComparison

  compatible : G.StarCompatible (pendingPart G base)
    (slice.target ∪ slice.clean)
  installed_star_finite : G.HasFiniteCharacter (G.star compatible)
  vertices_closed :
    G.vertexSet
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (slice.target ∪ slice.clean) compatible) ⊆ Z

  cleanIntervals : SliceCandidate.HasStageIntervalSegments
    G L slice.clean alpha stageIndex
  cleanMavericks_small :
    #(ControlledSlices.sliceMavericks G (L.warpAt stageIndex)
      slice.clean) < kappa
  cleanMavericks_closed :
    G.vertexSet
      (ControlledSlices.sliceMavericks G (L.warpAt stageIndex)
        slice.clean) ⊆ Z

namespace RoofedAnnularSplitTargetedComparisonStage

variable {kappa : Cardinal.{u}} {G : DWeb V}
  {L : G.KappaLadder kappa} {Sigma : Set (Ladder.Stage kappa)}
  {Z : Set V} {base : Set G.DPath} {alpha : Ladder.Stage kappa}
  {U : Set V}

/-- The annular comparison simultaneously proves the exact clean-step
condition and whole-row roof containment at the new stage. -/
theorem cleanStep_and_result_below_roof
    (S : RoofedAnnularSplitTargetedComparisonStage
      G L Sigma Z base alpha U)
    (hL : L.SliceGeometry) :
    RegularCompletedPendingSplice.IsCleanTargetStep G base
        (S.slice.target ∪ S.slice.clean) S.compatible ∧
      G.vertexSet
          (RegularCompletedPendingSplice.freezeCompletedStar G base
            (S.slice.target ∪ S.slice.clean) S.compatible) ⊆
        G.roof (L.frontier S.stageIndex) := by
  exact
    RegularRoofedAnnularSuccessor.cleanTargetStep_and_result_below_roof_of_annular
      hL S.index_lt_stageIndex S.base_warp S.base_below_roof
        S.annularComparison_annular S.slice S.installed_subset_annular
        S.compatible

/-- Retype the minimal roofed-annular stage as the direct persistent input.
The next pending-roof field is obtained by restricting the whole-result roof
conclusion, rather than requested separately from the source theorem. -/
def directPersistentSplitInput
    {A : Set V} {request : Ladder.Stage kappa → Option A}
    {i : Ladder.Stage kappa}
    {previous : ∀ j : Ladder.Stage kappa, j < i →
      RegularCompletedPendingSplice.RecursivePayload G L Sigma Z A}
    (hL : L.SliceGeometry)
    (hbaseFinite : G.HasFiniteCharacter base)
    (hbaseInitial : G.initialSet base = A)
    (hbaseExtends : ∀ j (hji : j < i),
      G.ForwardExtension (previous j hji).row base)
    (hbaseFreezes : ∀ j (hji : j < i),
      completedPart G (previous j hji).row ⊆ completedPart G base)
    (hbasePendingTight : TightLinkageBetween G
      (G.initialSet (pendingPart G base)) (L.frontier alpha)
        (pendingPart G base))
    (hbasePendingRoof : G.vertexSet (pendingPart G base) ⊆
      G.roof (L.frontier alpha))
    (S : RoofedAnnularSplitTargetedComparisonStage
      G L Sigma Z base alpha
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
      SliceSpliceConstructor.IsStagePrefix G L alpha p ∨
        ∃ x ∈ RegularGlobalAdmissibleProvider.requiredPendingTerminals
            G L Sigma Z A request i previous base,
          G.terminal? p = some x) :
    RegularDirectPersistentCanonicalSuccessor.DirectPersistentSplitInput
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
      (hL.frontiersEssential alpha) hbasePendingRoof
        hbasePendingTight.2
        (hL.strictFrontierChronology S.index_lt_stageIndex)
  let hcompat : G.StarCompatible (pendingPart G base)
      (slice.target ∪ slice.clean) := hunion.symm ▸ S.compatible
  have hstep : RegularCompletedPendingSplice.IsCleanTargetStep G base
      (slice.target ∪ slice.clean) hcompat := by
    simpa only [hunion] using (S.cleanStep_and_result_below_roof hL).1
  have hpendingRoofOriginal : G.vertexSet (pendingPart G
      (RegularCompletedPendingSplice.freezeCompletedStar G base
        (S.slice.target ∪ S.slice.clean) S.compatible)) ⊆
      G.roof (L.frontier S.stageIndex) := by
    rintro x ⟨p, hp, hxp⟩
    exact (S.cleanStep_and_result_below_roof hL).2 ⟨p, hp.1, hxp⟩
  exact
    { baseStage := alpha
      base := base
      base_warp := S.base_warp
      base_finite := hbaseFinite
      base_initial := hbaseInitial
      base_extends := hbaseExtends
      base_freezes := hbaseFreezes
      stageIndex := S.stageIndex
      stageIndex_mem := S.stageIndex_mem
      index_strict := hindex
      slice := slice
      compatible := hcompat
      cleanStep := hstep
      installed_star_finite := transport_star_finite hunion.symm
        S.compatible S.installed_star_finite
      vertices_closed := transport_freeze_vertices hunion.symm
        S.compatible S.vertices_closed
      pending_below_roof := transport_freeze_pending_roof hunion.symm
        S.compatible hpendingRoofOriginal
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

end RoofedAnnularSplitTargetedComparisonStage

end RegularSplitProtectedComparisonAdapter
end CardinalInduction
end Erdos599
