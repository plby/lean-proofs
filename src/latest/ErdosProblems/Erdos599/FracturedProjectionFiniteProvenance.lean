/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedProjectionFinite
import ErdosProblems.Erdos599.FiniteTraceOwnerUniqueness
import ErdosProblems.Erdos599.FiniteRunTagSeparation
import ErdosProblems.Erdos599.AlternatingMacroProvenance
import ErdosProblems.Erdos599.AlternatingMacroSafety
import ErdosProblems.Erdos599.FracturedProjectionSelectedEndpoints
import Mathlib.Data.List.NodupEquivFin

/-!
# Occurrence provenance for finite fractured projection

The connector-deleted raw list is tagged by its unique source-link
occurrence.  Transporting those tags through the order embedding supplied by
chronological erasure makes it possible to prove that one reference member
owns at most one compressed backward run.
-/

noncomputable section

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint
namespace FracturedAssignmentPeel

open Set DirectedPath Alternating
open Alternating.FracturedDuplication
open PopularAuxiliary.Input

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}

local instance fracturedFiniteProvenanceDecidableEq : DecidableEq V :=
  Classical.decEq V

/-- The raw projected steps, with every occurrence tagged by the finite-trace
link that emitted it. -/
def taggedProjectedFiniteTraceSteps (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph) :
    List (Fin (Q.lastIndex + 1) × SignedEdge V) :=
  (List.ofFn fun i : Fin (Q.lastIndex + 1) ↦
    (projectedLinkSteps Z (Q.link i)).map (i, ·)).flatten

@[simp] theorem taggedProjectedFiniteTraceSteps_map_snd
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph) :
    (taggedProjectedFiniteTraceSteps Z Q).map Prod.snd =
      projectedFiniteTraceSteps Z Q := by
  unfold taggedProjectedFiniteTraceSteps projectedFiniteTraceSteps
    projectedChainSteps finiteTraceLinks
  rw [List.map_flatten, List.flatMap_def]
  apply congrArg List.flatten
  rw [List.map_ofFn, List.map_ofFn]
  rw [List.ofFn_inj]
  funext i
  change List.map Prod.snd
    (List.map (fun x ↦ (i, x)) (projectedLinkSteps Z (Q.link i))) =
      projectedLinkSteps Z (Q.link i)
  rw [List.map_map]
  change List.map (fun x ↦ x) (projectedLinkSteps Z (Q.link i)) = _
  induction projectedLinkSteps Z (Q.link i) with
  | nil => rfl
  | cons s ss ih => simp only [List.map_cons, ih]

@[simp] theorem taggedProjectedFiniteTraceSteps_length
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph) :
    (taggedProjectedFiniteTraceSteps Z Q).length =
      (projectedFiniteTraceSteps Z Q).length := by
  have h := congrArg List.length
    (taggedProjectedFiniteTraceSteps_map_snd Z Q)
  simpa only [List.length_map] using h

/-- The source link occurrence of a raw projected step. -/
def rawSourceLinkIndex (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (k : Fin (projectedFiniteTraceSteps Z Q).length) :
    Fin (Q.lastIndex + 1) :=
  ((taggedProjectedFiniteTraceSteps Z Q).get
    (Fin.cast (taggedProjectedFiniteTraceSteps_length Z Q).symm k)).1

theorem rawSourceLinkIndex_step_mem
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (k : Fin (projectedFiniteTraceSteps Z Q).length) :
    (projectedFiniteTraceSteps Z Q).get k ∈
      projectedLinkSteps Z (Q.link (rawSourceLinkIndex Z Q k)) := by
  let kt := Fin.cast (taggedProjectedFiniteTraceSteps_length Z Q).symm k
  have hget := List.get_mem (taggedProjectedFiniteTraceSteps Z Q) kt
  simp only [taggedProjectedFiniteTraceSteps, List.mem_flatten] at hget
  rcases hget with ⟨block, hblock, hpair⟩
  rcases List.mem_ofFn.mp hblock with ⟨i, hi⟩
  rw [← hi] at hpair
  obtain ⟨s, hs, hst⟩ := List.mem_map.mp hpair
  have htag : rawSourceLinkIndex Z Q k = i := by
    change ((taggedProjectedFiniteTraceSteps Z Q).get kt).1 = i
    exact congrArg Prod.fst hst.symm
  rw [htag]
  have hsnd : (projectedFiniteTraceSteps Z Q).get k = s := by
    have hmap := congrArg (fun l : List (SignedEdge V) ↦ l[k.1]?)
      (taggedProjectedFiniteTraceSteps_map_snd Z Q)
    have htagged :
        ((taggedProjectedFiniteTraceSteps Z Q).map Prod.snd)[k.1]? =
          some ((taggedProjectedFiniteTraceSteps Z Q).get kt).2 := by
      rw [List.getElem?_eq_getElem (by
        simpa only [List.length_map,
          taggedProjectedFiniteTraceSteps_length] using k.isLt)]
      simp only [List.getElem_map]
      rfl
    have hraw : (projectedFiniteTraceSteps Z Q)[k.1]? =
        some ((projectedFiniteTraceSteps Z Q).get k) := by
      rw [List.getElem?_eq_getElem k.isLt]
      rfl
    rw [htagged, hraw] at hmap
    exact Option.some.inj (hmap.symm.trans (congrArg (some ∘ Prod.snd) hst.symm))
  rw [hsnd]
  exact hs

theorem rawSourceLinkIndex_direction
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (k : Fin (projectedFiniteTraceSteps Z Q).length) :
    ((projectedFiniteTraceSteps Z Q).get k).direction =
      (Q.link (rawSourceLinkIndex Z Q k)).direction :=
  (projectedLinkSteps_mem Z _
    (rawSourceLinkIndex_step_mem Z Q k)).1

/-- Source-link tags are monotone along the flattened raw step list. -/
theorem taggedProjectedFiniteTraceSteps_pairwise
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph) :
    (taggedProjectedFiniteTraceSteps Z Q).Pairwise
      (fun a b ↦ a.1 ≤ b.1) := by
  rw [taggedProjectedFiniteTraceSteps, List.pairwise_flatten]
  constructor
  · intro block hblock
    rcases List.mem_ofFn.mp hblock with ⟨i, hi⟩
    rw [← hi]
    rw [List.pairwise_iff_getElem]
    intro a b ha hb hab
    simp
  · rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    simp only [List.getElem_ofFn]
    intro a ha b hb
    rcases List.mem_map.mp ha with ⟨s, _hs, rfl⟩
    rcases List.mem_map.mp hb with ⟨t, _ht, rfl⟩
    simp
    omega

theorem rawSourceLinkIndex_mono
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    {a b : Fin (projectedFiniteTraceSteps Z Q).length} (hab : a ≤ b) :
    rawSourceLinkIndex Z Q a ≤ rawSourceLinkIndex Z Q b := by
  let ka := Fin.cast (taggedProjectedFiniteTraceSteps_length Z Q).symm a
  let kb := Fin.cast (taggedProjectedFiniteTraceSteps_length Z Q).symm b
  have hkakb : ka ≤ kb := by simpa [ka, kb] using hab
  change ((taggedProjectedFiniteTraceSteps Z Q).get ka).1 ≤
    ((taggedProjectedFiniteTraceSteps Z Q).get kb).1
  exact (taggedProjectedFiniteTraceSteps_pairwise Z Q).rel_get_of_le hkakb

/-- The strictly monotone raw positions selected by chronological erasure. -/
noncomputable def erasedRawEmbedding (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph) :
    let E := (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute
    Fin E.steps.length ↪o Fin (projectedFiniteTraceSteps Z Q).length :=
  Classical.choose
    (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
      (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps_sublist)

theorem erasedRawEmbedding_step_eq
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (k : Fin
      (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.length) :
    ((projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.get k) =
      (projectedFiniteTraceSteps Z Q).get (erasedRawEmbedding Z Q k) := by
  exact Classical.choose_spec
    (List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp
      (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps_sublist) k

/-- The upstairs source-link index of an erased retained step. -/
noncomputable def erasedSourceLinkIndex (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (k : Fin
      (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.length) :
    Fin (Q.lastIndex + 1) :=
  rawSourceLinkIndex Z Q (erasedRawEmbedding Z Q k)

theorem erasedSourceLinkIndex_mono
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    {a b : Fin
      (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.length}
    (hab : a ≤ b) :
    erasedSourceLinkIndex Z Q a ≤ erasedSourceLinkIndex Z Q b :=
  rawSourceLinkIndex_mono Z Q ((erasedRawEmbedding Z Q).monotone hab)

theorem erasedSourceLinkIndex_direction
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (k : Fin
      (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.length) :
    (((projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.get k).direction) =
      (Q.link (erasedSourceLinkIndex Z Q k)).direction := by
  rw [erasedRawEmbedding_step_eq Z Q k]
  exact rawSourceLinkIndex_direction Z Q (erasedRawEmbedding Z Q k)

/-! ## Backward retained-step witnesses -/

/-- Source-link and active-reference ownership data for one erased backward
step. -/
structure ErasedBackwardWitness (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (k : Fin
      (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.length)
    (hd : ((projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.get k).direction =
      .backward) where
  owner : FinitePath Gamma.graph
  owner_mem : (Sum.inl owner : Gamma.DPath) ∈ activeReference Z Y
  source_direction :
    (Q.link (erasedSourceLinkIndex Z Q k)).direction = .backward
  source_subpath :
    (Q.link (erasedSourceLinkIndex Z Q k)).path.IsSubpathOf
      (.inl (expandFinitePath Z owner))
  step_edge_mem :
    ((projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.get k).edge ∈
      owner.edgeSet

theorem exists_erasedBackwardWitness
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (k : Fin
      (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.length)
    (hd : ((projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.get k).direction =
      .backward) :
    Nonempty (ErasedBackwardWitness (Y := Y) Z Q k hd) := by
  let r := erasedRawEmbedding Z Q k
  let i := erasedSourceLinkIndex Z Q k
  have hrawEq :
      ((projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.get k) =
        (projectedFiniteTraceSteps Z Q).get r :=
    erasedRawEmbedding_step_eq Z Q k
  have hs := rawSourceLinkIndex_step_mem Z Q r
  have hinfo := projectedLinkSteps_mem Z (Q.link i) (by
    simpa [i, r, erasedSourceLinkIndex] using hs)
  have hidirection : (Q.link i).direction = .backward := by
    have hsource := erasedSourceLinkIndex_direction Z Q k
    exact hsource.symm.trans hd
  have hilink : Q.link i ∈ (AltPath.finite Q).links := by
    exact ⟨i, rfl⟩
  obtain ⟨P, hP, hsub⟩ :=
    hQ.isAlternating.2.1 (Q.link i) hilink hidirection
  obtain ⟨p, hp, hPeq⟩ := hP
  subst P
  rcases hinfo with ⟨_hstepDirection, _hvalid, hne, e, he, hedge⟩
  have heExpanded : e ∈ (expandFinitePath Z p).edgeSet := hsub.2 he
  have hprojNe : project e.1 ≠ project e.2 := by
    intro h
    apply hne
    rw [hedge]
    exact h
  have heOwner :=
    projected_edge_mem_of_mem_expandFinitePath Z p heExpanded hprojNe
  refine ⟨{
    owner := p
    owner_mem := hp
    source_direction := by simpa [i] using hidirection
    source_subpath := by simpa [i] using hsub
    step_edge_mem := ?_ }⟩
  have hedge' :
      ((projectedFiniteTraceSteps Z Q).get r).edge =
        (project e.1, project e.2) := by
    simpa [r] using hedge
  rw [hrawEq]
  rw [hedge']
  exact heOwner

/-- Canonical ownership data for an erased backward step. -/
noncomputable def erasedBackwardWitness
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (k : Fin
      (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.length)
    (hd : ((projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.get k).direction =
      .backward) :
    ErasedBackwardWitness (Y := Y) Z Q k hd :=
  Classical.choice (exists_erasedBackwardWitness Z Q hQ k hd)

/-- Adjacent erased backward steps come from the same upstairs source-link
occurrence.  Downstairs warp disjointness first identifies their active
reference owners; finite safe-trace owner injectivity then identifies the
source occurrences. -/
theorem erasedSourceLinkIndex_eq_of_adjacent_backward
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hY : Gamma.IsWarp Y)
    (hlast : Q.lastLink.direction = .forward)
    (k : ℕ)
    (hk : k + 1 <
      (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.length)
    (hd : ((projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps[k]).direction =
      .backward)
    (hdnext :
      ((projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps[k + 1]).direction =
        .backward) :
    erasedSourceLinkIndex Z Q ⟨k, by omega⟩ =
      erasedSourceLinkIndex Z Q ⟨k + 1, hk⟩ := by
  let E := (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute
  let a : Fin E.steps.length := ⟨k, by simpa [E] using (show k < k + 1 from by omega).trans hk⟩
  let b : Fin E.steps.length := ⟨k + 1, by simpa [E] using hk⟩
  have hda : (E.steps.get a).direction = .backward := by
    simpa [E, a] using hd
  have hdb : (E.steps.get b).direction = .backward := by
    simpa [E, b] using hdnext
  let A := erasedBackwardWitness Z Q hQ a hda
  let B := erasedBackwardWitness Z Q hQ b hdb
  have hjoin : (E.steps.get a).exit = (E.steps.get b).entry := by
    calc
      (E.steps.get a).exit = E.routeVertex (k + 1) := by
        simpa [a] using (E.routeVertex_succ_eq_exit a).symm
      _ = (E.steps.get b).entry := by
        simpa [b] using E.routeVertex_eq_entry b
  have hownerPath :
      (Sum.inl A.owner : Gamma.DPath) = Sum.inl B.owner := by
    refine DWeb.IsWarp.eq_of_mem_support (activeReference_isWarp Z hY)
      A.owner_mem B.owner_mem (x := (E.steps.get a).exit) ?_ ?_
    · rw [SignedEdge.exit_eq_fst_of_direction_backward _ hda]
      exact (A.owner.edgeSet_subset_support_prod A.step_edge_mem).1
    · rw [hjoin, SignedEdge.entry_eq_snd_of_direction_backward _ hdb]
      exact (B.owner.edgeSet_subset_support_prod B.step_edge_mem).2
  have howner : A.owner = B.owner := Sum.inl.inj hownerPath
  apply Q.backward_indices_eq_of_common_finite_owner_of_last_forward
    hQ.isSafe hlast A.source_direction B.source_direction
      ⟨A.owner, A.owner_mem, rfl⟩ A.source_subpath
  simpa [howner] using B.source_subpath

/-! ## Ownership of compressed backward runs -/

/-- The active-reference member selected by the already-proved
`BackwardLinksOn` certificate for a compressed backward link. -/
noncomputable def compressedBackwardOwner
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hY : Gamma.IsWarp Y)
    (l : Link Gamma.graph) (hl : l ∈ (finiteTraceCompression Z Q).path.links)
    (hd : l.direction = .backward) : Gamma.DPath :=
  Classical.choose
    (finiteTraceCompression_backwardLinksOn Z Q hQ hY l hl hd)

theorem compressedBackwardOwner_mem
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hY : Gamma.IsWarp Y)
    (l : Link Gamma.graph) (hl : l ∈ (finiteTraceCompression Z Q).path.links)
    (hd : l.direction = .backward) :
    compressedBackwardOwner Z Q hQ hY l hl hd ∈ activeReference Z Y :=
  (Classical.choose_spec
    (finiteTraceCompression_backwardLinksOn Z Q hQ hY l hl hd)).1

theorem compressedBackwardOwner_isSubpath
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hY : Gamma.IsWarp Y)
    (l : Link Gamma.graph) (hl : l ∈ (finiteTraceCompression Z Q).path.links)
    (hd : l.direction = .backward) :
    l.path.IsSubpathOf (compressedBackwardOwner Z Q hQ hY l hl hd) :=
  (Classical.choose_spec
    (finiteTraceCompression_backwardLinksOn Z Q hQ hY l hl hd)).2

/-! ## Canonical nonempty compression input -/

/-- The validity proof used by the finite projected compressor. -/
theorem projectedFiniteTraceErasedStep_valid
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    {s : SignedEdge V}
    (hs : s ∈ (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps) :
    SignedEdge.Valid (Gamma := Gamma) s :=
  (projectedFiniteTraceSteps_mem Z Q
    ((projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps_sublist.subset hs)).1

/-- The maximal-run input in the nonempty branch of finite projection. -/
noncomputable def projectedFiniteTraceInput
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hnil : (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps ≠ []) :
    Alternating.RunCompressor.FiniteInput Gamma.graph :=
  (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.toFiniteInputOfValid
    hnil (projectedFiniteTraceErasedStep_valid Z Q)

theorem finiteTraceCompression_path_eq_of_steps_ne_nil
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hnil : (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps ≠ []) :
    (finiteTraceCompression Z Q).path =
      .finite (projectedFiniteTraceInput Z Q hnil).toFiniteRunWalk.toFiniteTrace := by
  simp [finiteTraceCompression, ErasedSignedRoute.compressionOfValid, hnil,
    projectedFiniteTraceInput]

/-- The first retained erased edge of a maximal compressed run. -/
def projectedFiniteRunFirstIndex
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hnil : (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps ≠ [])
    (i : Fin (projectedFiniteTraceInput Z Q hnil).runs.length) :
    Fin (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.length :=
  ⟨Alternating.RunCompressor.runLower
      (projectedFiniteTraceInput Z Q hnil).runs i, by
    change Alternating.RunCompressor.runLower
      (projectedFiniteTraceInput Z Q hnil).runs i <
        (projectedFiniteTraceInput Z Q hnil).lastEdge
    exact lt_of_lt_of_le
      (Nat.lt_add_of_pos_right (List.length_pos_iff_ne_nil.2
        ((projectedFiniteTraceInput Z Q hnil).run_ne_nil (List.get_mem _ i))))
      ((projectedFiniteTraceInput Z Q hnil).runUpper_le_lastEdge i)⟩

theorem projectedFiniteRunFirstIndex_direction
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hnil : (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps ≠ [])
    (i : Fin (projectedFiniteTraceInput Z Q hnil).runs.length) :
    ((projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.get
        (projectedFiniteRunFirstIndex Z Q hnil i)).direction =
      (projectedFiniteTraceInput Z Q hnil).runDirection i := by
  let S := projectedFiniteTraceInput Z Q hnil
  have hpos : 0 < (S.runs.get i).length :=
    List.length_pos_iff_ne_nil.2 (S.run_ne_nil (List.get_mem _ i))
  change S.colour ⟨Alternating.RunCompressor.runLower S.runs i, _⟩ =
    S.runDirection i
  exact S.colour_run_offset i hpos

/-- Canonical reference owner of a compressed backward run: the owner of
its first retained erased edge. -/
noncomputable def projectedFiniteRunBackwardOwner
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hnil : (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps ≠ [])
    (i : Fin (projectedFiniteTraceInput Z Q hnil).runs.length)
    (hd : (projectedFiniteTraceInput Z Q hnil).runDirection i = .backward) :
    Gamma.DPath :=
  .inl (erasedBackwardWitness Z Q hQ
    (projectedFiniteRunFirstIndex Z Q hnil i)
    ((projectedFiniteRunFirstIndex_direction Z Q hnil i).trans hd)).owner

theorem projectedFiniteRunBackwardOwner_mem
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hnil : (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps ≠ [])
    (i : Fin (projectedFiniteTraceInput Z Q hnil).runs.length)
    (hd : (projectedFiniteTraceInput Z Q hnil).runDirection i = .backward) :
    projectedFiniteRunBackwardOwner Z Q hQ hnil i hd ∈ activeReference Z Y :=
  (erasedBackwardWitness Z Q hQ
    (projectedFiniteRunFirstIndex Z Q hnil i)
    ((projectedFiniteRunFirstIndex_direction Z Q hnil i).trans hd)).owner_mem

theorem projectedFiniteRunBackwardOwner_isSubpath
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hY : Gamma.IsWarp Y)
    (hnil : (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps ≠ [])
    (i : Fin (projectedFiniteTraceInput Z Q hnil).runs.length)
    (hd : (projectedFiniteTraceInput Z Q hnil).runDirection i = .backward) :
    ((projectedFiniteTraceInput Z Q hnil).projectedRun i).link.path.IsSubpathOf
      (projectedFiniteRunBackwardOwner Z Q hQ hnil i hd) := by
  let E := (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute
  let S := projectedFiniteTraceInput Z Q hnil
  let j : Fin (S.runs.length - 1 + 1) := Fin.cast S.runCount_eq.symm i
  have hji : S.runIndex j = i := Fin.ext rfl
  have hlink : (S.projectedRun i).link ∈
      (finiteTraceCompression Z Q).path.links := by
    rw [finiteTraceCompression_path_eq_of_steps_ne_nil Z Q hnil]
    change (S.projectedRun i).link ∈ S.toFiniteRunWalk.toFiniteTrace.links
    rw [S.toFiniteRunWalk.toFiniteTrace_links]
    refine ⟨j, ?_⟩
    change (S.projectedRun i).link = (S.projectedRun (S.runIndex j)).link
    rw [hji]
  have hlinkdir : (S.projectedRun i).link.direction = .backward :=
    (S.projectedRun_direction i).trans hd
  let P := compressedBackwardOwner Z Q hQ hY
    (S.projectedRun i).link hlink hlinkdir
  have hPmem : P ∈ activeReference Z Y :=
    compressedBackwardOwner_mem Z Q hQ hY _ hlink hlinkdir
  have hPsub : (S.projectedRun i).link.path.IsSubpathOf P :=
    compressedBackwardOwner_isSubpath Z Q hQ hY _ hlink hlinkdir
  let n := projectedFiniteRunFirstIndex Z Q hnil i
  have hndir : (E.steps.get n).direction = .backward := by
    exact (projectedFiniteRunFirstIndex_direction Z Q hnil i).trans hd
  let A := erasedBackwardWitness Z Q hQ n hndir
  have hpos : 0 < (S.runs.get i).length :=
    List.length_pos_iff_ne_nil.2 (S.run_ne_nil (List.get_mem _ i))
  have hedgeLink : (E.steps.get n).edge ∈
      (S.projectedRun i).link.path.edgeSet := by
    rw [S.projectedRun_edgeSet_eq_backward i hd]
    refine ⟨0, hpos, ?_⟩
    have heq := E.step_edge_eq_routeVertices_backward n hndir
    change (E.steps.get n).edge =
      (E.routeVertex (n.1 + 1), E.routeVertex n.1)
    exact heq
  have hedgeP : (E.steps.get n).edge ∈ P.edgeSet := hPsub.2 hedgeLink
  have hPA : P = (Sum.inl A.owner : Gamma.DPath) := by
    apply DWeb.IsWarp.eq_of_mem_support (activeReference_isWarp Z hY)
      hPmem A.owner_mem
    · exact (P.edgeSet_subset_support_prod hedgeP).1
    · exact (A.owner.edgeSet_subset_support_prod A.step_edge_mem).1
  change (S.projectedRun i).link.path.IsSubpathOf
    (Sum.inl A.owner : Gamma.DPath)
  rw [← hPA]
  exact hPsub

theorem projectedFiniteRunFirst_source_eq_of_owner_eq
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hlast : Q.lastLink.direction = .forward)
    (hnil : (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps ≠ [])
    (i j : Fin (projectedFiniteTraceInput Z Q hnil).runs.length)
    (hi : (projectedFiniteTraceInput Z Q hnil).runDirection i = .backward)
    (hj : (projectedFiniteTraceInput Z Q hnil).runDirection j = .backward)
    (howner : projectedFiniteRunBackwardOwner Z Q hQ hnil i hi =
      projectedFiniteRunBackwardOwner Z Q hQ hnil j hj) :
    erasedSourceLinkIndex Z Q (projectedFiniteRunFirstIndex Z Q hnil i) =
      erasedSourceLinkIndex Z Q (projectedFiniteRunFirstIndex Z Q hnil j) := by
  let ni := projectedFiniteRunFirstIndex Z Q hnil i
  let nj := projectedFiniteRunFirstIndex Z Q hnil j
  have hdi :
      ((projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.get ni).direction =
        .backward :=
    (projectedFiniteRunFirstIndex_direction Z Q hnil i).trans hi
  have hdj :
      ((projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps.get nj).direction =
        .backward :=
    (projectedFiniteRunFirstIndex_direction Z Q hnil j).trans hj
  let A := erasedBackwardWitness Z Q hQ ni hdi
  let B := erasedBackwardWitness Z Q hQ nj hdj
  have hAB : A.owner = B.owner := by
    have hsum : (Sum.inl A.owner : Gamma.DPath) = Sum.inl B.owner := by
      simpa [projectedFiniteRunBackwardOwner, ni, nj, A, B] using howner
    exact Sum.inl.inj hsum
  apply Q.backward_indices_eq_of_common_finite_owner_of_last_forward
    hQ.isSafe hlast A.source_direction B.source_direction
      ⟨A.owner, A.owner_mem, rfl⟩ A.source_subpath
  simpa [hAB] using B.source_subpath

/-- Canonical reference ownership is injective on compressed backward runs. -/
theorem projectedFiniteRunBackwardOwner_injective
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hlast : Q.lastLink.direction = .forward)
    (hnil : (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps ≠ [])
    (i j : Fin (projectedFiniteTraceInput Z Q hnil).runs.length)
    (hi : (projectedFiniteTraceInput Z Q hnil).runDirection i = .backward)
    (hj : (projectedFiniteTraceInput Z Q hnil).runDirection j = .backward)
    (howner : projectedFiniteRunBackwardOwner Z Q hQ hnil i hi =
      projectedFiniteRunBackwardOwner Z Q hQ hnil j hj) :
    i = j := by
  let S := projectedFiniteTraceInput Z Q hnil
  let tag : Fin S.lastEdge → Fin (Q.lastIndex + 1) :=
    erasedSourceLinkIndex Z Q
  have htag : Monotone tag := by
    intro a b hab
    exact erasedSourceLinkIndex_mono Z Q hab
  have htagDirection : ∀ k,
      (Q.link (tag k)).direction = S.colour k := by
    intro k
    exact (erasedSourceLinkIndex_direction Z Q k).symm
  apply S.run_eq_of_backward_of_firstTag_eq tag htag
    (fun k ↦ (Q.link k).direction) htagDirection i j
  have hsource := projectedFiniteRunFirst_source_eq_of_owner_eq
    Z Q hQ hlast hnil i j hi hj howner
  change erasedSourceLinkIndex Z Q
      (projectedFiniteRunFirstIndex Z Q hnil i) =
    erasedSourceLinkIndex Z Q
      (projectedFiniteRunFirstIndex Z Q hnil j)
  exact hsource

theorem compressedBackwardOwner_eq_projectedFiniteRunBackwardOwner
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hY : Gamma.IsWarp Y)
    (hnil : (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute.steps ≠ [])
    (i : Fin (projectedFiniteTraceInput Z Q hnil).runs.length)
    (hd : (projectedFiniteTraceInput Z Q hnil).runDirection i = .backward) :
    let S := projectedFiniteTraceInput Z Q hnil
    let j : Fin (S.runs.length - 1 + 1) := Fin.cast S.runCount_eq.symm i
    let l := (S.projectedRun i).link
    let hl : l ∈ (finiteTraceCompression Z Q).path.links := by
      rw [finiteTraceCompression_path_eq_of_steps_ne_nil Z Q hnil]
      change l ∈ S.toFiniteRunWalk.toFiniteTrace.links
      rw [S.toFiniteRunWalk.toFiniteTrace_links]
      exact ⟨j, by change l = (S.projectedRun (S.runIndex j)).link; congr 2⟩
    let hld : l.direction = .backward := (S.projectedRun_direction i).trans hd
    compressedBackwardOwner Z Q hQ hY l hl hld =
      projectedFiniteRunBackwardOwner Z Q hQ hnil i hd := by
  let S := projectedFiniteTraceInput Z Q hnil
  let j : Fin (S.runs.length - 1 + 1) := Fin.cast S.runCount_eq.symm i
  let l := (S.projectedRun i).link
  have hji : S.runIndex j = i := Fin.ext rfl
  let hl : l ∈ (finiteTraceCompression Z Q).path.links := by
    rw [finiteTraceCompression_path_eq_of_steps_ne_nil Z Q hnil]
    change l ∈ S.toFiniteRunWalk.toFiniteTrace.links
    rw [S.toFiniteRunWalk.toFiniteTrace_links]
    exact ⟨j, by change l = (S.projectedRun (S.runIndex j)).link; rw [hji]⟩
  let hld : l.direction = .backward := (S.projectedRun_direction i).trans hd
  let P := compressedBackwardOwner Z Q hQ hY l hl hld
  let A := projectedFiniteRunBackwardOwner Z Q hQ hnil i hd
  have hPmem : P ∈ activeReference Z Y :=
    compressedBackwardOwner_mem Z Q hQ hY l hl hld
  have hAmem : A ∈ activeReference Z Y :=
    projectedFiniteRunBackwardOwner_mem Z Q hQ hnil i hd
  have hPsub : l.path.IsSubpathOf P :=
    compressedBackwardOwner_isSubpath Z Q hQ hY l hl hld
  have hAsub : l.path.IsSubpathOf A := by
    exact projectedFiniteRunBackwardOwner_isSubpath Z Q hQ hY hnil i hd
  obtain ⟨t, ht⟩ := FinitePath.exists_edge_from_of_mem_of_ne_finish
    l.path l.path.start_mem_support l.nontrivial
  apply DWeb.IsWarp.eq_of_mem_support (activeReference_isWarp Z hY)
    hPmem hAmem
  · exact (P.edgeSet_subset_support_prod (hPsub.2 ht)).1
  · exact (A.edgeSet_subset_support_prod (hAsub.2 ht)).1

/-- Unique owner provenance for every backward link of the finite projected
compression. -/
noncomputable def finiteTraceCompression_backwardProvenance
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hY : Gamma.IsWarp Y)
    (hlast : Q.lastLink.direction = .forward) :
    (finiteTraceCompression Z Q).path.BackwardLinkProvenance
      (activeReference Z Y) where
  owner := compressedBackwardOwner Z Q hQ hY
  owner_mem := compressedBackwardOwner_mem Z Q hQ hY
  isSubpath := compressedBackwardOwner_isSubpath Z Q hQ hY
  owner_unique := by
    intro l hl hld r hr hrd howner
    let E := (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute
    by_cases hnil : E.steps = []
    · have : l ∈ (AltPath.trivial (project Q.initial)).links := by
        simpa [finiteTraceCompression, ErasedSignedRoute.compressionOfValid,
          E, hnil] using hl
      simpa using this
    · let S := projectedFiniteTraceInput Z Q hnil
      rw [finiteTraceCompression_path_eq_of_steps_ne_nil Z Q hnil] at hl hr
      change l ∈ S.toFiniteRunWalk.toFiniteTrace.links at hl
      change r ∈ S.toFiniteRunWalk.toFiniteTrace.links at hr
      rw [S.toFiniteRunWalk.toFiniteTrace_links] at hl hr
      rcases hl with ⟨i, rfl⟩
      rcases hr with ⟨j, rfl⟩
      let ri := S.runIndex i
      let rj := S.runIndex j
      have hri : S.runDirection ri = .backward := by
        exact (S.toFiniteRunWalk_run_direction i).symm.trans hld
      have hrj : S.runDirection rj = .backward := by
        exact (S.toFiniteRunWalk_run_direction j).symm.trans hrd
      have hci := compressedBackwardOwner_eq_projectedFiniteRunBackwardOwner
        Z Q hQ hY hnil ri hri
      have hcj := compressedBackwardOwner_eq_projectedFiniteRunBackwardOwner
        Z Q hQ hY hnil rj hrj
      have hcanonical :
          projectedFiniteRunBackwardOwner Z Q hQ hnil ri hri =
            projectedFiniteRunBackwardOwner Z Q hQ hnil rj hrj := by
        exact hci.symm.trans (howner.trans hcj)
      have hrun : ri = rj :=
        projectedFiniteRunBackwardOwner_injective Z Q hQ hlast hnil
          ri rj hri hrj hcanonical
      have hval : ri.1 = rj.1 := congrArg (fun x : Fin S.runs.length ↦ x.1) hrun
      change i.1 = j.1 at hval
      have hij : i = j := Fin.ext hval
      subst j
      rfl

/-- Index-friendly form of the finite compressed backward provenance. -/
noncomputable def finiteTraceCompression_indexedBackwardProvenance
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hY : Gamma.IsWarp Y)
    (hlast : Q.lastLink.direction = .forward) :
    (finiteTraceCompression Z Q).path.IndexedBackwardProvenance
      (activeReference Z Y)
      {l : Link Gamma.graph //
        l ∈ (finiteTraceCompression Z Q).path.links} := by
  let P := finiteTraceCompression_backwardProvenance Z Q hQ hY hlast
  refine {
    link := Subtype.val
    links_eq_range := ?_
    owner := fun i hd ↦ P.owner i.1 i.2 hd
    owner_mem := fun i hd ↦ P.owner_mem i.1 i.2 hd
    isSubpath := fun i hd ↦ P.isSubpath i.1 i.2 hd
    owner_unique := ?_ }
  · ext l
    constructor
    · intro hl
      exact ⟨⟨l, hl⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.2
  · intro i j hi hj howner
    exact P.owner_unique i.1 i.2 hi j.1 j.2 hj howner

/-- The finite connector-deleted projection is bracket safe against the
peeled active reference. -/
theorem finiteTraceCompression_isBracketSafe_active
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hlast : Q.lastLink.direction = .forward)
    (hinitial : project Q.initial ∉
      Gamma.vertexSet (activeReference Z Y))
    (hterminal : project Q.terminal ∉
      Gamma.vertexSet (activeReference Z Y)) :
    IsBracketSafe Z.edgeWarp (activeReference Z Y)
      (finiteTraceCompression Z Q).path :=
  (finiteTraceCompression_isBracketAlternating Z Q hQ hY
      hinitial hterminal).isBracketSafe_of_backwardProvenance
    Z.edgeWarp_isWarp (activeReference_isWarp Z hY) hZfinite
    (finiteTraceCompression_backwardProvenance Z Q hQ hY hlast)

/-- The exact finite selected branch consumed by the common fractured
projection compiler. -/
noncomputable def selectedFiniteProjection
    (Z : FracturedWarp Gamma)
    (hboundary : BoundaryAligned Z.paths Y)
    (hY : Gamma.IsWarp Y)
    (hZfinite : Gamma.HasFiniteCharacter Z.edgeWarp)
    (hYfinite : Gamma.HasFiniteCharacter Y)
    (B : BracketSimultaneousAssignment
      (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)))
    (z : {x // x ∈ Gamma.initialSet (activePaths Z) \
      Gamma.initialSet Y})
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQselected : B.assigned (toLiftedSource Z hYfinite z) = .finite Q) :
    AssignedPathProjection (Y := Y) Z
      (B.assigned (toLiftedSource Z hYfinite z)) z.1 := by
  have hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q) := by
    have h := B.bracket_safe (toLiftedSource Z hYfinite z)
    rw [hQselected] at h
    exact h
  have hlast : Q.lastLink.direction = .forward :=
    selected_finite_last_direction_forward Z hYfinite B z Q hQselected
  have hinitialY : project Q.initial ∉ Gamma.vertexSet Y := by
    have h := selected_project_initial_outside Z hboundary hYfinite B z
    rw [hQselected] at h
    exact h
  have hselectedTerminal :
      (B.assigned (toLiftedSource Z hYfinite z)).terminal? =
        some Q.terminal := by
    rw [hQselected]
    rfl
  have hterminalData := selected_finite_terminal_data Z hYfinite B z
    hselectedTerminal
  have hterminalY : project Q.terminal ∉ Gamma.vertexSet Y :=
    hterminalData.2.2
  have hinitialActive : project Q.initial ∉
      Gamma.vertexSet (activeReference Z Y) := by
    intro hx
    rcases hx with ⟨p, hp, hpx⟩
    exact hinitialY ⟨p, activeReference_subset Z Y hp, hpx⟩
  have hterminalActive : project Q.terminal ∉
      Gamma.vertexSet (activeReference Z Y) := by
    intro hx
    rcases hx with ⟨p, hp, hpx⟩
    exact hterminalY ⟨p, activeReference_subset Z Y hp, hpx⟩
  have hactive : IsBracketSafe Z.edgeWarp (activeReference Z Y)
      (finiteTraceCompression Z Q).path :=
    finiteTraceCompression_isBracketSafe_active Z Q hQ hY hZfinite
      hlast hinitialActive hterminalActive
  have hfull : IsBracketSafe Z.edgeWarp Y
      (finiteTraceCompression Z Q).path :=
    IsBracketSafe.of_reference_subwarp hactive hY
      (activeReference_subset Z Y)
      (fun _ ↦ by
        rw [finiteTraceCompression_initial]
        exact hinitialY)
      (fun t ht _ ↦ by
        rw [finiteTraceCompression_terminal] at ht
        have ht' : t = project Q.terminal := Option.some.inj ht.symm
        simpa [ht'] using hterminalY)
  refine {
    path := (finiteTraceCompression Z Q).path
    starts_at := ?_
    bracket_safe := hfull
    safe := hfull.isSafe
    leaving := ?_
    maximal := ?_
    terminal_lift := ?_ }
  · rw [finiteTraceCompression_initial]
    have h := selected_project_initial Z hYfinite B z
    rw [hQselected] at h
    exact h
  · right
    exact ⟨project Q.terminal, finiteTraceCompression_terminal Z Q,
      hterminalY⟩
  · right
    exact ⟨project Q.terminal, hterminalData.2,
      finiteTraceCompression_terminal Z Q⟩
  · intro v hv
    rw [hQselected]
    exact finiteTraceCompression_terminal_lift Z Q hv

end FracturedAssignmentPeel
end LinkageBlueprint
end Blueprint
end Erdos599
