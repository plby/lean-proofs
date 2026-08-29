/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FracturedProjectionEndpoints
import ErdosProblems.Erdos599.GroundingErasedDecode

/-!
# Finite connector-deletion projection for fractured assignments

This is the finite half of the occurrence-splitting construction used in
Remark 4.20.  A finite alternating path in the duplicated graph is traversed
link by link.  Each genuine projected edge is retained with its traversal
direction, while an edge between two role copies of the same original vertex
is contracted.  Chronological erasure and maximal-run compression then give
an honest finite alternating path in the original graph.
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

local instance fracturedProjectionDecidableEq : DecidableEq V :=
  Classical.decEq V

/-! ## Connector-deleting traversal of one directed walk -/

/-- Project a directed walk in its forward traversal order, deleting exactly
the steps whose two endpoints have the same projection. -/
def projectedForwardSteps (Z : FracturedWarp Gamma) :
    {a b : Vertex V} -> Walk (web Gamma Z).graph a b ->
      List (SignedEdge V)
  | _, _, .nil => []
  | _, _, @Walk.cons _ _ a b _ h q =>
      if project a = project b then projectedForwardSteps Z q
      else SignedEdge.forward (project a, project b) ::
        projectedForwardSteps Z q

/-- Project a directed walk against its orientation.  The list is in
traversal order, so the last directed edge of the walk is emitted first. -/
def projectedBackwardSteps (Z : FracturedWarp Gamma) :
    {a b : Vertex V} -> Walk (web Gamma Z).graph a b ->
      List (SignedEdge V)
  | _, _, .nil => []
  | _, _, @Walk.cons _ _ a b _ h q =>
      projectedBackwardSteps Z q ++
        if project a = project b then []
        else [SignedEdge.backward (project a, project b)]

theorem projectedForwardSteps_runs (Z : FracturedWarp Gamma)
    {a b : Vertex V} (q : Walk (web Gamma Z).graph a b) :
    RunsFromTo (project a) (project b) (projectedForwardSteps Z q) := by
  induction q with
  | nil => exact .nil _
  | @cons a b c h q ih =>
      by_cases hab : project a = project b
      · simpa [projectedForwardSteps, hab] using ih
      · simp only [projectedForwardSteps, hab, ↓reduceIte]
        exact .cons (SignedEdge.forward (project a, project b)) ih

theorem projectedBackwardSteps_runs (Z : FracturedWarp Gamma)
    {a b : Vertex V} (q : Walk (web Gamma Z).graph a b) :
    RunsFromTo (project b) (project a) (projectedBackwardSteps Z q) := by
  induction q with
  | nil => exact .nil _
  | @cons a b c h q ih =>
      by_cases hab : project a = project b
      · simpa [projectedBackwardSteps, hab] using ih
      · simp only [projectedBackwardSteps, hab, ↓reduceIte]
        exact ih.append (RunsFromTo.singleton
          (SignedEdge.backward (project a, project b)))

theorem projectedForwardSteps_mem
    (Z : FracturedWarp Gamma) {a b : Vertex V}
    (q : Walk (web Gamma Z).graph a b) {s : SignedEdge V}
    (hs : s ∈ projectedForwardSteps Z q) :
    s.direction = .forward ∧ SignedEdge.Valid (Gamma := Gamma) s ∧
      s.edge.1 ≠ s.edge.2 ∧
      ∃ e ∈ q.edgeSet, s.edge = (project e.1, project e.2) := by
  induction q with
  | nil => simp [projectedForwardSteps] at hs
  | @cons a b c h q ih =>
      by_cases hab : project a = project b
      · rcases ih (by simpa [projectedForwardSteps, hab] using hs) with
          ⟨hdir, hvalid, hne, e, he, hedge⟩
        exact ⟨hdir, hvalid, hne, e, by simp [Walk.edgeSet, he], hedge⟩
      · simp only [projectedForwardSteps, hab, ↓reduceIte,
          List.mem_cons] at hs
        rcases hs with rfl | hs
        · refine ⟨rfl, ?_, hab, (by
            refine ⟨(a, b), ?_, rfl⟩
            simp [Walk.edgeSet])⟩
          exact (graph_adj_projects_or_contracts Z h).resolve_right hab
        · rcases ih hs with ⟨hdir, hvalid, hne, e, he, hedge⟩
          exact ⟨hdir, hvalid, hne, e, by simp [Walk.edgeSet, he], hedge⟩

theorem projectedBackwardSteps_mem
    (Z : FracturedWarp Gamma) {a b : Vertex V}
    (q : Walk (web Gamma Z).graph a b) {s : SignedEdge V}
    (hs : s ∈ projectedBackwardSteps Z q) :
    s.direction = .backward ∧ SignedEdge.Valid (Gamma := Gamma) s ∧
      s.edge.1 ≠ s.edge.2 ∧
      ∃ e ∈ q.edgeSet, s.edge = (project e.1, project e.2) := by
  induction q with
  | nil => simp [projectedBackwardSteps] at hs
  | @cons a b c h q ih =>
      by_cases hab : project a = project b
      · rcases ih (by simpa [projectedBackwardSteps, hab] using hs) with
          ⟨hdir, hvalid, hne, e, he, hedge⟩
        exact ⟨hdir, hvalid, hne, e, by simp [Walk.edgeSet, he], hedge⟩
      · simp only [projectedBackwardSteps, hab, ↓reduceIte,
          List.mem_append, List.mem_singleton] at hs
        rcases hs with hs | rfl
        · rcases ih hs with ⟨hdir, hvalid, hne, e, he, hedge⟩
          exact ⟨hdir, hvalid, hne, e, by simp [Walk.edgeSet, he], hedge⟩
        · refine ⟨rfl, ?_, hab, (by
            refine ⟨(a, b), ?_, rfl⟩
            simp [Walk.edgeSet])⟩
          exact (graph_adj_projects_or_contracts Z h).resolve_right hab

/-! ## Traversing links and finite traces -/

/-- The connector-deleted signed traversal of one alternating link. -/
def projectedLinkSteps (Z : FracturedWarp Gamma)
    (l : Link (web Gamma Z).graph) : List (SignedEdge V) :=
  match l.direction with
  | .forward => projectedForwardSteps Z l.path.walk
  | .backward => projectedBackwardSteps Z l.path.walk

theorem projectedLinkSteps_runs (Z : FracturedWarp Gamma)
    (l : Link (web Gamma Z).graph) :
    RunsFromTo (project l.entry) (project l.exit)
      (projectedLinkSteps Z l) := by
  cases hdir : l.direction with
  | forward =>
      simpa [projectedLinkSteps, Link.entry, Link.exit, hdir] using
        projectedForwardSteps_runs Z l.path.walk
  | backward =>
      simpa [projectedLinkSteps, Link.entry, Link.exit, hdir] using
        projectedBackwardSteps_runs Z l.path.walk

theorem projectedLinkSteps_mem (Z : FracturedWarp Gamma)
    (l : Link (web Gamma Z).graph) {s : SignedEdge V}
    (hs : s ∈ projectedLinkSteps Z l) :
    s.direction = l.direction ∧ SignedEdge.Valid (Gamma := Gamma) s ∧
      s.edge.1 ≠ s.edge.2 ∧
      ∃ e ∈ l.path.edgeSet, s.edge = (project e.1, project e.2) := by
  cases hdir : l.direction with
  | forward =>
      simp only [projectedLinkSteps, hdir] at hs
      rcases projectedForwardSteps_mem Z l.path.walk hs with
        ⟨hsdir, hsvalid, hsne, e, he, hedge⟩
      exact ⟨hsdir, hsvalid, hsne, e, he, hedge⟩
  | backward =>
      simp only [projectedLinkSteps, hdir] at hs
      rcases projectedBackwardSteps_mem Z l.path.walk hs with
        ⟨hsdir, hsvalid, hsne, e, he, hedge⟩
      exact ⟨hsdir, hsvalid, hsne, e, he, hedge⟩

/-- Flatten a list of alternating links in traversal order. -/
def projectedChainSteps (Z : FracturedWarp Gamma)
    (links : List (Link (web Gamma Z).graph)) : List (SignedEdge V) :=
  links.flatMap (projectedLinkSteps Z)

private theorem projectedChainSteps_runs
    (Z : FracturedWarp Gamma)
    (l : Link (web Gamma Z).graph)
    (ls : List (Link (web Gamma Z).graph))
    (hc : List.IsChain (fun p q => p.exit = q.entry) (l :: ls)) :
    RunsFromTo (project l.entry)
      (project ((l :: ls).getLast (by simp)).exit)
      (projectedChainSteps Z (l :: ls)) := by
  induction ls generalizing l with
  | nil => simpa [projectedChainSteps] using projectedLinkSteps_runs Z l
  | cons r rs ih =>
      have hlr : l.exit = r.entry := by
        simpa only [List.head?_cons, Option.mem_def] using
          (List.isChain_cons.mp hc).1 r (by simp)
      have htail : List.IsChain (fun p q => p.exit = q.entry) (r :: rs) :=
        (List.isChain_cons.mp hc).2
      rw [projectedChainSteps, List.flatMap_cons]
      rw [List.getLast_cons (by simp : r :: rs ≠ [])]
      exact (projectedLinkSteps_runs Z l).append (by
        rw [hlr]
        exact ih r htail)

/-- The indexed links of a finite trace, as an ordinary list. -/
def finiteTraceLinks (Q : FiniteTrace (web Gamma Z).graph) :
    List (Link (web Gamma Z).graph) :=
  List.ofFn Q.link

@[simp] theorem finiteTraceLinks_length
    (Q : FiniteTrace (web Gamma Z).graph) :
    (finiteTraceLinks (Z := Z) Q).length = Q.lastIndex + 1 := by
  simp [finiteTraceLinks]

theorem finiteTraceLinks_ne_nil
    (Q : FiniteTrace (web Gamma Z).graph) :
    finiteTraceLinks (Z := Z) Q ≠ [] := by
  intro h
  have hh := congrArg List.length h
  simp [finiteTraceLinks] at hh

@[simp] theorem finiteTraceLinks_head
    (Q : FiniteTrace (web Gamma Z).graph) :
    (finiteTraceLinks (Z := Z) Q).head
      (finiteTraceLinks_ne_nil (Z := Z) Q) = Q.firstLink := by
  rw [List.head_eq_getElem]
  simp [finiteTraceLinks, FiniteTrace.firstLink]

@[simp] theorem finiteTraceLinks_getLast
    (Q : FiniteTrace (web Gamma Z).graph) :
    (finiteTraceLinks (Z := Z) Q).getLast
      (finiteTraceLinks_ne_nil (Z := Z) Q) = Q.lastLink := by
  have hne : List.ofFn Q.link ≠ [] := by
    intro h
    have hh := congrArg List.length h
    simp at hh
  calc
    (finiteTraceLinks (Z := Z) Q).getLast
        (finiteTraceLinks_ne_nil (Z := Z) Q) =
        (List.ofFn Q.link).getLast hne := by rfl
    _ = Q.lastLink := by
      rw [List.getLast_ofFn]
      apply congrArg Q.link
      apply Fin.ext
      simp [FiniteTrace.lastLink]

theorem finiteTraceLinks_isChain
    (Q : FiniteTrace (web Gamma Z).graph) :
    List.IsChain (fun p q => p.exit = q.entry)
      (finiteTraceLinks (Z := Z) Q) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  rw [finiteTraceLinks_length] at hi
  have hiLast : i < Q.lastIndex := by omega
  have hi0 : i < (finiteTraceLinks (Z := Z) Q).length := by
    rw [finiteTraceLinks_length]
    omega
  have hi1 : i + 1 < (finiteTraceLinks (Z := Z) Q).length := by
    rw [finiteTraceLinks_length]
    omega
  have hleft : (finiteTraceLinks (Z := Z) Q)[i] =
      Q.link (Fin.castSucc ⟨i, hiLast⟩) := by
    simp only [finiteTraceLinks, List.getElem_ofFn]
    apply congrArg Q.link
    apply Fin.ext
    rfl
  have hright : (finiteTraceLinks (Z := Z) Q)[i + 1] =
      Q.link (Fin.succ ⟨i, hiLast⟩) := by
    simp only [finiteTraceLinks, List.getElem_ofFn]
    apply congrArg Q.link
    apply Fin.ext
    rfl
  rw [hleft, hright]
  exact Q.joins ⟨i, hiLast⟩

/-- The connector-deleted signed traversal of a finite alternating trace. -/
def projectedFiniteTraceSteps (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph) : List (SignedEdge V) :=
  projectedChainSteps Z (finiteTraceLinks (Z := Z) Q)

theorem projectedFiniteTraceSteps_runs (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph) :
    RunsFromTo (project Q.initial) (project Q.terminal)
      (projectedFiniteTraceSteps Z Q) := by
  let links := finiteTraceLinks (Z := Z) Q
  have hne : links ≠ [] := by
    simpa [links] using finiteTraceLinks_ne_nil (Z := Z) Q
  have hcons : links.head hne :: links.tail = links :=
    List.cons_head_tail hne
  have hchain := finiteTraceLinks_isChain (Z := Z) Q
  have hruns := projectedChainSteps_runs Z (links.head hne) links.tail (by
    rw [hcons]
    exact hchain)
  have hstart : links.head hne = Q.firstLink := by
    exact finiteTraceLinks_head (Z := Z) Q
  have hend : (links.head hne :: links.tail).getLast
      (List.cons_ne_nil _ _) =
      Q.lastLink := by
    calc
      (links.head hne :: links.tail).getLast (List.cons_ne_nil _ _) =
          links.getLast hne :=
            List.getLast_congr (List.cons_ne_nil _ _) hne hcons
      _ = Q.lastLink := by
        exact finiteTraceLinks_getLast (Z := Z) Q
  have hsteps : projectedChainSteps Z (links.head hne :: links.tail) =
      projectedFiniteTraceSteps Z Q := by
    rw [hcons]
    rfl
  have hstartProjected : project (links.head hne).entry =
      project Q.firstLink.entry :=
    congrArg (fun l => project l.entry) hstart
  have hendProjected :
      project ((links.head hne :: links.tail).getLast
        (List.cons_ne_nil _ _)).exit = project Q.lastLink.exit :=
    congrArg (fun l => project l.exit) hend
  rw [hstartProjected, hendProjected, hsteps] at hruns
  simpa [FiniteTrace.initial, FiniteTrace.terminal] using hruns

theorem projectedFiniteTraceSteps_mem
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph) {s : SignedEdge V}
    (hs : s ∈ projectedFiniteTraceSteps Z Q) :
    SignedEdge.Valid (Gamma := Gamma) s ∧
      s.edge.1 ≠ s.edge.2 ∧
      ∃ l ∈ (AltPath.finite Q).links,
        s.direction = l.direction ∧
          ∃ e ∈ l.path.edgeSet,
            s.edge = (project e.1, project e.2) := by
  simp only [projectedFiniteTraceSteps, projectedChainSteps,
    List.mem_flatMap] at hs
  rcases hs with ⟨l, hl, hs⟩
  rcases projectedLinkSteps_mem Z l hs with
    ⟨hdir, hvalid, hne, e, he, hedge⟩
  refine ⟨hvalid, hne, l, ?_, hdir, e, he, hedge⟩
  change l ∈ FiniteTrace.links Q
  change l ∈ List.ofFn Q.link at hl
  rcases List.mem_ofFn.mp hl with ⟨i, hi⟩
  exact ⟨i, hi⟩

/-! ## Projecting the two lifted path families -/

private theorem mem_mapWalk_edgeSet_projects
    {A B : Type u} {D : Digraph A} {E : Digraph B}
    (f : A → B) (g : B → A) (hgf : ∀ x, g (f x) = x)
    (hf : ∀ {x y}, D.Adj x y → E.Adj (f x) (f y))
    {a b : A} (q : Walk D a b) {e : B × B}
    (he : e ∈ (FracturedDuplication.mapWalk f hf q).edgeSet) :
    (g e.1, g e.2) ∈ q.edgeSet := by
  induction q with
  | nil => simp [FracturedDuplication.mapWalk, Walk.edgeSet] at he
  | @cons a b c h q ih =>
      simp only [FracturedDuplication.mapWalk, Walk.edgeSet_cons,
        Set.mem_union, Set.mem_singleton_iff] at he ⊢
      rcases he with rfl | he
      · left
        simp [hgf]
      · exact Or.inr (ih he)

/-- Every edge of an occurrence-lifted path projects to the corresponding
edge of its original fractured member. -/
theorem projected_edge_mem_of_mem_liftPath
    (Z : FracturedWarp Gamma) (p : Gamma.DPath)
    {e : Vertex V × Vertex V} (he : e ∈ (liftPath Z p).edgeSet) :
    (project e.1, project e.2) ∈ p.edgeSet := by
  rcases p with p | r
  · exact mem_mapWalk_edgeSet_projects
      (occurrence Z (Sum.inl p)) project
      (project_occurrence Z (Sum.inl p))
      (web_adj_occurrence Z (Sum.inl p)) p.walk he
  · rcases he with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa [liftPath, FracturedDuplication.mapPath,
      FracturedDuplication.mapRay] using congrArg
        (fun e : Vertex V × Vertex V => (project e.1, project e.2)) hn

private theorem vertexWalk_edges_contract
    (Z : FracturedWarp Gamma) (x : V) {e : Vertex V × Vertex V}
    (he : e ∈ (vertexWalk Z x).edgeSet) : project e.1 = project e.2 := by
  have hs := (vertexWalk Z x).edgeSet_subset_support_prod he
  rw [support_vertexWalk] at hs
  exact (mem_vertexBlock_project Z hs.1).trans
    (mem_vertexBlock_project Z hs.2).symm

/-- Every nonconnector edge of an expanded reference walk projects to an
edge of the original reference walk. -/
private theorem projected_edge_mem_of_mem_expandWalk
    (Z : FracturedWarp Gamma) {a b : V} (q : Walk Gamma.graph a b)
    {e : Vertex V × Vertex V} (he : e ∈ (expandWalk Z q).edgeSet)
    (hne : project e.1 ≠ project e.2) :
    (project e.1, project e.2) ∈ q.edgeSet := by
  induction q with
  | nil =>
      exact False.elim (hne (vertexWalk_edges_contract Z _ he))
  | @cons a b c h q ih =>
      rw [expandWalk, Alternating.RunCompressor.walk_edgeSet_append] at he
      rcases he with hblock | hrest
      · exact False.elim (hne (vertexWalk_edges_contract Z _ hblock))
      · simp only [Walk.edgeSet_cons, Set.mem_union,
          Set.mem_singleton_iff] at hrest ⊢
        rcases hrest with rfl | htail
        · left
          rfl
        · exact Or.inr (ih htail)

/-- Every retained edge of an expanded reference path projects to an edge of
the original reference member. -/
theorem projected_edge_mem_of_mem_expandFinitePath
    (Z : FracturedWarp Gamma) (p : FinitePath Gamma.graph)
    {e : Vertex V × Vertex V}
    (he : e ∈ (expandFinitePath Z p).edgeSet)
    (hne : project e.1 ≠ project e.2) :
    (project e.1, project e.2) ∈ p.edgeSet :=
  projected_edge_mem_of_mem_expandWalk Z p.walk he hne

/-! ## Raw directional provenance -/

theorem projectedFiniteTraceSteps_forward_on_edgeWarp
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    {s : SignedEdge V} (hs : s ∈ projectedFiniteTraceSteps Z Q)
    (hdir : s.direction = .forward) :
    s.edge ∈ familyEdges Z.edgeWarp := by
  rcases projectedFiniteTraceSteps_mem Z Q hs with
    ⟨_hvalid, _hne, l, hl, hsdir, e, he, hedge⟩
  have hldir : l.direction = .forward := hsdir.symm.trans hdir
  rcases hQ.isBracketAlternating.2 l hl hldir with
    ⟨P, hP, hsub⟩
  rcases hP with ⟨p, hp, rfl⟩
  have heLift : e ∈ (liftPath Z p).edgeSet := hsub.2 he
  have heOriginal := projected_edge_mem_of_mem_liftPath Z p heLift
  rw [hedge]
  rw [← Z.same_edges]
  simp only [Alternating.familyEdges, Set.mem_iUnion]
  exact ⟨p, hp.1, heOriginal⟩

theorem projectedFiniteTraceSteps_backward_on_activeReference
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    {s : SignedEdge V} (hs : s ∈ projectedFiniteTraceSteps Z Q)
    (hdir : s.direction = .backward) :
    s.edge ∈ familyEdges (activeReference Z Y) := by
  rcases projectedFiniteTraceSteps_mem Z Q hs with
    ⟨_hvalid, hsne, l, hl, hsdir, e, he, hedge⟩
  have hldir : l.direction = .backward := hsdir.symm.trans hdir
  rcases hQ.isAlternating.2.1 l hl hldir with ⟨P, hP, hsub⟩
  rcases hP with ⟨p, hp, rfl⟩
  have heExpanded : e ∈ (expandFinitePath Z p).edgeSet := hsub.2 he
  have hprojNe : project e.1 ≠ project e.2 := by
    simpa [hedge] using hsne
  have heOriginal :=
    projected_edge_mem_of_mem_expandFinitePath Z p heExpanded hprojNe
  rw [hedge]
  simp only [Alternating.familyEdges, Set.mem_iUnion]
  exact ⟨Sum.inl p, hp, heOriginal⟩

/-! ## Compression of the projected traversal -/

/-- The forward analogue of `compressionOfValid_backwardLinksOn`: every
maximal retained forward run is a fragment of one member of the indicated
warp.  This formulation is useful independently of fractured projection. -/
theorem compressionOfValid_forwardLinksOn
    {x y : V} {raw : List (SignedEdge V)}
    (E : ErasedSignedRoute x y raw)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s)
    {U : Set Gamma.DPath} (hU : Gamma.IsWarp U)
    (hforward : ∀ {s : SignedEdge V}, s ∈ E.steps →
      s.direction = .forward → s.edge ∈ Alternating.familyEdges U) :
    ∀ l ∈ (E.compressionOfValid hvalid).path.links,
      l.direction = .forward → IsFragmentOf l.path U := by
  classical
  by_cases hnil : E.steps = []
  · simp [ErasedSignedRoute.compressionOfValid, hnil]
  · let S := E.toFiniteInputOfValid hnil hvalid
    suffices h : ∀ l ∈ (AltPath.finite S.toFiniteRunWalk.toFiniteTrace).links,
        l.direction = .forward → IsFragmentOf l.path U by
      simpa [ErasedSignedRoute.compressionOfValid, hnil, S] using h
    intro l hl hdir
    change l ∈ S.toFiniteRunWalk.toFiniteTrace.links at hl
    rw [S.toFiniteRunWalk.toFiniteTrace_links] at hl
    rcases hl with ⟨i, rfl⟩
    have hrun : S.runDirection (S.runIndex i) = .forward := by
      exact (S.toFiniteRunWalk_run_direction i).symm.trans hdir
    apply SwitchingCore.finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
      hU (S.toFiniteRunWalk.run i).link.path
        (S.toFiniteRunWalk.run i).link.nontrivial
    intro e he
    change e ∈ (S.projectedRun (S.runIndex i)).link.path.edgeSet at he
    rw [S.projectedRun_edgeSet_eq_forward (S.runIndex i) hrun] at he
    rcases he with ⟨k, hk, rfl⟩
    let n : Fin E.steps.length :=
      ⟨Alternating.RunCompressor.runLower S.runs (S.runIndex i) + k,
        by
          change Alternating.RunCompressor.runLower S.runs (S.runIndex i) + k <
            S.lastEdge
          exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
            (S.runUpper_le_lastEdge (S.runIndex i))⟩
    have hcolour := S.colour_run_offset (S.runIndex i) hk
    have hstep : (E.steps.get n).direction = .forward :=
      hcolour.trans hrun
    have hedge := hforward (List.get_mem E.steps n) hstep
    rw [E.step_edge_eq_routeVertices_forward n hstep] at hedge
    exact hedge

/-- The canonical chronologically erased and run-compressed projection of a
finite upstairs trace. -/
noncomputable def finiteTraceCompression
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph) :
    ErasedSignedRoute.ErasedCompression (Gamma := Gamma)
      (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute :=
  let E := (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute
  E.compressionOfValid (fun {_s} hs ↦
    (projectedFiniteTraceSteps_mem Z Q (E.steps_sublist.subset hs)).1)

@[simp] theorem finiteTraceCompression_initial
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph) :
    (finiteTraceCompression Z Q).path.initial = project Q.initial :=
  (finiteTraceCompression Z Q).initial_eq

@[simp] theorem finiteTraceCompression_terminal
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph) :
    (finiteTraceCompression Z Q).path.terminal? = some (project Q.terminal) :=
  (finiteTraceCompression Z Q).terminal_eq

/-- The finite compressed terminal is the projection of the literal
upstairs terminal; this is the witness used to preserve terminal
injectivity when the per-source projections are assembled. -/
theorem finiteTraceCompression_terminal_lift
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph) {v : V}
    (hv : (finiteTraceCompression Z Q).path.terminal? = some v) :
    ∃ w : Vertex V, (AltPath.finite Q).terminal? = some w ∧
      project w = v := by
  refine ⟨Q.terminal, rfl, ?_⟩
  have h := finiteTraceCompression_terminal (Z := Z) Q
  rw [hv] at h
  exact Option.some.inj h.symm

/-- Every compressed backward link lies on the peeled reference warp. -/
theorem finiteTraceCompression_backwardLinksOn
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hY : Gamma.IsWarp Y) :
    BackwardLinksOn (activeReference Z Y) (finiteTraceCompression Z Q).path := by
  let E := (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute
  apply E.compressionOfValid_backwardLinksOn
    (fun {_s} hs ↦
      (projectedFiniteTraceSteps_mem Z Q (E.steps_sublist.subset hs)).1)
    (activeReference_isWarp Z hY)
  intro s hs hdir
  exact projectedFiniteTraceSteps_backward_on_activeReference Z Q hQ
    (E.steps_sublist.subset hs) hdir

/-- Every compressed forward link lies on the recombined honest warp. -/
theorem finiteTraceCompression_forwardLinksOn
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q)) :
    ∀ l ∈ (finiteTraceCompression Z Q).path.links,
      l.direction = .forward → IsFragmentOf l.path Z.edgeWarp := by
  let E := (projectedFiniteTraceSteps_runs Z Q).erasedSignedRoute
  apply compressionOfValid_forwardLinksOn E
    (fun {_s} hs ↦
      (projectedFiniteTraceSteps_mem Z Q (E.steps_sublist.subset hs)).1)
    Z.edgeWarp_isWarp
  intro s hs hdir
  exact projectedFiniteTraceSteps_forward_on_edgeWarp Z Q hQ
    (E.steps_sublist.subset hs) hdir

/-- Directional provenance and exposed projected endpoints give the literal
bracket-alternating certificate before the global interval clause is added. -/
theorem finiteTraceCompression_isBracketAlternating
    (Z : FracturedWarp Gamma)
    (Q : FiniteTrace (web Gamma Z).graph)
    (hQ : IsBracketSafe (activeLiftedPaths Z)
      (liftedReference Z (activeReference Z Y)) (.finite Q))
    (hY : Gamma.IsWarp Y)
    (hinitial : project Q.initial ∉
      Gamma.vertexSet (activeReference Z Y))
    (hterminal : project Q.terminal ∉
      Gamma.vertexSet (activeReference Z Y)) :
    IsBracketAlternating Z.edgeWarp (activeReference Z Y)
      (finiteTraceCompression Z Q).path := by
  refine ⟨⟨activeReference_isWarp Z hY,
    finiteTraceCompression_backwardLinksOn Z Q hQ hY, ?_, ?_⟩,
      finiteTraceCompression_forwardLinksOn Z Q hQ⟩
  · intro _hfirst
    rw [finiteTraceCompression_initial]
    exact hinitial
  · intro t ht _hlast
    rw [finiteTraceCompression_terminal] at ht
    have ht' : t = project Q.terminal := Option.some.inj ht.symm
    simpa [ht'] using hterminal

end FracturedAssignmentPeel
end LinkageBlueprint
end Blueprint
end Erdos599
