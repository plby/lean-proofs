/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeRealPartFinite
import ErdosProblems.Erdos599.ColouredSafeRealReach
import ErdosProblems.Erdos599.SourceRootedPathSelection
import ErdosProblems.Erdos599.SingularSafeCompletedMachine

/-!
# Direct source-rooted selection from an eventually completed native chain

The actual source-cover clauses rule out incoming real edges at original
sources. If every stage real terminal is eventually linked to the target,
the finite stage real components give finite target paths for all sources
ever represented. Left uniqueness of the real-edge union makes these paths
disjoint. Reference owners at unrepresented sources avoid the whole union,
so the source-cover clause survives at every individual old slice.

This final selection does not construct the fair chain, retain all auxiliary
vertices, or provide the proper intermediate-limit blueprints.
-/

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal DirectedPath Alternating ColouredSafeLocalTransactionRealLedger

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}} {I : Type v} [LinearOrder I]

/-- Only the actual chain observables needed for source-rooted selection.
The slice may change with the index. -/
structure RealStageChain (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (kappa : Cardinal.{u}) (I : Type v) [LinearOrder I] (frontier : I → Set V) where
  stage : I → Set (imaginaryWeb Y kappa).DPath
  warp : ∀ i, (imaginaryWeb Y kappa).IsWarp (stage i)
  covers_source : ∀ i, CoversSource (stage i) (frontier i)
  vertices_mono : Monotone (fun i ↦ (imaginaryWeb Y kappa).vertexSet (stage i))
  edges_mono : Monotone
    (fun i ↦ RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj (stage i))

namespace RealStageChain

variable {frontier : I → Set V}

def vertexUnion (C : RealStageChain Gamma Y kappa I frontier) : Set V :=
  ⋃ i, (imaginaryWeb Y kappa).vertexSet (C.stage i)

def edgeUnion (C : RealStageChain Gamma Y kappa I frontier) : Set (V × V) :=
  ⋃ i, RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj (C.stage i)

theorem stage_vertices_subset (C : RealStageChain Gamma Y kappa I frontier) (i : I) :
    (imaginaryWeb Y kappa).vertexSet (C.stage i) ⊆ C.vertexUnion :=
  Set.subset_iUnion (fun j ↦ (imaginaryWeb Y kappa).vertexSet (C.stage j)) i

theorem stage_edges_subset (C : RealStageChain Gamma Y kappa I frontier) (i : I) :
    RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj (C.stage i) ⊆ C.edgeUnion :=
  Set.subset_iUnion
    (fun j ↦ RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj (C.stage j)) i

theorem edgeUnion_biUnique (C : RealStageChain Gamma Y kappa I frontier) :
    Relator.BiUnique fun x y ↦ (x, y) ∈ C.edgeUnion := by
  constructor
  · intro x y z hxz hyz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxz
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hyz
    rcases le_total i j with hij | hji
    · exact (IsWarp.familyEdges_biUnique (C.warp j)).1 (C.edges_mono hij hi).1 hj.1
    · exact (IsWarp.familyEdges_biUnique (C.warp i)).1 hi.1 (C.edges_mono hji hj).1
  · intro x y z hxy hxz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxy
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxz
    rcases le_total i j with hij | hji
    · exact (IsWarp.familyEdges_biUnique (C.warp j)).2 (C.edges_mono hij hi).1 hj.1
    · exact (IsWarp.familyEdges_biUnique (C.warp i)).2 hi.1 (C.edges_mono hji hj).1

theorem edgeUnion_adj (C : RealStageChain Gamma Y kappa I frontier) :
    C.edgeUnion ⊆ {e | Gamma.graph.Adj e.1 e.2} := by
  intro e he
  obtain ⟨_i, hi⟩ := Set.mem_iUnion.mp he
  exact hi.2

theorem edgeUnion_endpoints (C : RealStageChain Gamma Y kappa I frontier) :
    ∀ e ∈ C.edgeUnion, e.1 ∈ C.vertexUnion ∧ e.2 ∈ C.vertexUnion := by
  intro e he
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
  have hends := familyEdges_subset_vertexSet_prod (C.stage i) hi.1
  exact ⟨C.stage_vertices_subset i hends.1, C.stage_vertices_subset i hends.2⟩

/-- The source-cover clause itself excludes incoming original edges at a
source, including when that source was previously handled by the reference. -/
theorem source_no_incoming (C : RealStageChain Gamma Y kappa I frontier)
    {a : V} (ha : a ∈ Gamma.source) : ¬HasIncoming C.edgeUnion a := by
  rintro ⟨x, hxa⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxa
  have haV := (familyEdges_subset_vertexSet_prod (C.stage i) hi.1).2
  rcases C.covers_source i ha with haInitial | haReference
  · rw [TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
      (C.warp i)] at haInitial
    exact haInitial.2 ⟨x, hi.1⟩
  · obtain ⟨p, hp, hpa⟩ := haReference
    exact hp.2 ⟨hp.1.1, a, hpa ▸ p.initial_mem_support, haV⟩

/-- Fair terminal completion and finite stage real parts give finite union
reachability from every represented vertex, not just from sources. -/
theorem vertex_reaches_target
    (C : RealStageChain Gamma Y kappa I frontier) {B : Set V}
    (hnoRay : ∀ i, ¬ContainsDirectedRay
      (RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj (C.stage i)))
    (hfair : ∀ i x, IsRealTerminal (Gamma := imaginaryWeb Y kappa)
        Gamma.graph.Adj (C.stage i) x →
      ∃ j, i ≤ j ∧ RealReaches (C.stage j) x B)
    {a : V} (ha : a ∈ C.vertexUnion) :
    ∃ b ∈ B, Relation.ReflTransGen (fun x y ↦ (x, y) ∈ C.edgeUnion) a b := by
  obtain ⟨i, hai⟩ := Set.mem_iUnion.mp ha
  obtain ⟨p, hpa, hpterminal, hpV, hpE⟩ :=
    exists_finiteRealPath_to_realTerminal (C.warp i) (hnoRay i) hai
  obtain ⟨j, hij, b, hbB, hxb⟩ := hfair i p.finish hpterminal
  have hax : RealReach (C.stage j) p.start p.finish :=
    (RealReach.of_path p hpV hpE).mono (C.vertices_mono hij) (C.edges_mono hij)
  have hab : RealReach (C.stage j) a b := hpa ▸ hax.trans hxb
  exact ⟨b, hbB, Relation.ReflTransGen.mono
    (fun _ _ he ↦ C.stage_edges_subset j he) _ _ hab.2⟩

/-- A reference owner at an original source meets a stage carrier only if
that source is actually represented somewhere in the chain. -/
theorem source_mem_vertexUnion_of_reference_meets
    (C : RealStageChain Gamma Y kappa I frontier) (hY : Gamma.IsWarp Y)
    {p : Gamma.DPath} (hp : p ∈ Y) (ha : p.initial ∈ Gamma.source)
    (hmeet : (p.support ∩ C.vertexUnion).Nonempty) : p.initial ∈ C.vertexUnion := by
  obtain ⟨x, hxp, hx⟩ := hmeet
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  rcases C.covers_source i ha with hinitial | hreference
  · exact C.stage_vertices_subset i (initialSet_subset_vertexSet (C.stage i) hinitial)
  · obtain ⟨q, hq, hqp⟩ := hreference
    have heq : q = p := DWeb.IsWarp.eq_of_mem_support hY hq.1.1 hp
      (hqp ▸ q.initial_mem_support) p.initial_mem_support
    subst q
    exact False.elim (hq.2 ⟨hp, x, hxp, hxi⟩)

/-- Construct the final source-rooted finite warp directly. Its source
coverage holds at every old slice, but no retention of arbitrary auxiliary
vertices or intermediate-limit blueprint is claimed. -/
theorem exists_sourceProjection_of_eventuallyCompleted
    (C : RealStageChain Gamma Y kappa I frontier) (hY : Gamma.IsWarp Y)
    {B : Set V}
    (hnoRay : ∀ i, ¬ContainsDirectedRay
      (RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj (C.stage i)))
    (hfair : ∀ i x, IsRealTerminal (Gamma := imaginaryWeb Y kappa)
        Gamma.graph.Adj (C.stage i) x →
      ∃ j, i ≤ j ∧ RealReaches (C.stage j) x B) :
    ∃ P : Set Gamma.DPath, Gamma.IsWarp P ∧ Gamma.HasFiniteCharacter P ∧
      Gamma.initialSet P = Gamma.source ∩ C.vertexUnion ∧
      Gamma.terminalFrontier P ⊆ B ∧ familyEdges P ⊆ C.edgeUnion ∧
      Gamma.vertexSet P ⊆ C.vertexUnion ∧
      ∀ i, Gamma.source ⊆ Gamma.initialSet P ∪
        Gamma.initialSet (LinkageBlueprint.referencePathsMeeting Y (frontier i) \
          LinkageBlueprint.referencePathsMeeting Y (Gamma.vertexSet P)) := by
  obtain ⟨P, hP, hPfin, hPI, hPT, hPE, hPV⟩ :=
    SourceRootedPathSelection.exists_finiteWarp C.edgeUnion_adj C.edgeUnion_biUnique.1
      (A := Gamma.source ∩ C.vertexUnion) Set.inter_subset_right C.edgeUnion_endpoints
      (fun _ ha ↦ C.source_no_incoming ha.1)
      (fun _ ha ↦ C.vertex_reaches_target hnoRay hfair ha.2)
  refine ⟨P, hP, hPfin, hPI, hPT, hPE, hPV, ?_⟩
  intro i a ha
  by_cases haV : a ∈ C.vertexUnion
  · exact Or.inl (hPI ▸ ⟨ha, haV⟩)
  · right
    rcases C.covers_source i ha with haInitial | haReference
    · exact False.elim (haV (C.stage_vertices_subset i
        (initialSet_subset_vertexSet (C.stage i) haInitial)))
    · obtain ⟨p, hp, hpa⟩ := haReference
      refine ⟨p, ⟨hp.1, ?_⟩, hpa⟩
      rintro ⟨_hpY, x, hxp, hxP⟩
      have haUnion := C.source_mem_vertexUnion_of_reference_meets hY hp.1.1
        (hpa ▸ ha) ⟨x, hxp, hPV hxP⟩
      exact haV (hpa ▸ haUnion)

/-- For native blueprints the finite-real-component premise is discharged
by the proved theorem-preserving subdivision geometry. Fairness remains an
explicit construction obligation. -/
theorem exists_sourceProjection_of_blueprints
    (C : RealStageChain Gamma Y kappa I frontier) (hY : Gamma.IsWarp Y)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    (Z : I → Set V) (persistent B : Set V)
    (hblueprint : ∀ i, IsLinkageBlueprint (C.stage i) (frontier i) (Z i) persistent)
    (hfair : ∀ i x, IsRealTerminal (Gamma := imaginaryWeb Y kappa)
        Gamma.graph.Adj (C.stage i) x →
      ∃ j, i ≤ j ∧ RealReaches (C.stage j) x B) :
    ∃ P : Set Gamma.DPath, Gamma.IsWarp P ∧ Gamma.HasFiniteCharacter P ∧
      Gamma.initialSet P = Gamma.source ∩ C.vertexUnion ∧
      Gamma.terminalFrontier P ⊆ B ∧ familyEdges P ⊆ C.edgeUnion ∧
      Gamma.vertexSet P ⊆ C.vertexUnion ∧
      ∀ i, Gamma.source ⊆ Gamma.initialSet P ∪
        Gamma.initialSet (LinkageBlueprint.referencePathsMeeting Y (frontier i) \
          LinkageBlueprint.referencePathsMeeting Y (Gamma.vertexSet P)) :=
  C.exists_sourceProjection_of_eventuallyCompleted hY
    (fun i ↦ (hblueprint i).realPart_not_containsDirectedRay hY hinc) hfair

/-- In the normalized web used by the main argument, the selected warp
has the exact endpoint-clean linkage predicate, not merely finite paths
whose last vertices lie in the target. -/
theorem exists_linkageProjection_of_blueprints
    (C : RealStageChain Gamma Y kappa I frontier) (hY : Gamma.IsWarp Y)
    (hGamma : Gamma.IsNormalized)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    (Z : I → Set V) (persistent : Set V)
    (hblueprint : ∀ i, IsLinkageBlueprint (C.stage i) (frontier i) (Z i) persistent)
    (hfair : ∀ i x, IsRealTerminal (Gamma := imaginaryWeb Y kappa)
        Gamma.graph.Adj (C.stage i) x →
      ∃ j, i ≤ j ∧ RealReaches (C.stage j) x Gamma.target) :
    ∃ P : Set Gamma.DPath,
      CardinalInduction.IsLinkageBetween Gamma (Gamma.source ∩ C.vertexUnion) Gamma.target P ∧
      familyEdges P ⊆ C.edgeUnion ∧ Gamma.vertexSet P ⊆ C.vertexUnion ∧
      ∀ i, Gamma.source ⊆ Gamma.initialSet P ∪
        Gamma.initialSet (LinkageBlueprint.referencePathsMeeting Y (frontier i) \
          LinkageBlueprint.referencePathsMeeting Y (Gamma.vertexSet P)) := by
  obtain ⟨P, hP, hPfin, hPI, hPT, hPE, hPV, hcover⟩ :=
    C.exists_sourceProjection_of_blueprints hY hinc Z persistent Gamma.target hblueprint hfair
  refine ⟨P, ⟨hP, hPfin, hPI, hPT, ?_⟩, hPE, hPV, hcover⟩
  intro p hp
  obtain ⟨q, rfl⟩ := hPfin hp
  exact CardinalInduction.SingularSafeCompletedMachine.isPathBetween_of_normalized
    hGamma Set.inter_subset_left q
    (hPI ▸ ⟨Sum.inl q, hp, rfl⟩) (hPT ⟨Sum.inl q, hp, rfl⟩)

#print axioms edgeUnion_biUnique
#print axioms source_no_incoming
#print axioms vertex_reaches_target
#print axioms exists_sourceProjection_of_eventuallyCompleted
#print axioms exists_sourceProjection_of_blueprints
#print axioms exists_linkageProjection_of_blueprints

end RealStageChain
end Erdos599.Blueprint.ColouredSafeShortcutGraph
