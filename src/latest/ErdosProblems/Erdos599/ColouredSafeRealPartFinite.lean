/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeLocalTransactionRealLedger
import ErdosProblems.Erdos599.ColouredSafeNativeNoStrongReal
import ErdosProblems.Erdos599.ColouredSafeWeakBlueprintTransaction
import ErdosProblems.Erdos599.PathFilterComponents

/-!
# Actual finite components of the native real part

The spanning real-edge filter is decomposed into actual paths, including
isolated vertices. When that real relation has no directed ray, every
component is finite. Every carrier point then has a finite real suffix to
an actual pending terminal. No implication from strong marks to absence of
real rays is assumed; that separate geometric fact must be supplied.
-/

noncomputable section

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set Cardinal Order DirectedPath Alternating
open ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}

/-- Exact spanning finite-path realization of a ray-free native real part.
Its terminal set is exactly the predicate used by the local real ledger. -/
theorem exists_finiteRealPart
    {W : Set (imaginaryWeb Y kappa).DPath}
    (hW : (imaginaryWeb Y kappa).IsWarp W)
    (hnoRay : ¬ContainsDirectedRay
      (RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj W)) :
    ∃ K : Set Gamma.DPath, Gamma.IsWarp K ∧ Gamma.HasFiniteCharacter K ∧
      Gamma.vertexSet K = (imaginaryWeb Y kappa).vertexSet W ∧
      familyEdges K = RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj W ∧
      Gamma.terminalFrontier K =
        {x | IsRealTerminal (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj W x} := by
  let D := imaginaryWeb Y kappa
  obtain ⟨K, hK, hKV, hKE⟩ :=
    PathFilterComponents.exists_warp_filtering_to_subgraph
      Gamma W (D.vertexSet W) hW (fun h ↦ Or.inl h)
      (fun e he ↦ familyEdges_subset_vertexSet_prod W he.1)
  have hKE' : familyEdges K = RealEdges (Gamma := D) Gamma.graph.Adj W := hKE
  have hKfinite : Gamma.HasFiniteCharacter K := by
    intro q hq
    rcases q with p | r
    · exact ⟨p, rfl⟩
    · apply False.elim
      apply hnoRay
      refine ⟨{ vertex := r.toFun, injective := r.injective }, ?_⟩
      rintro e ⟨n, rfl⟩
      rw [← hKE']
      exact Set.mem_iUnion.mpr ⟨Sum.inr r, Set.mem_iUnion.mpr ⟨hq, ⟨n, rfl⟩⟩⟩
  refine ⟨K, hK, hKfinite, hKV, hKE', ?_⟩
  rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hK,
    hKV, hKE']
  rfl

/-- Any point of the augmented carrier reaches a real terminal by a finite
real path as soon as the spanning real part is known to be ray-free. -/
theorem exists_finiteRealPath_to_realTerminal
    {W : Set (imaginaryWeb Y kappa).DPath}
    (hW : (imaginaryWeb Y kappa).IsWarp W)
    (hnoRay : ¬ContainsDirectedRay
      (RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj W))
    {s : V} (hs : s ∈ (imaginaryWeb Y kappa).vertexSet W) :
    ∃ p : FinitePath Gamma.graph, p.start = s ∧
      IsRealTerminal (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj W p.finish ∧
      p.support ⊆ (imaginaryWeb Y kappa).vertexSet W ∧
      p.edgeSet ⊆ familyEdges W := by
  obtain ⟨K, _hK, hKfinite, hKV, hKE, hKT⟩ := exists_finiteRealPart hW hnoRay
  obtain ⟨q0, hq, hsq⟩ := hKV.symm ▸ hs
  obtain ⟨q, rfl⟩ := hKfinite hq
  let p := q.suffixFrom s hsq
  have hpstart : p.start = s := q.suffixFrom_start s hsq
  have hpfinish : p.finish = q.finish := q.suffixFrom_finish s hsq
  refine ⟨p, hpstart, ?_, ?_, ?_⟩
  · rw [hpfinish]
    have hterminal : q.finish ∈ Gamma.terminalFrontier K := ⟨Sum.inl q, hq, rfl⟩
    change q.finish ∈ {x | IsRealTerminal
      (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj W x}
    rw [← hKT]
    exact hterminal
  · intro x hx
    rw [← hKV]
    exact ⟨Sum.inl q, hq, q.suffixFrom_support_subset s hsq hx⟩
  · intro e he
    have heK : e ∈ familyEdges K :=
      Set.mem_iUnion.mpr ⟨Sum.inl q, Set.mem_iUnion.mpr
        ⟨hq, q.suffixFrom_edgeSet_subset s hsq he⟩⟩
    exact (hKE ▸ heK).1

/-- In a subdivided ambient web, the six native blueprint conditions do
exclude real rays. The contained ray is first lifted to the augmented graph
and identified with a tail of one of its actual blueprint owners. -/
theorem IsLinkageBlueprint.realPart_not_containsDirectedRay
    {W : Set (imaginaryWeb Y kappa).DPath} {T Z persistent : Set V}
    (hW : IsLinkageBlueprint W T Z persistent) (hY : Gamma.IsWarp Y)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph) :
    ¬ContainsDirectedRay
      (RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj W) := by
  rintro ⟨r, hr⟩
  let q : Ray (imaginaryWeb Y kappa).graph := {
    toFun := r.vertex
    adj_succ := fun n ↦ Or.inl (hr ⟨n, rfl⟩).2
    injective := r.injective }
  have hqE : q.edgeSet ⊆ familyEdges W := by
    rintro e ⟨n, rfl⟩
    exact (hr ⟨n, rfl⟩).1
  obtain ⟨n, hn⟩ :=
    (hW.isWarp.markedIndices_infinite_of_edgeSet_subset
      hW.infinitely_many_strong q hqE).nonempty
  exact not_isStrong_of_subdivisionIncidence hY (hinc (hr ⟨n, rfl⟩).2) hn

/-- Every point of a native blueprint has a finite real continuation to a
pending terminal under the theorem-preserving subdivision incidence. -/
theorem IsLinkageBlueprint.exists_finiteRealPath_to_realTerminal
    {W : Set (imaginaryWeb Y kappa).DPath} {T Z persistent : Set V}
    (hW : IsLinkageBlueprint W T Z persistent) (hY : Gamma.IsWarp Y)
    (hinc : HasHereditarySubdivisionIncidence Gamma.graph)
    {s : V} (hs : s ∈ (imaginaryWeb Y kappa).vertexSet W) :
    ∃ p : FinitePath Gamma.graph, p.start = s ∧
      IsRealTerminal (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj W p.finish ∧
      p.support ⊆ (imaginaryWeb Y kappa).vertexSet W ∧
      p.edgeSet ⊆ familyEdges W :=
  ColouredSafeShortcutGraph.exists_finiteRealPath_to_realTerminal hW.isWarp
    (hW.realPart_not_containsDirectedRay hY hinc) hs

#print axioms exists_finiteRealPart
#print axioms exists_finiteRealPath_to_realTerminal
#print axioms IsLinkageBlueprint.realPart_not_containsDirectedRay
#print axioms IsLinkageBlueprint.exists_finiteRealPath_to_realTerminal

end Erdos599.Blueprint.ColouredSafeShortcutGraph
