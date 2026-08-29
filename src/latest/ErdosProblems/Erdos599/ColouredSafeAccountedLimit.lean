/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeSourceRefinedWarpLimit
import ErdosProblems.Erdos599.ColouredSafeFullAccounting
import ErdosProblems.Erdos599.ColouredSafeNativeTargetBoundary

/-!
# Rays and terminals of a genuinely target-accounted native limit

Full accounting is to the original target, not to a moving intermediate
frontier. It forces every eventual forward ray into one old stage and
forces every eventual sink outside the target to be an old terminal.
This discharges the remaining relation-limit fields once the actual
successor construction supplies genuine target accounting.
-/

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph.RealStageChain

open Set DirectedPath Alternating ColouredSafeLocalTransactionRealLedger

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}} {I : Type v} [LinearOrder I] {frontier : I → Set V}

theorem forward_index_of_reaches
    {E : Set (V × V)} (hE : Relator.RightUnique fun x y ↦ (x, y) ∈ E)
    (r : ℕ → V) (hr : ∀ n, (r n, r (n + 1)) ∈ E)
    {a b : V} (h : Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b) :
    ∀ n, a = r n → ∃ m, n ≤ m ∧ b = r m := by
  induction h with
  | refl => exact fun n hn ↦ ⟨n, le_rfl, hn⟩
  | @tail b c hab hbc ih =>
      intro n hn
      obtain ⟨m, hnm, hbm⟩ := ih n hn
      have hcm : c = r (m + 1) := hE (hbm ▸ hbc) (hr m)
      exact ⟨m + 1, hnm.trans (Nat.le_succ m), hcm⟩

theorem eq_of_reaches_of_noOutgoing
    {E : Set (V × V)} {a b : V} (ha : ¬HasOutgoing E a)
    (h : Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b) : b = a := by
  induction h with
  | refl => rfl
  | @tail b c hab hbc ih => exact False.elim (ha ⟨c, ih ▸ hbc⟩)

theorem realReach_eventual (C : RealStageChain Gamma Y kappa I frontier)
    {j : I} {a b : V} (h : RealReach (C.stage j) a b) :
    Relation.ReflTransGen (fun x y ↦ (x, y) ∈ C.eventualEdges) a b :=
  Relation.ReflTransGen.mono
    (fun _ _ he ↦ C.edgeUnion_subset_eventualEdges (C.stage_edges_subset j he)) _ _ h.2

theorem noRealCompletion_on_eventualRay
    (C : RealStageChain Gamma Y kappa I frontier)
    (hGamma : Gamma.IsNormalized) (hY : Gamma.IsWarp Y)
    (r : Ray (imaginaryWeb Y kappa).graph) (hr : r.edgeSet ⊆ C.eventualEdges)
    (j : I) (n : ℕ) : ¬RealReaches (C.stage j) (r n) Gamma.target := by
  rintro ⟨b, hb, hreach⟩
  obtain ⟨m, _hnm, hbm⟩ := forward_index_of_reaches C.eventualEdges_biUnique.2
    r (fun n ↦ hr ⟨n, rfl⟩) (C.realReach_eventual hreach) n rfl
  exact nativeRay_not_mem_target hGamma hY r m (hbm ▸ hb)

theorem eventualRay_edge_mem_stage
    (C : RealStageChain Gamma Y kappa I frontier)
    (hGamma : Gamma.IsNormalized) (hY : Gamma.IsWarp Y)
    (haccount : ∀ {i j}, i ≤ j → FullAccount (C.stage i) (C.stage j) Gamma.target)
    (r : Ray (imaginaryWeb Y kappa).graph) (hr : r.edgeSet ⊆ C.eventualEdges)
    (i : I) (n : ℕ) (hx : r n ∈ (imaginaryWeb Y kappa).vertexSet (C.stage i)) :
    (r n, r (n + 1)) ∈ familyEdges (C.stage i) := by
  obtain ⟨j₀, hj₀⟩ := hr ⟨n, rfl⟩
  let j := max i j₀
  have hjEdge : (r n, r (n + 1)) ∈ familyEdges (C.stage j) :=
    hj₀ j (le_max_right _ _)
  rcases haccount (le_max_left i j₀) (r n) hx with hterm | ⟨y, hyi, hyj⟩ | hdone
  · have hno := hterm.2
    rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
      (C.warp j)] at hno
    exact False.elim (hno.2 ⟨r (n + 1), hjEdge⟩)
  · have hy := (IsWarp.familyEdges_biUnique (C.warp j)).2 hyj hjEdge
    exact hy ▸ hyi
  · exact False.elim (C.noRealCompletion_on_eventualRay hGamma hY r hr j n hdone)

/-- Every eventual ray is contained in any stage containing its first
vertex. Completion to the actual target excludes all later divergence. -/
theorem eventualRay_edges_subset_stage
    (C : RealStageChain Gamma Y kappa I frontier)
    (hGamma : Gamma.IsNormalized) (hY : Gamma.IsWarp Y)
    (haccount : ∀ {i j}, i ≤ j → FullAccount (C.stage i) (C.stage j) Gamma.target)
    (r : Ray (imaginaryWeb Y kappa).graph) (hr : r.edgeSet ⊆ C.eventualEdges)
    (i : I) (hfirst : r 0 ∈ (imaginaryWeb Y kappa).vertexSet (C.stage i)) :
    r.edgeSet ⊆ familyEdges (C.stage i) := by
  have hvertices : ∀ n, r n ∈ (imaginaryWeb Y kappa).vertexSet (C.stage i) := by
    intro n
    induction n with
    | zero => exact hfirst
    | succ n ih =>
        exact (familyEdges_subset_vertexSet_prod (C.stage i)
          (C.eventualRay_edge_mem_stage hGamma hY haccount r hr i n ih)).2
  rintro _ ⟨n, rfl⟩
  exact C.eventualRay_edge_mem_stage hGamma hY haccount r hr i n (hvertices n)

theorem eventualWarp_infinitelyManyStrong
    (C : RealStageChain Gamma Y kappa I frontier)
    (hGamma : Gamma.IsNormalized) (hY : Gamma.IsWarp Y)
    (haccount : ∀ {i j}, i ≤ j → FullAccount (C.stage i) (C.stage j) Gamma.target)
    (hstrong : ∀ i, (imaginaryWeb Y kappa).InfinitelyManyMarkedEdges
      (C.stage i) (IsStrong Y kappa))
    {U : Set (imaginaryWeb Y kappa).DPath} (hUE : familyEdges U = C.eventualEdges) :
    (imaginaryWeb Y kappa).InfinitelyManyMarkedEdges U (IsStrong Y kappa) := by
  intro r hrU
  have hr : r.edgeSet ⊆ C.eventualEdges := by
    intro e he
    rw [← hUE]
    exact Set.mem_iUnion.mpr ⟨Sum.inr r, Set.mem_iUnion.mpr ⟨hrU, he⟩⟩
  obtain ⟨i, hi⟩ := hr ⟨0, rfl⟩
  have hfirst := (familyEdges_subset_vertexSet_prod (C.stage i) (hi i le_rfl)).1
  exact (C.warp i).markedIndices_infinite_of_edgeSet_subset (hstrong i) r
    (C.eventualRay_edges_subset_stage hGamma hY haccount r hr i hfirst)

theorem eventual_sink_mem_target_or_stage_terminal
    (C : RealStageChain Gamma Y kappa I frontier)
    (haccount : ∀ {i j}, i ≤ j → FullAccount (C.stage i) (C.stage j) Gamma.target)
    {x : V} (hsink : ¬HasOutgoing C.eventualEdges x)
    (i : I) (hx : x ∈ (imaginaryWeb Y kappa).vertexSet (C.stage i)) :
    x ∈ Gamma.target ∨ x ∈ (imaginaryWeb Y kappa).terminalFrontier (C.stage i) := by
  classical
  by_cases hxB : x ∈ Gamma.target
  · exact Or.inl hxB
  right
  by_contra hxT
  have hout : HasOutgoing (familyEdges (C.stage i)) x := by
    by_contra hno
    apply hxT
    rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp (C.warp i)]
    exact ⟨hx, hno⟩
  obtain ⟨y, hxy⟩ := hout
  apply hsink
  refine ⟨y, i, ?_⟩
  intro j hij
  rcases haccount hij x hx with hterm | ⟨z, hzOld, hzNew⟩ | ⟨b, hb, hxb⟩
  · exact False.elim (hxT hterm.1)
  · have hzy := (IsWarp.familyEdges_biUnique (C.warp i)).2 hzOld hxy
    exact hzy ▸ hzNew
  · have hbx := eq_of_reaches_of_noOutgoing hsink (C.realReach_eventual hxb)
    exact False.elim (hxB (hbx ▸ hb))

theorem eventualWarp_terminals_popular
    (C : RealStageChain Gamma Y kappa I frontier)
    (haccount : ∀ {i j}, i ≤ j → FullAccount (C.stage i) (C.stage j) Gamma.target)
    (closed : I → Set V) (persistent : Set V)
    (hstage : ∀ i, IsLinkageBlueprint (C.stage i) (frontier i) (closed i) persistent)
    (hstable : ∀ i, (imaginaryWeb Y kappa).terminalFrontier (C.stage i) ∩
      frontier i ⊆ persistent)
    (hB : Gamma.target ∩ C.vertexUnion ⊆ persistent)
    {U : Set (imaginaryWeb Y kappa).DPath}
    (hU : (imaginaryWeb Y kappa).IsWarp U)
    (hUV : (imaginaryWeb Y kappa).vertexSet U = C.vertexUnion)
    (hUE : familyEdges U = C.eventualEdges) :
    (imaginaryWeb Y kappa).terminalFrontier U ⊆
      {x | IsPopular Y persistent kappa x} := by
  intro x hx
  have hxV : x ∈ C.vertexUnion :=
    hUV ▸ terminalFrontier_subset_vertexSet U hx
  have hsink := hx
  rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hU,
    hUE] at hsink
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxV
  rcases C.eventual_sink_mem_target_or_stage_terminal haccount hsink.2 i hxi with hxB | hxT
  · exact Or.inl (hB ⟨hxB, hxV⟩)
  · rcases (hstage i).terminals_popular hxT with hpop | hfrontier
    · exact hpop
    · exact Or.inl (hstable i ⟨hxT, hfrontier⟩)

theorem realReach_exact_eventualWarp
    (C : RealStageChain Gamma Y kappa I frontier)
    {U : Set (imaginaryWeb Y kappa).DPath}
    (hUV : (imaginaryWeb Y kappa).vertexSet U = C.vertexUnion)
    (hUE : familyEdges U = C.eventualEdges)
    {i : I} {a b : V} (h : RealReach (C.stage i) a b) : RealReach U a b := by
  apply h.mono
  · rw [hUV]
    exact C.stage_vertices_subset i
  · intro e he
    exact ⟨hUE.symm ▸ C.edgeUnion_subset_eventualEdges (C.stage_edges_subset i he), he.2⟩

/-- Source-anchored refinement is retained at the exact relation limit,
not merely assumed at each successor. -/
theorem sourcePredecessorRefines_eventualWarp
    (C : RealStageChain Gamma Y kappa I frontier)
    (hrefine : ∀ {i j}, i ≤ j → SourcePredecessorRefines (C.stage i) (C.stage j))
    {U : Set (imaginaryWeb Y kappa).DPath}
    (hUV : (imaginaryWeb Y kappa).vertexSet U = C.vertexUnion)
    (hUE : familyEdges U = C.eventualEdges) (i : I) :
    SourcePredecessorRefines (C.stage i) U := by
  intro x y hx hyx
  obtain ⟨j₀, hj₀⟩ := hUE ▸ hyx
  rcases hrefine (le_max_left i j₀) hx
      (hj₀ (max i j₀) (le_max_right _ _)) with hold | ⟨z, hz, hzx⟩ | ⟨a, ha, hax⟩
  · exact Or.inl hold
  · exact Or.inr (Or.inl ⟨z, hz, C.realReach_exact_eventualWarp hUV hUE hzx⟩)
  · exact Or.inr (Or.inr ⟨a, ha, C.realReach_exact_eventualWarp hUV hUE hax⟩)

/-- Full target accounting passes to the actual exact relation-limit warp. -/
theorem fullAccount_eventualWarp
    (C : RealStageChain Gamma Y kappa I frontier)
    (haccount : ∀ {i j}, i ≤ j → FullAccount (C.stage i) (C.stage j) Gamma.target)
    {U : Set (imaginaryWeb Y kappa).DPath}
    (hU : (imaginaryWeb Y kappa).IsWarp U)
    (hUV : (imaginaryWeb Y kappa).vertexSet U = C.vertexUnion)
    (hUE : familyEdges U = C.eventualEdges) (i : I) :
    FullAccount (C.stage i) U Gamma.target := by
  classical
  intro x hx
  by_cases hdone : ∃ j, RealReaches (C.stage j) x Gamma.target
  · obtain ⟨j, b, hb, hxb⟩ := hdone
    exact Or.inr (Or.inr ⟨b, hb, C.realReach_exact_eventualWarp hUV hUE hxb⟩)
  have hnotDone : ∀ j, ¬RealReaches (C.stage j) x Gamma.target :=
    fun j hj ↦ hdone ⟨j, hj⟩
  by_cases hxT : x ∈ (imaginaryWeb Y kappa).terminalFrontier (C.stage i)
  · left
    refine ⟨hxT, ?_⟩
    rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hU,
      hUV, hUE]
    refine ⟨C.stage_vertices_subset i hx, ?_⟩
    rintro ⟨y, j₀, hj₀⟩
    let j := max i j₀
    have hjEdge := hj₀ j (le_max_right _ _)
    rcases haccount (le_max_left i j₀) x hx with hterm | ⟨z, hzi, _⟩ | hcompleted
    · have hno := hterm.2
      rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
        (C.warp j)] at hno
      exact hno.2 ⟨y, hjEdge⟩
    · have hno := hxT
      rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
        (C.warp i)] at hno
      exact hno.2 ⟨z, hzi⟩
    · exact hnotDone j hcompleted
  · have hout : HasOutgoing (familyEdges (C.stage i)) x := by
      by_contra hno
      apply hxT
      rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp
        (C.warp i)]
      exact ⟨hx, hno⟩
    obtain ⟨y, hxy⟩ := hout
    refine Or.inr (Or.inl ⟨y, hxy, ?_⟩)
    rw [hUE]
    refine ⟨i, ?_⟩
    intro j hij
    rcases haccount hij x hx with hterm | ⟨z, hzi, hzj⟩ | hcompleted
    · exact False.elim (hxT hterm.1)
    · have hzy := (IsWarp.familyEdges_biUnique (C.warp i)).2 hzi hxy
      exact hzy ▸ hzj
    · exact False.elim (hnotDone j hcompleted)

#print axioms eventualRay_edges_subset_stage
#print axioms eventualWarp_infinitelyManyStrong
#print axioms eventual_sink_mem_target_or_stage_terminal
#print axioms eventualWarp_terminals_popular
#print axioms sourcePredecessorRefines_eventualWarp
#print axioms fullAccount_eventualWarp

end Erdos599.Blueprint.ColouredSafeShortcutGraph.RealStageChain
