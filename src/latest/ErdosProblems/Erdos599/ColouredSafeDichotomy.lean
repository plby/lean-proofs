/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafePrefixState
import ErdosProblems.Erdos599.InfiniteColouredOccurrenceSwitch

/-!
# Constructed safe occurrence dichotomy for endpoint-pure finite warps

If the source is outside actual reverse reachability, the proved successor
produces a strictly growing prefix chain and an interval-safe infinite word.
If it is inside, simple residual path extraction produces a finite safe word
and a reducing warp. All forward transitions remain in the original fixed
warp for this single-source result. Simultaneous assignment is separate.
-/

namespace Erdos599.ColouredSafeReverseReachability

open Set DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

theorem exists_prefixChain_of_source_not_reverseReachable
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {s : V} (hs : s ∈ Gamma.initialSet W) (hsOff : s ∉ Gamma.vertexSet Y)
    (hsC : s ∉ reverseReachable W Y s) :
    ∃ C : FiniteColouredOccurrencePrefixChain W Y,
      (∀ n, (C.stage n).IsIntervalSafe) ∧ C.limit.vertex 0 = s := by
  classical
  have hsW : s ∈ Gamma.vertexSet W := by
    obtain ⟨p, hp, hps⟩ := hs
    exact ⟨p, hp, by simpa only [hps] using p.initial_mem_support⟩
  let initial := SafePrefixState.initial hsW hsC
  have hstep (S : SafePrefixState W Y s) :
      ∃ T : SafePrefixState W Y s,
        S.word.Prefix T.word ∧ S.word.length < T.word.length :=
    S.exists_successor hW hY hWfin hYfin hsource hterminal hs hsOff
  let next (S : SafePrefixState W Y s) := Classical.choose (hstep S)
  let stages : ℕ → SafePrefixState W Y s := Nat.rec initial (fun _ S ↦ next S)
  let C : FiniteColouredOccurrencePrefixChain W Y := {
    stage := fun n ↦ (stages n).word
    grows := fun n ↦ (Classical.choose_spec (hstep (stages n))).1
    length_strict := fun n ↦ (Classical.choose_spec (hstep (stages n))).2 }
  refine ⟨C, fun n ↦ (stages n).safe, ?_⟩
  have hfirst : (C.stage 0).vertex 0 = s := (stages 0).first_eq
  exact (C.stage_vertex_eq_limit 0 0).symm.trans hfirst

/-- The infinite branch includes the actual finite-character switched
warp and its exact one-initial boundary, not merely the infinite word. -/
theorem exists_safeInfinite_of_source_not_reverseReachable
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {s : V} (hs : s ∈ Gamma.initialSet W) (hsOff : s ∉ Gamma.vertexSet Y)
    (hsC : s ∉ reverseReachable W Y s) :
    ∃ Q : InfiniteColouredOccurrenceWord W Y, Q.IsIntervalSafe ∧ Q.vertex 0 = s ∧
      ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
        familyEdges U = (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges ∧
        isolatedVertices U = isolatedVertices Y ∧
        Gamma.initialSet U = Gamma.initialSet Y ∪ {s} ∧
        Gamma.terminalFrontier U = Gamma.terminalFrontier Y := by
  obtain ⟨C, hsafe, hfirst⟩ := exists_prefixChain_of_source_not_reverseReachable
    hW hY hWfin hYfin hsource hterminal hs hsOff hsC
  have hfirstOff : C.limit.vertex 0 ∉ Gamma.vertexSet Y := by
    simpa only [hfirst] using hsOff
  obtain ⟨U, hU, hUfin, hUE, hUI, hUinitial, hUterminal⟩ :=
    C.exists_finiteWarp_realizing_limitSwitch_of_stageSafe
      hW hWfin hY hYfin hsafe hfirstOff
  refine ⟨C.limit, C.limit_isIntervalSafe hYfin hsafe, hfirst,
    U, hU, hUfin, hUE, hUI, ?_, hUterminal⟩
  simpa only [hfirst] using hUinitial

/-- The single-source dichotomy with actual switching witnesses. The
nonisolated hypothesis applies only to deleting the finite branch's two
old endpoints; the isolated initial-terminal case is separate. -/
theorem exists_safe_occurrence_dichotomy
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    (hsource : Gamma.initialSet Y ⊆ Gamma.initialSet W)
    (hinitial : Gamma.initialSet W ∩ Gamma.vertexSet Y ⊆ Gamma.initialSet Y)
    (hterminal : Gamma.terminalFrontier W ∩ Gamma.vertexSet Y ⊆
      Gamma.terminalFrontier Y)
    {s : V} (hs : s ∈ Gamma.initialSet W) (hsOff : s ∉ Gamma.vertexSet Y)
    (hsiso : s ∉ isolatedVertices W) :
    (∃ Q : InfiniteColouredOccurrenceWord W Y, Q.IsIntervalSafe ∧ Q.vertex 0 = s ∧
      ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
        familyEdges U = (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges ∧
        isolatedVertices U = isolatedVertices Y ∧
        Gamma.initialSet U = Gamma.initialSet Y ∪ {s} ∧
        Gamma.terminalFrontier U = Gamma.terminalFrontier Y) ∨
    (∃ t ∈ Gamma.terminalFrontier W \ Gamma.vertexSet Y,
      ∃ Q : FiniteColouredOccurrenceWord W Y, Q.IsIntervalSafe ∧
        Q.vertex 0 = s ∧ Q.vertex (Fin.last Q.length) = t ∧
        ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
          familyEdges U ⊆ familyEdges W ∪ familyEdges Y ∧
          isolatedVertices U = isolatedVertices W ∧
          Gamma.initialSet U = Gamma.initialSet W \ {s} ∧
          Gamma.terminalFrontier U = Gamma.terminalFrontier W \ {t}) := by
  classical
  by_cases hsC : s ∈ reverseReachable W Y s
  · right
    apply finite_reduction_of_source_mem_reverseReachable hW hY hWfin hYfin
      hs hsiso _ hsC
    intro x y hxy
    have hxyV := familyEdges_subset_vertexSet_prod Y hxy
    constructor
    · intro hy
      have hyInitial := hinitial ⟨hy, hxyV.2⟩
      rw [initialSet_eq_vertexSet_diff_hasIncoming hY hYfin] at hyInitial
      exact hyInitial.2 ⟨x, hxy⟩
    · intro hx
      have hxTerminal := hterminal ⟨hx, hxyV.1⟩
      rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing hY hYfin] at hxTerminal
      exact hxTerminal.2 ⟨y, hxy⟩
  · exact Or.inl (exists_safeInfinite_of_source_not_reverseReachable
      hW hY hWfin hYfin hsource hterminal hs hsOff hsC)

#print axioms exists_prefixChain_of_source_not_reverseReachable
#print axioms exists_safeInfinite_of_source_not_reverseReachable
#print axioms exists_safe_occurrence_dichotomy

end Erdos599.ColouredSafeReverseReachability
