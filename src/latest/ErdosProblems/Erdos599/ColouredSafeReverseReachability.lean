/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceSafeStep
import ErdosProblems.Erdos599.ColouredResidualPortReduction
import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp

/-!
# Actual reverse reachability in the safe occurrence-word construction

Reverse reachability is defined in the residual port graph, not by a
postulated collision-trimmed `AltPath`. The continuation lemmas are actual
port walks. If the original source is reverse reachable, finite simple-path
extraction and the checked residual switch construct the reducing warp.
-/

namespace Erdos599.ColouredSafeReverseReachability

open Set DirectedPath Alternating
open ColouredResidualPortContinuation ColouredResidualPortReduction

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

def safelyReachable (W Y : Set Gamma.DPath) (s : V) : Set V :=
  {t | t ∈ Gamma.terminalFrontier W \ Gamma.vertexSet Y ∧
    ∃ Q : FiniteColouredOccurrenceWord W Y, Q.IsIntervalSafe ∧
      Q.vertex 0 = s ∧ Q.vertex (Fin.last Q.length) = t}

def reverseReachable (W Y : Set Gamma.DPath) (s : V) : Set V :=
  {x | ∃ t ∈ safelyReachable W Y s,
    Relation.ReflTransGen (ResidualStep W Y) (.inr t) (.inl x)}

/-- The source proof's first outside assertion is literal transitivity of
the constructed residual continuation along the forward-warp fragment. -/
theorem finish_not_reverseReachable_of_start_not
    {s : V} (p : FinitePath Gamma.graph) (hp : p.edgeSet ⊆ familyEdges W)
    (hstart : p.start ∉ reverseReachable W Y s) :
    p.finish ∉ reverseReachable W Y s := by
  rintro ⟨t, ht, hreach⟩
  exact hstart ⟨t, ht, hreach.trans
    (finiteReferencePath_sender_finish_reaches_start_of_edges p hp)⟩

/-- The predecessor assertion includes the common forward/reference-edge
case, which is handled by the proved cancellation continuation. -/
theorem reference_predecessor_not_reverseReachable
    (hW : Gamma.IsWarp W) {s y : V}
    (p : FinitePath Gamma.graph) (hp : p.edgeSet ⊆ familyEdges W)
    (hne : p.start ≠ p.finish)
    (hy : (y, p.finish) ∈ familyEdges Y)
    (hstart : p.start ∉ reverseReachable W Y s) :
    y ∉ reverseReachable W Y s := by
  rintro ⟨t, ht, hreach⟩
  exact hstart ⟨t, ht, hreach.trans
    (forwardEdge_to_finiteReferenceFinish_reaches_start_of_edges hW p hp hne hy)⟩

private theorem terminal_not_isolated_of_word
    (hW : Gamma.IsWarp W) {s t : V}
    (hs : s ∉ isolatedVertices W) (ht : t ∉ Gamma.vertexSet Y)
    (Q : FiniteColouredOccurrenceWord W Y)
    (hfirst : Q.vertex 0 = s) (hlast : Q.vertex (Fin.last Q.length) = t) :
    t ∉ isolatedVertices W := by
  intro htiso
  cases hlength : Q.length with
  | zero =>
      have hindex : Fin.last Q.length = 0 := Fin.ext (by simp [hlength])
      have hts : t = s := hlast.symm.trans (by simpa [hindex] using hfirst)
      exact hs (hts ▸ htiso)
  | succ n =>
      let i : Fin Q.length := ⟨n, by omega⟩
      have hiLast : i.succ = Fin.last Q.length := Fin.ext (by simp [i, hlength])
      have hlast' : Q.vertex i.succ = t := by rw [hiLast, hlast]
      have hedge := Q.actualEdge_spec i
      cases hdir : Q.direction i with
      | forward =>
          simp only [hdir] at hedge
          have h := IsWarp.familyEdge_not_incident_isolated hW htiso hedge
          exact h.2 hlast'
      | backward =>
          simp only [hdir] at hedge
          exact ht (hlast' ▸ (familyEdges_subset_vertexSet_prod Y hedge).1)

/-- Reverse reachability of the original source gives the finite branch
of the source dichotomy: an actual safe outward word and an actual reduced
finite-character warp with precisely those two old endpoints removed. -/
theorem finite_reduction_of_source_mem_reverseReachable
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W) (hYfin : Gamma.HasFiniteCharacter Y)
    {s : V} (hs : s ∈ Gamma.initialSet W) (hsiso : s ∉ isolatedVertices W)
    (hYpure : ∀ {x y : V}, (x, y) ∈ familyEdges Y →
      y ∉ Gamma.initialSet W ∧ x ∉ Gamma.terminalFrontier W)
    (hreach : s ∈ reverseReachable W Y s) :
    ∃ t ∈ Gamma.terminalFrontier W \ Gamma.vertexSet Y,
      ∃ Q : FiniteColouredOccurrenceWord W Y, Q.IsIntervalSafe ∧
        Q.vertex 0 = s ∧ Q.vertex (Fin.last Q.length) = t ∧
        ∃ U : Set Gamma.DPath, Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
          familyEdges U ⊆ familyEdges W ∪ familyEdges Y ∧
          isolatedVertices U = isolatedVertices W ∧
          Gamma.initialSet U = Gamma.initialSet W \ {s} ∧
          Gamma.terminalFrontier U = Gamma.terminalFrontier W \ {t} := by
  obtain ⟨t, ⟨ht, Q, hQ, hQfirst, hQlast⟩, hroute⟩ := hreach
  let H : DWeb (V ⊕ V) :=
    ⟨residualPortDigraph W Y, ∅, ∅⟩
  let E : Set ((V ⊕ V) × (V ⊕ V)) := {e | ResidualStep W Y e.1 e.2}
  obtain ⟨P⟩ := GroundingRootedReachabilityWarp.exists_rootedPath_of_reflTransGen
    (Gamma := H) (E := E) (A := {Sum.inr t}) (b := Sum.inl s)
    (fun _ h ↦ h) ⟨.inr t, Set.mem_singleton _, hroute⟩
  have hPfirst : P.path.start = .inr t := Set.mem_singleton_iff.mp P.start_mem
  have htiso : t ∉ isolatedVertices W :=
    terminal_not_isolated_of_word hW hsiso ht.2 Q hQfirst hQlast
  obtain ⟨U, hU, hUfin, hUE, hUI, _hUbalance, hUstart, hUfinish⟩ :=
    exists_reducingWarp_of_residualPortPath hW hY hWfin hYfin
      P.path hPfirst P.finish_eq hs hsiso ht.1 htiso hYpure
  refine ⟨t, ht, Q, hQ, hQfirst, hQlast, U, hU, hUfin, ?_, hUI,
    hUstart, hUfinish⟩
  intro e he
  rcases hUE he with he | he
  · exact Or.inl he.1
  · exact Or.inr (forwardEdges_subset_familyEdges P.path he)

#print axioms finish_not_reverseReachable_of_start_not
#print axioms reference_predecessor_not_reverseReachable
#print axioms finite_reduction_of_source_mem_reverseReachable

end Erdos599.ColouredSafeReverseReachability
