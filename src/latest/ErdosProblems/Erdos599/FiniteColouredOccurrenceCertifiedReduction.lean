/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeReverseReachability
import ErdosProblems.Erdos599.FiniteColouredOccurrenceReductionTransfer

/-!
# Retaining the residual path of a finite coloured reduction

The ordinary finite branch exposes the safe outward word and the reduced
warp, but forgets the simple residual-port path used to construct that warp.
For a source-changing exchange this path is essential: an arbitrary warp
with the same endpoint profile does not determine how inherited reference
edges arose.

This file keeps the outward word, residual path, and reduced warp in one
existential certificate.  The reduced edge relation is still only a balanced
subrelation of the literal toggle, exactly as in the underlying cyclowarp
decomposition; no converse normalization or Hall assertion is added.
-/

noncomputable section

namespace Erdos599.ColouredSafeReverseReachability

open Set DirectedPath Alternating
open ColouredResidualPortContinuation ColouredResidualPortReduction

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

private theorem terminal_not_isolated_of_coloured_word
    (hW : Gamma.IsWarp W) {s t : V}
    (hs : s ∉ isolatedVertices W) (ht : t ∉ Gamma.vertexSet Y)
    (Q : FiniteColouredOccurrenceWord W Y)
    (hfirst : Q.vertex 0 = s)
    (hlast : Q.vertex (Fin.last Q.length) = t) :
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
          exact ht (hlast' ▸
            (familyEdges_subset_vertexSet_prod Y hedge).1)

/-- A finite reverse-reachable source has a safe outward word and a literal
simple residual path whose toggle produces the displayed reduced warp.  In
particular, every inherited reference edge of a later word can be traced to
this concrete path rather than merely to a union-of-relations bound. -/
theorem exists_certifiedFiniteReduction_of_source_mem_reverseReachable
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (hWfin : Gamma.HasFiniteCharacter W)
    (hYfin : Gamma.HasFiniteCharacter Y)
    {s : V} (hs : s ∈ Gamma.initialSet W)
    (hsiso : s ∉ isolatedVertices W)
    (hYpure : ∀ {x y : V}, (x, y) ∈ familyEdges Y →
      y ∉ Gamma.initialSet W ∧ x ∉ Gamma.terminalFrontier W)
    (hreach : s ∈ reverseReachable W Y s) :
    ∃ t ∈ Gamma.terminalFrontier W \ Gamma.vertexSet Y,
      ∃ Q : FiniteColouredOccurrenceWord W Y,
        Q.IsIntervalSafe ∧ Q.vertex 0 = s ∧
        Q.vertex (Fin.last Q.length) = t ∧
      ∃ P : FinitePath (residualPortDigraph W Y),
        P.start = .inr t ∧ P.finish = .inl s ∧
      ∃ U : Set Gamma.DPath,
        Gamma.IsWarp U ∧ Gamma.HasFiniteCharacter U ∧
        familyEdges U ⊆
          (familyEdges W \ backwardEdges P) ∪ forwardEdges P ∧
        isolatedVertices U = isolatedVertices W ∧
        (∀ x, edgeBalance (familyEdges U) x =
          edgeBalance
            ((familyEdges W \ backwardEdges P) ∪ forwardEdges P) x) ∧
        Gamma.initialSet U = Gamma.initialSet W \ {s} ∧
        Gamma.terminalFrontier U = Gamma.terminalFrontier W \ {t} := by
  obtain ⟨t, ⟨ht, Q, hQ, hQfirst, hQlast⟩, hroute⟩ := hreach
  let H : DWeb (V ⊕ V) := ⟨residualPortDigraph W Y, ∅, ∅⟩
  let E : Set ((V ⊕ V) × (V ⊕ V)) := {e | ResidualStep W Y e.1 e.2}
  obtain ⟨P⟩ :=
    GroundingRootedReachabilityWarp.exists_rootedPath_of_reflTransGen
      (Gamma := H) (E := E) (A := {Sum.inr t}) (b := Sum.inl s)
      (fun _ h ↦ h) ⟨.inr t, Set.mem_singleton _, hroute⟩
  have hPfirst : P.path.start = .inr t :=
    Set.mem_singleton_iff.mp P.start_mem
  have htiso : t ∉ isolatedVertices W :=
    terminal_not_isolated_of_coloured_word hW hsiso ht.2 Q hQfirst hQlast
  obtain ⟨U, hU, hUfin, hUE, hUI, hUbalance, hUstart, hUfinish⟩ :=
    exists_reducingWarp_of_residualPortPath hW hY hWfin hYfin
      P.path hPfirst P.finish_eq hs hsiso ht.1 htiso hYpure
  exact ⟨t, ht, Q, hQ, hQfirst, hQlast, P.path, hPfirst, P.finish_eq,
    U, hU, hUfin, hUE, hUI, hUbalance, hUstart, hUfinish⟩

#print axioms exists_certifiedFiniteReduction_of_source_mem_reverseReachable

end Erdos599.ColouredSafeReverseReachability

namespace Erdos599.Alternating.FiniteColouredOccurrenceWord

open Set DirectedPath
open ColouredResidualPortReduction

universe u

variable {V : Type u} {Gamma : DWeb V} {W U Y : Set Gamma.DPath}

/-- Actual later-word forward edges which were inserted by the displayed
residual path.  This finite set is the well-founded measure for a prospective
source-changing cancellation proof. -/
def residualPathInheritedEdges
    (P : FinitePath (residualPortDigraph W Y))
    (Q : FiniteColouredOccurrenceWord U Y) : Set (V × V) :=
  Q.forwardEdges ∩ ColouredResidualPortReduction.forwardEdges P

theorem residualPathInheritedEdges_finite
    (P : FinitePath (residualPortDigraph W Y))
    (Q : FiniteColouredOccurrenceWord U Y) :
    (residualPathInheritedEdges P Q).Finite := by
  simpa [residualPathInheritedEdges] using
    Q.forwardEdges_finite.inter_of_left
      (ColouredResidualPortReduction.forwardEdges P)

/-- Vanishing of the concrete inherited-edge measure is exactly the easy
original-forward branch, provided `U` is the actual residual reduction. -/
theorem residualPathInheritedEdges_eq_empty_iff
    (P : FinitePath (residualPortDigraph W Y))
    (Q : FiniteColouredOccurrenceWord U Y)
    (hUE : familyEdges U ⊆
      (familyEdges W \ ColouredResidualPortReduction.backwardEdges P) ∪
        ColouredResidualPortReduction.forwardEdges P) :
    residualPathInheritedEdges P Q = ∅ ↔
      Q.forwardEdges ⊆ familyEdges W := by
  constructor
  · intro hempty e heQ
    rcases hUE (Q.forwardEdges_subset_familyEdges heQ) with heOld | hePath
    · exact heOld.1
    · have : e ∈ residualPathInheritedEdges P Q := ⟨heQ, hePath⟩
      simpa [hempty] using this
  · intro hOriginal
    apply Set.Subset.antisymm
    · intro e he
      exact False.elim <|
        Set.disjoint_left.1
          (ColouredResidualPortReduction.forwardEdges_disjoint_familyEdges P)
          he.2 (hOriginal he.1)
    · exact Set.empty_subset _

/-- The hard branch of transfer through a certified residual reduction can
be located on the actual residual path, not merely somewhere in the
reference relation.  The same edge occurs in opposite colours in the later
word.  This is the concrete pivot on which a decreasing source-changing
surgery has to operate. -/
theorem residualReduction_original_or_pathPivot
    (P : FinitePath (residualPortDigraph W Y))
    {Q : FiniteColouredOccurrenceWord U Y} (hQ : Q.IsIntervalSafe)
    (hUE : familyEdges U ⊆
      (familyEdges W \ ColouredResidualPortReduction.backwardEdges P) ∪
        ColouredResidualPortReduction.forwardEdges P) :
    Q.forwardEdges ⊆ familyEdges W ∨
      ∃ (e : V × V) (i j : Fin Q.length),
        e ∈ ColouredResidualPortReduction.forwardEdges P ∧
          e ∉ familyEdges W ∧ e ∈ familyEdges Y ∧
          Q.direction i = .forward ∧ Q.direction j = .backward ∧
          Q.actualEdge i = e ∧ Q.actualEdge j = e ∧ i ≠ j := by
  by_cases hOriginal : Q.forwardEdges ⊆ familyEdges W
  · exact Or.inl hOriginal
  · obtain ⟨e, heF, heNotW⟩ := Set.not_subset.mp hOriginal
    have heU : e ∈ familyEdges U := Q.forwardEdges_subset_familyEdges heF
    have hePath : e ∈ ColouredResidualPortReduction.forwardEdges P := by
      rcases hUE heU with heOld | hePath
      · exact False.elim (heNotW heOld.1)
      · exact hePath
    have heY : e ∈ familyEdges Y :=
      ColouredResidualPortReduction.forwardEdges_subset_familyEdges P hePath
    have heR : e ∈ Q.backwardEdges := by
      rcases e with ⟨x, y⟩
      exact hQ.incoming_removed heF heY
    obtain ⟨i, j, hi, hj, hie, hje, hij⟩ :=
      Q.exists_oppositeOccurrences_of_mem_forwardEdges_inter_backwardEdges
        heF heR
    exact Or.inr ⟨e, i, j, hePath, heNotW, heY,
      hi, hj, hie, hje, hij⟩

#print axioms residualReduction_original_or_pathPivot
#print axioms residualPathInheritedEdges_eq_empty_iff

end Erdos599.Alternating.FiniteColouredOccurrenceWord
