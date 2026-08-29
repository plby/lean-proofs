/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayPostClosureLocalMatchingOrbit

/-!
# Exact boundary information for stopped outside-local matching orbits

A stopped matching orbit has no outgoing edge in the symmetric difference.
Thus, at a sending terminal, every forward matching edge is also a reference
matching edge; at a receiving terminal, every reference matching edge is also
a forward matching edge.  For literal path-family edges the identity case is
impossible, so the edge itself belongs to both path families.

This is the precise information available from the stopped alternative.  It
does not identify a compiled alternating path or assert a terminal boundary
condition.  The projected-return alternative similarly records only which of
the two copies of the starting ambient vertex is its terminal port.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace TwoWarpMatchingTraversal

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- The endpoints of a literal path-family edge are distinct. -/
theorem familyEdge_endpoints_ne {W : Set Gamma.DPath} {x y : V}
    (hxy : (x, y) ∈ familyEdges W) : x ≠ y := by
  simp only [familyEdges, Set.mem_iUnion] at hxy
  obtain ⟨p, _hpW, hxy⟩ := hxy
  cases p with
  | inl p =>
      obtain ⟨n, hn, hnx, hny⟩ :=
        DirectedPath.Walk.exists_adjacent_getElem_of_mem_edgeSet p.walk hxy
      intro hxyEq
      have hn0 : n < p.walk.support.length := by omega
      have hget :
          p.walk.support[n]'hn0 = p.walk.support[n + 1]'hn := by
        exact hnx.trans (hxyEq.trans hny.symm)
      have hindex : (⟨n, hn0⟩ : Fin p.walk.support.length) =
          ⟨n + 1, hn⟩ := p.isPath.get_inj_iff.mp hget
      have hval := congrArg Fin.val hindex
      exact Nat.ne_of_lt (Nat.lt_succ_self n) hval
  | inr r =>
      obtain ⟨n, hn⟩ := hxy
      intro hxyEq
      have hvalue : r n = r (n + 1) :=
        (congrArg Prod.fst hn).symm.trans
          (hxyEq.trans (congrArg Prod.snd hn))
      have hindex := r.injective hvalue
      omega

namespace FinitePortPrefix

variable {W Y : Set Gamma.DPath} {root : V}

/-- If a stopped prefix ends at a sending port, every matching edge of the
forward family there is also a matching edge of the reference family. -/
theorem matchingEdge_reference_of_terminal_stopped_inl
    (P : FinitePortPrefix W Y root)
    (hstop : ¬ ∃ b, Step W Y
      (P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩) b)
    {x y : V}
    (hterminal : P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩ = .inl x)
    (hxy : matchingEdge W x y) : matchingEdge Y x y := by
  by_contra hnot
  apply hstop
  refine ⟨.inr y, ?_⟩
  rw [hterminal]
  exact ⟨hxy, hnot⟩

/-- If a stopped prefix ends at a receiving port, every matching edge of the
reference family there is also a matching edge of the forward family. -/
theorem matchingEdge_forward_of_terminal_stopped_inr
    (P : FinitePortPrefix W Y root)
    (hstop : ¬ ∃ b, Step W Y
      (P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩) b)
    {x y : V}
    (hterminal : P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩ = .inr y)
    (hxy : matchingEdge Y x y) : matchingEdge W x y := by
  by_contra hnot
  apply hstop
  refine ⟨.inl x, ?_⟩
  rw [hterminal]
  exact ⟨hxy, hnot⟩

/-- Literal forward edges at a stopped sending terminal are common edges of
the two path families. -/
theorem familyEdge_reference_of_terminal_stopped_inl
    (P : FinitePortPrefix W Y root)
    (hstop : ¬ ∃ b, Step W Y
      (P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩) b)
    {x y : V}
    (hterminal : P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩ = .inl x)
    (hxy : (x, y) ∈ familyEdges W) : (x, y) ∈ familyEdges Y := by
  have hmatch := P.matchingEdge_reference_of_terminal_stopped_inl
    hstop hterminal (matchingEdge_actual hxy)
  rcases hmatch with hactual | hidentity
  · exact hactual
  · exact False.elim (familyEdge_endpoints_ne hxy hidentity.1)

/-- Literal reference edges at a stopped receiving terminal are common edges
of the two path families. -/
theorem familyEdge_forward_of_terminal_stopped_inr
    (P : FinitePortPrefix W Y root)
    (hstop : ¬ ∃ b, Step W Y
      (P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩) b)
    {x y : V}
    (hterminal : P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩ = .inr y)
    (hxy : (x, y) ∈ familyEdges Y) : (x, y) ∈ familyEdges W := by
  have hmatch := P.matchingEdge_forward_of_terminal_stopped_inr
    hstop hterminal (matchingEdge_actual hxy)
  rcases hmatch with hactual | hidentity
  · exact hactual
  · exact False.elim (familyEdge_endpoints_ne hxy hidentity.1)

end FinitePortPrefix

namespace FiniteProjectedReturn

variable {W Y : Set Gamma.DPath} {X : Set V} {root : V}

/-- A projected return ends at one of the two copies of its starting ambient
vertex.  No stronger copy equality follows from projected return alone. -/
theorem terminal_port_eq_inl_or_inr
    (P : FiniteProjectedReturn W Y X root) :
    P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩ = .inl root ∨
      P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩ = .inr root := by
  cases hport : P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩ with
  | inl x =>
      left
      have hx : x = root := by
        simpa [projectPort, hport] using P.terminal_projects_root
      simpa [hport, hx]
  | inr x =>
      right
      have hx : x = root := by
        simpa [projectPort, hport] using P.terminal_projects_root
      simpa [hport, hx]

end FiniteProjectedReturn

#print axioms familyEdge_endpoints_ne
#print axioms FinitePortPrefix.matchingEdge_reference_of_terminal_stopped_inl
#print axioms FinitePortPrefix.matchingEdge_forward_of_terminal_stopped_inr
#print axioms FinitePortPrefix.familyEdge_reference_of_terminal_stopped_inl
#print axioms FinitePortPrefix.familyEdge_forward_of_terminal_stopped_inr
#print axioms FiniteProjectedReturn.terminal_port_eq_inl_or_inr

end TwoWarpMatchingTraversal

namespace Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment

open DirectedPath TwoWarpMatchingTraversal
open _root_.Erdos599.Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {globalZ seed : Set V} {z : V}
variable {root : V}
variable {Rlimit : LimitMoving931GlobalClosure C globalZ seed}
variable {T : PostClosureIntervalTransaction C globalZ seed z
  Rlimit.toDynamicMoving931GlobalClosure}

/-- Actual stopped sending ports have no interval-row continuation exclusive
from the outside-local reference: every literal continuation is common. -/
theorem outsideLocalStopped_inl_commonEdge
    (P : FinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) root)
    (hstop : ¬ ∃ b, Step T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet)
      (P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩) b)
    {x y : V}
    (hterminal : P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩ = .inl x)
    (hxy : (x, y) ∈ familyEdges T.interval.ambientInterval) :
    (x, y) ∈ familyEdges
      (outsideReference T.intervalReference Rlimit.closedSet) :=
  P.familyEdge_reference_of_terminal_stopped_inl hstop hterminal hxy

/-- Actual stopped receiving ports have no outside-reference continuation
exclusive from the interval row: every literal continuation is common. -/
theorem outsideLocalStopped_inr_commonEdge
    (P : FinitePortPrefix T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet) root)
    (hstop : ¬ ∃ b, Step T.interval.ambientInterval
      (outsideReference T.intervalReference Rlimit.closedSet)
      (P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩) b)
    {x y : V}
    (hterminal : P.port ⟨P.lastIndex, Nat.lt_succ_self _⟩ = .inr y)
    (hxy : (x, y) ∈ familyEdges
      (outsideReference T.intervalReference Rlimit.closedSet)) :
    (x, y) ∈ familyEdges T.interval.ambientInterval :=
  P.familyEdge_forward_of_terminal_stopped_inr hstop hterminal hxy

#print axioms outsideLocalStopped_inl_commonEdge
#print axioms outsideLocalStopped_inr_commonEdge

end Blueprint.LinkageBlueprint.PostClosureMacroCompressorAssignment
end Erdos599
