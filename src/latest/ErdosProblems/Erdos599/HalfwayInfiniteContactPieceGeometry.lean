/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayInfiniteContactCoordinates
import ErdosProblems.Erdos599.HalfwayInfiniteInputDirectionEdgeCoverage
import ErdosProblems.Erdos599.HalfwayFiniteInputDirectionEdgeCoverage

/-!
# Geometry of the actual infinite contact pieces

Consecutive enumerated contacts have no closing-set vertex in their hammock
interior.  The final suffix in the eventual case has no later contact.
Literal coordinate restriction preserves vertices, edges, and their forward
or backward direction in the original infinite compressor trace.
-/

noncomputable section

open Set

namespace Erdos599.Alternating.RunCompressor.InfiniteInput

open DirectedPath

universe u

variable {V : Type u} {D : Digraph V}

theorem coordinateInterval_directionEdges_subset (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b) (d : Direction) :
    (AltPath.finite
      (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace
      ).directionEdges d ⊆
      (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace).directionEdges d := by
  intro e he
  obtain ⟨k, hkcolour, rfl⟩ :=
    (S.coordinateInterval a b hab).mem_directionEdges_exists_rawEdge d he
  rw [S.coordinateInterval_rawEdge a b hab k]
  have hjcolour : S.colour (a + k.1) = d := by
    simpa [coordinateInterval] using hkcolour
  simpa only [hjcolour] using S.rawEdge_mem_directionEdges hchange (a + k.1)

theorem coordinateInterval_vertexSet_subset (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b) :
    (AltPath.finite
      (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace).vertexSet ⊆
      (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace).vertexSet := by
  rw [AltPath.vertexSet, S.coordinateInterval_trace_vertexSet,
    AltPath.vertexSet, S.toInfiniteTrace_vertexSet hchange]
  rintro x ⟨n, _hn, rfl⟩
  exact ⟨n, rfl⟩

theorem coordinateInterval_edgeSet_subset (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a b : Nat) (hab : a < b) :
    (AltPath.finite
      (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace).edgeSet ⊆
      (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace).edgeSet := by
  intro e he
  change e ∈ (S.coordinateInterval a b hab).toFiniteRunWalk.toFiniteTrace.edgeSet at he
  rw [S.coordinateInterval_trace_edgeSet a b hab] at he
  obtain ⟨n, _hlo, _hhi, rfl⟩ := he
  exact S.rawEdge_mem_toInfiniteTrace hchange n

theorem mem_directionEdges_exists_rawEdge (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (d : Direction) {e : V × V}
    (he : e ∈ (AltPath.infinite
      (S.toInfiniteRunWalk hchange).toInfiniteTrace).directionEdges d) :
    ∃ n, S.colour n = d ∧ e = S.rawEdge n := by
  simp only [AltPath.directionEdges, AltPath.links, InfiniteTrace.links,
    Set.mem_iUnion, Set.mem_range] at he
  obtain ⟨l, ⟨i, rfl⟩, hdir, he⟩ := he
  have hrun : S.colour (runBoundary S.colour hchange i) = d :=
    (S.toInfiniteRunWalk_run_direction hchange i).symm.trans hdir
  change e ∈ (S.projectedRun hchange i).link.path.edgeSet at he
  cases d with
  | forward =>
      rw [S.projectedRun_edgeSet_eq_forward hchange i hrun] at he
      obtain ⟨n, hlo, hhi, rfl⟩ := he
      have hc := colour_eq_on_run S.colour hchange hlo hhi
      exact ⟨n, hc.trans hrun, by simp [rawEdge, hc.trans hrun]⟩
  | backward =>
      rw [S.projectedRun_edgeSet_eq_backward hchange i hrun] at he
      obtain ⟨n, hlo, hhi, rfl⟩ := he
      have hc := colour_eq_on_run S.colour hchange hlo hhi
      exact ⟨n, hc.trans hrun, by simp [rawEdge, hc.trans hrun]⟩

theorem shift_directionEdges_subset (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a : Nat) (d : Direction) :
    (AltPath.infinite ((S.shift a).toInfiniteRunWalk
      (S.shift_changes hchange a)).toInfiniteTrace).directionEdges d ⊆
      (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace).directionEdges d := by
  intro e he
  obtain ⟨n, hncolour, rfl⟩ :=
    (S.shift a).mem_directionEdges_exists_rawEdge
      (S.shift_changes hchange a) d he
  rw [S.shift_rawEdge a n]
  have hcolour : S.colour (a + n) = d := by
    simpa only [shift_colour] using hncolour
  simpa only [hcolour] using S.rawEdge_mem_directionEdges hchange (a + n)

theorem shift_vertexSet_subset (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a : Nat) :
    (AltPath.infinite ((S.shift a).toInfiniteRunWalk
      (S.shift_changes hchange a)).toInfiniteTrace).vertexSet ⊆
      (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace).vertexSet := by
  rw [AltPath.vertexSet, S.shift_trace_vertexSet hchange a,
    AltPath.vertexSet, S.toInfiniteTrace_vertexSet hchange]
  rintro x ⟨n, _hn, rfl⟩
  exact ⟨n, rfl⟩

theorem shift_edgeSet_subset (S : InfiniteInput D)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n)
    (a : Nat) :
    (AltPath.infinite ((S.shift a).toInfiniteRunWalk
      (S.shift_changes hchange a)).toInfiniteTrace).edgeSet ⊆
      (AltPath.infinite
        (S.toInfiniteRunWalk hchange).toInfiniteTrace).edgeSet := by
  intro e he
  change e ∈ ((S.shift a).toInfiniteRunWalk
    (S.shift_changes hchange a)).toInfiniteTrace.edgeSet at he
  rw [S.shift_trace_edgeSet hchange a] at he
  obtain ⟨n, _hn, rfl⟩ := he
  exact S.rawEdge_mem_toInfiniteTrace hchange n

namespace EventualContactCoordinates

variable {S : InfiniteInput D} {X : Set V}

theorem no_contact_between (E : EventualContactCoordinates S X)
    (i : Fin E.count) {n : Nat}
    (hlo : E.coord i.castSucc < n) (hhi : n < E.coord i.succ) :
    S.vertex n ∉ X := by
  intro hnX
  obtain ⟨j, hj⟩ := E.complete hnX
  rw [← hj] at hlo hhi
  have hij : i.castSucc < j := E.strictMono_coord.lt_iff_lt.mp hlo
  have hji : j < i.succ := E.strictMono_coord.lt_iff_lt.mp hhi
  change i.1 < j.1 at hij
  change j.1 < i.1 + 1 at hji
  omega

theorem interval_hammockInterior_disjoint
    (E : EventualContactCoordinates S X) (i : Fin E.count) :
    Disjoint
      (Blueprint.hammockInterior (S.vertex (E.coord i.castSucc))
        (.vertex (S.vertex (E.coord i.succ)))
        (.finite (E.interval i).toFiniteRunWalk.toFiniteTrace)) X := by
  rw [Set.disjoint_left]
  intro x hx hxX
  have hxPath := hx.1
  change x ∈ (E.interval i).toFiniteRunWalk.toFiniteTrace.vertexSet at hxPath
  rw [EventualContactCoordinates.interval,
    S.coordinateInterval_trace_vertexSet] at hxPath
  obtain ⟨n, hn, hxn⟩ := hxPath
  have hna : n ≠ E.coord i.castSucc := by
    intro heq
    apply hx.2
    left
    rw [← hxn, heq]
  have hnb : n ≠ E.coord i.succ := by
    intro heq
    apply hx.2
    right
    rw [← hxn, heq]
    rfl
  exact E.no_contact_between i
    (lt_of_le_of_ne hn.1 (Ne.symm hna))
    (lt_of_le_of_ne hn.2 hnb) (by simpa [hxn] using hxX)

theorem suffix_hammockInterior_disjoint
    (E : EventualContactCoordinates S X)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n) :
    Disjoint
      (Blueprint.hammockInterior (S.vertex E.last) .infinity
        (.infinite ((S.shift E.last).toInfiniteRunWalk
          (S.shift_changes hchange E.last)).toInfiniteTrace)) X := by
  rw [Set.disjoint_left]
  intro x hx hxX
  have hxPath := hx.1
  change x ∈ ((S.shift E.last).toInfiniteRunWalk
    (S.shift_changes hchange E.last)).toInfiniteTrace.vertexSet at hxPath
  rw [S.shift_trace_vertexSet hchange E.last] at hxPath
  obtain ⟨n, hn, hxn⟩ := hxPath
  have hnNe : n ≠ E.last := by
    intro heq
    apply hx.2
    simp only [Blueprint.hammockEndpoints, Set.mem_singleton_iff]
    rw [← hxn, heq]
  exact E.no_contact_after_last (lt_of_le_of_ne hn hnNe.symm)
    (by simpa [hxn] using hxX)

theorem suffix_not_subset
    (E : EventualContactCoordinates S X)
    (hchange : ∀ n, ∃ m, n < m ∧ S.colour m ≠ S.colour n) :
    ¬ (AltPath.infinite ((S.shift E.last).toInfiniteRunWalk
      (S.shift_changes hchange E.last)).toInfiniteTrace).vertexSet ⊆ X := by
  intro hsubset
  have hmem : S.vertex (E.last + 1) ∈
      (AltPath.infinite ((S.shift E.last).toInfiniteRunWalk
        (S.shift_changes hchange E.last)).toInfiniteTrace).vertexSet := by
    change S.vertex (E.last + 1) ∈ ((S.shift E.last).toInfiniteRunWalk
      (S.shift_changes hchange E.last)).toInfiniteTrace.vertexSet
    rw [S.shift_trace_vertexSet hchange E.last]
    exact ⟨E.last + 1, Nat.le_add_right _ _, rfl⟩
  exact E.no_contact_after_last (Nat.lt_succ_self E.last) (hsubset hmem)

end EventualContactCoordinates

namespace OmegaContactCoordinates

variable {S : InfiniteInput D} {X : Set V}

theorem no_contact_between (E : OmegaContactCoordinates S X)
    (i : Nat) {n : Nat}
    (hlo : E.coord i < n) (hhi : n < E.coord (i + 1)) :
    S.vertex n ∉ X := by
  intro hnX
  obtain ⟨j, hj⟩ := E.complete hnX
  rw [← hj] at hlo hhi
  have hij : i < j := E.strictMono_coord.lt_iff_lt.mp hlo
  have hji : j < i + 1 := E.strictMono_coord.lt_iff_lt.mp hhi
  omega

theorem interval_hammockInterior_disjoint
    (E : OmegaContactCoordinates S X) (i : Nat) :
    Disjoint
      (Blueprint.hammockInterior (S.vertex (E.coord i))
        (.vertex (S.vertex (E.coord (i + 1))))
        (.finite (E.interval i).toFiniteRunWalk.toFiniteTrace)) X := by
  rw [Set.disjoint_left]
  intro x hx hxX
  have hxPath := hx.1
  change x ∈ (E.interval i).toFiniteRunWalk.toFiniteTrace.vertexSet at hxPath
  rw [OmegaContactCoordinates.interval,
    S.coordinateInterval_trace_vertexSet] at hxPath
  obtain ⟨n, hn, hxn⟩ := hxPath
  have hna : n ≠ E.coord i := by
    intro heq
    apply hx.2
    left
    rw [← hxn, heq]
  have hnb : n ≠ E.coord (i + 1) := by
    intro heq
    apply hx.2
    right
    rw [← hxn, heq]
    rfl
  exact E.no_contact_between i
    (lt_of_le_of_ne hn.1 (Ne.symm hna))
    (lt_of_le_of_ne hn.2 hnb) (by simpa [hxn] using hxX)

end OmegaContactCoordinates

#print axioms coordinateInterval_directionEdges_subset
#print axioms shift_directionEdges_subset
#print axioms EventualContactCoordinates.interval_hammockInterior_disjoint
#print axioms EventualContactCoordinates.suffix_hammockInterior_disjoint
#print axioms EventualContactCoordinates.suffix_not_subset
#print axioms OmegaContactCoordinates.interval_hammockInterior_disjoint

end Erdos599.Alternating.RunCompressor.InfiniteInput
