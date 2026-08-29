/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.InfiniteColouredOccurrenceLimit

/-!
# Pointwise balance of an infinite coloured occurrence word

At a fixed ambient vertex there are at most two chronological occurrences:
one forward occurrence, controlled by the outgoing edge of the forward warp,
and one backward occurrence, controlled by the incoming edge of the reference
warp.  This finite-occurrence fact lets finite-prefix balance pass to the
omega limit without an infinite sum.
-/

namespace Erdos599.Alternating

open Set DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

namespace InfiniteColouredOccurrenceWord

/-- A fixed ambient vertex occurs only finitely often in an infinite coloured
word.  Repeated ambient vertices remain allowed globally. -/
theorem vertex_preimage_finite (Q : InfiniteColouredOccurrenceWord W Y)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y) (x : V) :
    {n : ℕ | Q.vertex n = x}.Finite := by
  let S : Set ℕ := {n | Q.vertex n = x}
  have hinj : Set.InjOn Q.direction S := by
    intro i hi j hj hd
    change Q.vertex i = x at hi
    change Q.vertex j = x at hj
    have hedge : Q.actualEdge i = Q.actualEdge j := by
      cases hdi : Q.direction i with
      | forward =>
          have hdj : Q.direction j = .forward := hd.symm.trans hdi
          have ht : Q.vertex (i + 1) = Q.vertex (j + 1) :=
            (IsWarp.familyEdges_biUnique hW).2
              (by simpa [hdi, hi] using Q.actualEdge_spec i)
              (by simpa [hdj, hj] using Q.actualEdge_spec j)
          simp [InfiniteColouredOccurrenceWord.actualEdge, hdi, hdj, hi, hj, ht]
      | backward =>
          have hdj : Q.direction j = .backward := hd.symm.trans hdi
          have hs : Q.vertex (i + 1) = Q.vertex (j + 1) :=
            (IsWarp.familyEdges_biUnique hY).1
              (by simpa [hdi, hi] using Q.actualEdge_spec i)
              (by simpa [hdj, hj] using Q.actualEdge_spec j)
          simp [InfiniteColouredOccurrenceWord.actualEdge, hdi, hdj, hi, hj, hs]
    exact Q.occurrence_injective (Prod.ext hd hedge)
  have himage : (Q.direction '' S).Finite :=
    (Set.finite_singleton (.backward : Direction)).insert .forward |>.subset (by
      intro d hd
      cases d <;> simp)
  simpa [S] using Set.Finite.of_finite_image himage hinj

#print axioms vertex_preimage_finite

end InfiniteColouredOccurrenceWord

namespace FiniteColouredOccurrencePrefixChain

/-- The terminal occurrence of sufficiently late finite prefixes avoids any
fixed ambient vertex. -/
theorem eventually_last_ne (C : FiniteColouredOccurrencePrefixChain W Y)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y) (x : V) :
    ∃ N, ∀ n, N ≤ n →
      (C.stage n).vertex (Fin.last (C.stage n).length) ≠ x := by
  have hfinite := C.limit.vertex_preimage_finite hW hY x
  obtain ⟨B, hB⟩ := hfinite.bddAbove
  refine ⟨B + 1, ?_⟩
  intro n hn heq
  have hlimit : C.limit.vertex (C.stage n).length = x := by
    have hstage := C.stage_vertex_eq_limit n (Fin.last (C.stage n).length)
    simpa [heq] using hstage.symm
  have hle : (C.stage n).length ≤ B := hB hlimit
  have hnle := C.index_le_length n
  omega

private theorem exists_eventually_edgeBalance_eq_iUnion
    (A : ℕ → Set (V × V)) (hmono : Monotone A) (x : V) :
    ∃ N, ∀ n, N ≤ n →
      edgeBalance (A n) x = edgeBalance (⋃ k, A k) x := by
  have hout : ∃ N, ∀ n, N ≤ n →
      (HasOutgoing (A n) x ↔ HasOutgoing (⋃ k, A k) x) := by
    by_cases h : HasOutgoing (⋃ k, A k) x
    · obtain ⟨y, hy⟩ := h
      rcases Set.mem_iUnion.1 hy with ⟨N, hyN⟩
      refine ⟨N, fun n hn ↦ ⟨?_, fun _ ↦ ⟨y, hmono hn hyN⟩⟩⟩
      rintro ⟨z, hz⟩
      exact ⟨z, Set.mem_iUnion.2 ⟨n, hz⟩⟩
    · refine ⟨0, fun n _ ↦ ⟨?_, fun hu ↦ False.elim (h hu)⟩⟩
      rintro ⟨z, hz⟩
      exact ⟨z, Set.mem_iUnion.2 ⟨n, hz⟩⟩
  have hin : ∃ N, ∀ n, N ≤ n →
      (HasIncoming (A n) x ↔ HasIncoming (⋃ k, A k) x) := by
    by_cases h : HasIncoming (⋃ k, A k) x
    · obtain ⟨y, hy⟩ := h
      rcases Set.mem_iUnion.1 hy with ⟨N, hyN⟩
      refine ⟨N, fun n hn ↦ ⟨?_, fun _ ↦ ⟨y, hmono hn hyN⟩⟩⟩
      rintro ⟨z, hz⟩
      exact ⟨z, Set.mem_iUnion.2 ⟨n, hz⟩⟩
    · refine ⟨0, fun n _ ↦ ⟨?_, fun hu ↦ False.elim (h hu)⟩⟩
      rintro ⟨z, hz⟩
      exact ⟨z, Set.mem_iUnion.2 ⟨n, hz⟩⟩
  obtain ⟨No, hNo⟩ := hout
  obtain ⟨Ni, hNi⟩ := hin
  refine ⟨max No Ni, fun n hn ↦ ?_⟩
  have ho := hNo n ((le_max_left _ _).trans hn)
  have hi := hNi n ((le_max_right _ _).trans hn)
  simp only [edgeBalance]
  rw [propext ho, propext hi]

/-- At every vertex, the signed coloured-edge balance of the omega limit is
one at its initial occurrence and zero elsewhere. -/
theorem limit_edgeBalance_forward_sub_backward
    (C : FiniteColouredOccurrencePrefixChain W Y)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y) (x : V) :
    edgeBalance C.limit.forwardEdges x -
        edgeBalance C.limit.backwardEdges x =
      propInt (x = C.limit.vertex 0) := by
  obtain ⟨NF, hNF⟩ := exists_eventually_edgeBalance_eq_iUnion
    (fun n ↦ (C.stage n).forwardEdges) C.forwardEdges_mono x
  obtain ⟨NR, hNR⟩ := exists_eventually_edgeBalance_eq_iUnion
    (fun n ↦ (C.stage n).backwardEdges) C.backwardEdges_mono x
  obtain ⟨NE, hNE⟩ := C.eventually_last_ne hW hY x
  let N := max (max NF NR) NE
  have hNFN : NF ≤ N := (le_max_left NF NR).trans (le_max_left _ _)
  have hNRN : NR ≤ N := (le_max_right NF NR).trans (le_max_left _ _)
  have hNEN : NE ≤ N := le_max_right _ _
  have hF := hNF N hNFN
  have hR := hNR N hNRN
  have hlast := hNE N hNEN
  have hfirst := C.stage_vertex_eq_limit N
    (0 : Fin ((C.stage N).length + 1))
  have hfinite := (C.stage N).edgeBalance_forward_sub_backward hW hY x
  have hF' : edgeBalance (C.stage N).forwardEdges x =
      edgeBalance C.limit.forwardEdges x := by
    rw [C.limit_forwardEdges_eq_iUnion]
    exact hF
  have hR' : edgeBalance (C.stage N).backwardEdges x =
      edgeBalance C.limit.backwardEdges x := by
    rw [C.limit_backwardEdges_eq_iUnion]
    exact hR
  rw [← hF', ← hR', hfinite, hfirst]
  have hxlast : x ≠
      (C.stage N).vertex (Fin.last (C.stage N).length) := hlast.symm
  simp [propInt, hxlast]
  rfl

#print axioms eventually_last_ne
#print axioms limit_edgeBalance_forward_sub_backward

end FiniteColouredOccurrencePrefixChain
end Erdos599.Alternating
