import ErdosProblems.Erdos73.MatchingAugmenting

/-! The matching edges on an augmenting path have exactly the odd indices. -/

namespace Erdos73

open SimpleGraph Finset Erdos556
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem IsMatchingAugmentingPath.edge_mem_iff_odd_index {M : Finset (Sym2 V)}
    (hM : EdgeMatching G M) {P : GraphPath G} (hP : IsMatchingAugmentingPath M P)
    (i : ℕ) (hi : i < P.walk.length) :
    s(P.walk.getVert i, P.walk.getVert (i + 1)) ∈ M ↔ i % 2 = 1 := by
  induction i with
  | zero =>
    have hn : s(P.walk.getVert 0, P.walk.getVert 1) ∉ M := by
      intro he
      apply hP.source_uncovered
      exact matchingSupport_mem.mpr ⟨s(P.walk.getVert 0, P.walk.getVert 1), he,
        by simpa only [Walk.getVert_zero] using Sym2.mem_mk_left P.source (P.walk.getVert 1)⟩
    simpa only [Nat.zero_add, Nat.zero_mod, Nat.zero_ne_one, iff_false] using hn
  | succ i ih =>
    have hi' : i < P.walk.length := by omega
    have hprev := ih hi'
    have hv : P.walk.getVert (i + 1) ∈ P.vertexSet :=
      List.mem_toFinset.mpr (P.walk.getVert_mem_support (i + 1))
    have hs : P.walk.getVert (i + 1) ≠ P.source := by
      intro he
      have hh := P.isPath.getVert_injOn (show i + 1 ≤ P.walk.length by omega)
        (show 0 ≤ P.walk.length by omega) (by simpa only [Walk.getVert_zero] using he)
      omega
    have ht : P.walk.getVert (i + 1) ≠ P.target := by
      intro he
      have hh := P.isPath.getVert_injOn (show i + 1 ≤ P.walk.length by omega)
        (show P.walk.length ≤ P.walk.length from le_rfl)
        (by simpa only [Walk.getVert_length] using he)
      omega
    obtain ⟨w, hwM, hwP⟩ := hP.internal_matched _ hv hs ht
    have hnbr : w ∈ P.walk.toSubgraph.neighborSet (P.walk.getVert (i + 1)) :=
      Walk.adj_toSubgraph_iff_mem_edges.mpr (List.mem_toFinset.mp hwP)
    rw [P.isPath.neighborSet_toSubgraph_internal (by omega : i + 1 ≠ 0)
      (by omega : i + 1 < P.walk.length)] at hnbr
    simp only [Nat.add_sub_cancel, Set.mem_insert_iff, Set.mem_singleton_iff] at hnbr
    have hsome : s(P.walk.getVert i, P.walk.getVert (i + 1)) ∈ M ∨
        s(P.walk.getVert (i + 1), P.walk.getVert (i + 1 + 1)) ∈ M := by
      rcases hnbr with rfl | rfl
      · exact Or.inl (by simpa only [Sym2.eq_swap] using hwM)
      · exact Or.inr hwM
    have hnotBoth : ¬ (s(P.walk.getVert i, P.walk.getVert (i + 1)) ∈ M ∧
        s(P.walk.getVert (i + 1), P.walk.getVert (i + 1 + 1)) ∈ M) := by
      rintro ⟨ha, hb⟩
      have he := matching_neighbors_unique hM
        (show s(P.walk.getVert (i + 1), P.walk.getVert i) ∈ M by
          simpa only [Sym2.eq_swap] using ha) hb
      have hh := P.isPath.getVert_injOn (show i ≤ P.walk.length by omega)
        (show i + 1 + 1 ≤ P.walk.length by omega) he
      omega
    change s(P.walk.getVert (i + 1), P.walk.getVert (i + 1 + 1)) ∈ M ↔ (i + 1) % 2 = 1
    constructor
    · intro hn
      have hp : i % 2 ≠ 1 := fun hh => hnotBoth ⟨hprev.mpr hh, hn⟩
      omega
    · intro hn
      rcases hsome with hp | hp
      · have hh := hprev.mp hp
        omega
      · exact hp

end Erdos73
