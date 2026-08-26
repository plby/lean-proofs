import ErdosProblems.Erdos73.OddPathLayers
import ErdosProblems.Erdos73.FiniteSequencePath
import ErdosProblems.Erdos73.OddTerminalPathsDefs

/-! Project doubled-graph augmenting paths to simple odd terminal paths. -/

namespace Erdos73

open SimpleGraph Finset Erdos556 OddPathVertex
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A : Finset V}
variable {P : GraphPath (oddPathAuxiliary G A)}

theorem exists_oddTerminalPath_of_augmenting
    (hP : IsMatchingAugmentingPath (oddPathBaseMatching A) P) :
    ∃ Q : GraphPath G, IsOddTerminalPath A Q ∧
      Q.source = projection P.source ∧ Q.target = projection P.target ∧
      Q.vertexSet ⊆ P.vertexSet.image projection := by
  obtain ⟨t, hlen⟩ := oddPathAugmenting_length_mod_four hP
  let ix (i : Fin (2 * t + 2)) : ℕ := 2 * i.val - 1
  let f (i : Fin (2 * t + 2)) : V := projection (P.walk.getVert (ix i))
  have hix (i : Fin (2 * t + 2)) : ix i ≤ P.walk.length := by
    dsimp only [ix]
    have hi := i.isLt
    omega
  have hix_inj : Function.Injective ix := by
    intro i j he
    apply Fin.ext
    dsimp only [ix] at he
    omega
  have hf0 : f 0 = projection P.source := by
    simp only [f, ix, Fin.val_zero, Nat.mul_zero, Nat.zero_sub, Walk.getVert_zero]
  have hflast : f (Fin.last (2 * t + 1)) = projection P.target := by
    have he : ix (Fin.last (2 * t + 1)) = P.walk.length := by dsimp only [ix]; simp; omega
    simp only [f, he, Walk.getVert_length]
  have hfinj : Function.Injective f := by
    intro i j he
    change projection (P.walk.getVert (ix i)) = projection (P.walk.getVert (ix j)) at he
    rcases projection_eq_iff.mp he with he | he
    · exact hix_inj (P.isPath.getVert_injOn (hix i) (hix j) he)
    · by_cases hj0 : ix j = 0
      · have hm : mate (P.walk.getVert (ix j)) = P.walk.getVert (ix j) := by
          rw [hj0, Walk.getVert_zero]
          exact (mate_eq_self_iff _).mpr (oddPathAugmenting_source_terminal hP)
        rw [hm] at he
        exact hix_inj (P.isPath.getVert_injOn (hix i) (hix j) he)
      · by_cases hjlast : ix j = P.walk.length
        · have hm : mate (P.walk.getVert (ix j)) = P.walk.getVert (ix j) := by
            rw [hjlast, Walk.getVert_length]
            exact (mate_eq_self_iff _).mpr (oddPathAugmenting_target_terminal hP)
          rw [hm] at he
          exact hix_inj (P.isPath.getVert_injOn (hix i) (hix j) he)
        · have hjlt : ix j < P.walk.length := lt_of_le_of_ne (hix j) hjlast
          have hjodd : ix j % 2 = 1 := by dsimp only [ix] at hj0 ⊢; omega
          have hm := (mem_oddPathBaseMatching_iff _ _).mp
            ((hP.edge_mem_iff_odd_index (oddPathBaseMatching_isMatching G A) (ix j) hjlt).mpr hjodd)
          rw [← hm.1] at he
          have hidx := P.isPath.getVert_injOn (hix i)
            (show ix j + 1 ≤ P.walk.length by omega) he
          dsimp only [ix] at hidx hj0
          omega
  have hadj : ∀ i (hi : i + 1 < 2 * t + 2), G.Adj
      (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩) := by
    intro i hi
    have hile : 2 * i < P.walk.length := by omega
    have haux := P.walk.toSubgraph.adj_sub (P.walk.toSubgraph_adj_getVert hile)
    have hnot : s(P.walk.getVert (2 * i), P.walk.getVert (2 * i + 1)) ∉
        oddPathBaseMatching A := by
      intro hm
      have hp := (hP.edge_mem_iff_odd_index (oddPathBaseMatching_isMatching G A)
        (2 * i) hile).mp hm
      omega
    have hedge := (oddPathAuxiliary_adj_of_not_matching haux hnot).2
    have hnext : ix ⟨i + 1, hi⟩ = 2 * i + 1 := by dsimp only [ix]; omega
    change G.Adj (projection (P.walk.getVert (2 * i - 1)))
      (projection (P.walk.getVert (ix ⟨i + 1, hi⟩)))
    rw [hnext]
    by_cases hi0 : i = 0
    · simpa only [hi0, Nat.mul_zero, Nat.zero_sub] using hedge
    · have hprevlt : 2 * i - 1 < P.walk.length := by omega
      have hprevodd : (2 * i - 1) % 2 = 1 := by omega
      have hm := (mem_oddPathBaseMatching_iff _ _).mp
        ((hP.edge_mem_iff_odd_index (oddPathBaseMatching_isMatching G A)
          (2 * i - 1) hprevlt).mpr hprevodd)
      have hproj := congrArg projection hm.1
      rw [projection_mate, show 2 * i - 1 + 1 = 2 * i by omega] at hproj
      rw [← hproj]
      exact hedge
  let Q : GraphPath G := GraphPath.ofSequence (n := 2 * t + 1) f hfinj hadj
  have hQsrc : Q.source = projection P.source :=
    (GraphPath.ofSequence_source f hfinj hadj).trans hf0
  have hQtgt : Q.target = projection P.target :=
    (GraphPath.ofSequence_target f hfinj hadj).trans hflast
  have hQsubset : Q.vertexSet ⊆ P.vertexSet.image projection := by
    intro v hv
    obtain ⟨i, rfl⟩ := (GraphPath.mem_ofSequence_vertexSet f hfinj hadj v).mp hv
    exact Finset.mem_image.mpr ⟨P.walk.getVert (ix i),
      List.mem_toFinset.mpr (P.walk.getVert_mem_support (ix i)), rfl⟩
  refine ⟨Q, ⟨?_, ?_, ?_, ?_⟩, hQsrc, hQtgt, hQsubset⟩
  · rw [hQsrc]
    exact oddPathAugmenting_source_terminal hP
  · rw [hQtgt]
    exact oddPathAugmenting_target_terminal hP
  · rw [show Q.walk.length = 2 * t + 1 from GraphPath.ofSequence_length f hfinj hadj]
    exact ⟨t, rfl⟩
  · intro v hv hvA
    obtain ⟨i, rfl⟩ := (GraphPath.mem_ofSequence_vertexSet f hfinj hadj v).mp hv
    by_cases hs : P.walk.getVert (ix i) = P.source
    · exact Or.inl ((congrArg projection hs).trans hQsrc.symm)
    · by_cases ht : P.walk.getVert (ix i) = P.target
      · exact Or.inr ((congrArg projection ht).trans hQtgt.symm)
      · exact (oddPathAugmenting_internal_nonterminal hP
          (List.mem_toFinset.mpr (P.walk.getVert_mem_support (ix i))) hs ht hvA).elim

end Erdos73
