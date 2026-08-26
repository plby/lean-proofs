import ErdosProblems.Erdos73.OddTerminalPathsDefs

/-! An odd path with terminal ends contains a terminal-clean odd subpath. -/

namespace Erdos73

open SimpleGraph Finset
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

theorem exists_oddTerminalSegment (N : Finset V) (P : GraphPath G)
    (hs : P.source ∈ N) (ht : P.target ∈ N) (hodd : Odd P.walk.length) :
    ∃ Q : GraphPath G, IsOddTerminalPath N Q ∧ Q.vertexSet ⊆ P.vertexSet := by
  classical
  induction hn : P.walk.length using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hclean : ∀ v ∈ P.vertexSet, v ∈ N → v = P.source ∨ v = P.target
    · exact ⟨P, ⟨hs, ht, hodd, hclean⟩, Finset.Subset.refl _⟩
    · push Not at hclean
      obtain ⟨v, hvP, hvN, hvs, hvt⟩ := hclean
      let L := P.takeUntil hvP
      let R := P.dropUntil hvP
      have hv : v ∈ P.walk.support := List.mem_toFinset.mp hvP
      have hL : L.walk.length < n := by
        rw [← hn]
        exact Walk.length_takeUntil_lt_length hv hvt
      have hR : R.walk.length < n := by
        rw [← hn]
        exact Walk.length_dropUntil_lt_length hv hvs
      have hsum : L.walk.length + R.walk.length = P.walk.length := by
        have hh := congrArg Walk.length (P.walk.take_spec hv)
        simpa only [L, R, GraphPath.takeUntil, GraphPath.dropUntil, Walk.length_append] using hh
      by_cases hoL : Odd L.walk.length
      · obtain ⟨Q, hQ, hQL⟩ := ih L.walk.length hL L hs hvN hoL rfl
        exact ⟨Q, hQ, hQL.trans (P.takeUntil_vertexSet_subset hvP)⟩
      · have hoR : Odd R.walk.length := by
          rw [Nat.odd_iff] at hodd hoL ⊢
          omega
        obtain ⟨Q, hQ, hQR⟩ := ih R.walk.length hR R hvN ht hoR rfl
        exact ⟨Q, hQ, hQR.trans (P.dropUntil_vertexSet_subset hvP)⟩

end Erdos73
