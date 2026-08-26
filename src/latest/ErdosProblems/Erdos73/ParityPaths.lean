import ErdosProblems.Erdos73.WallTerminalColors
import ErdosProblems.Erdos73.OddTerminalPathsDefs

/-! Path parity relative to a fixed Boolean potential, and terminal-clean segments. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def ParityBreaking (c : V → Bool) (P : GraphPath G) : Prop :=
  Odd (P.walk.length + (c P.source).toNat + (c P.target).toNat)

structure IsParityBreakingPath (c : V → Bool) (T : Finset V) (P : GraphPath G) : Prop where
  source_mem : P.source ∈ T
  target_mem : P.target ∈ T
  breaking : ParityBreaking c P
  internal_disjoint : ∀ v ∈ P.vertexSet, v ∈ T → v = P.source ∨ v = P.target

theorem parityBreaking_of_odd_of_sameColor (c : V → Bool) (P : GraphPath G)
    (ho : Odd P.walk.length) (hc : c P.source = c P.target) : ParityBreaking c P := by
  rw [ParityBreaking, Nat.odd_iff, hc]
  rw [Nat.odd_iff] at ho
  omega

theorem exists_parityBreaking_segment (c : V → Bool) (T : Finset V) (P : GraphPath G)
    (hs : P.source ∈ T) (ht : P.target ∈ T) (hbreak : ParityBreaking c P) :
    ∃ Q : GraphPath G, IsParityBreakingPath c T Q ∧ Q.vertexSet ⊆ P.vertexSet := by
  induction hn : P.walk.length using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hclean : ∀ v ∈ P.vertexSet, v ∈ T → v = P.source ∨ v = P.target
    · exact ⟨P, ⟨hs, ht, hbreak, hclean⟩, subset_rfl⟩
    · push Not at hclean
      obtain ⟨v, hvP, hvT, hvs, hvt⟩ := hclean
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
      by_cases hLb : ParityBreaking c L
      · obtain ⟨Q, hQ, hQL⟩ := ih L.walk.length hL L hs hvT hLb rfl
        exact ⟨Q, hQ, hQL.trans (P.takeUntil_vertexSet_subset hvP)⟩
      · have hRb : ParityBreaking c R := by
          change ¬ Odd (L.walk.length + (c P.source).toNat + (c v).toNat) at hLb
          change Odd (R.walk.length + (c v).toNat + (c P.target).toNat)
          rw [ParityBreaking, Nat.odd_iff] at hbreak
          rw [Nat.odd_iff] at hLb ⊢
          omega
        obtain ⟨Q, hQ, hQR⟩ := ih R.walk.length hR R hvT ht hRb rfl
        exact ⟨Q, hQ, hQR.trans (P.dropUntil_vertexSet_subset hvP)⟩

theorem exists_parityBreakingPathPacking_of_oddTerminalPathPacking
    (c : V → Bool) (N T : Finset V) (hNT : N ⊆ T) (b : Bool)
    (hc : ∀ v ∈ N, c v = b) (k : ℕ) (hpack : HasOddTerminalPathPacking G N k) :
    ∃ P : Fin k → GraphPath G, (∀ i, IsParityBreakingPath c T (P i)) ∧
      Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet) := by
  obtain ⟨P, hP, hdis⟩ := hpack
  have hex (i : Fin k) : ∃ Q : GraphPath G,
      IsParityBreakingPath c T Q ∧ Q.vertexSet ⊆ (P i).vertexSet :=
    exists_parityBreaking_segment c T (P i) (hNT (hP i).source_mem) (hNT (hP i).target_mem)
      (parityBreaking_of_odd_of_sameColor c (P i) (hP i).odd_length
        ((hc _ (hP i).source_mem).trans (hc _ (hP i).target_mem).symm))
  choose Q hQ hsub using hex
  exact ⟨Q, hQ, fun i j hij => (hdis hij).mono (hsub i) (hsub j)⟩

end
end Erdos73
