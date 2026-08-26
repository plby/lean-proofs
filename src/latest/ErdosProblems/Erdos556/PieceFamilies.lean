import ErdosProblems.Erdos556.PieceGraph
import ErdosProblems.Erdos556.DenseCore
import ErdosProblems.Erdos556.Linkage

/-!
# Families of large two-connected pieces

Pieces found in an induced subgraph can be transported back to the original
vertex type without changing their sizes, disjointness, or edge counts.
-/

namespace Erdos556

open SimpleGraph Finset

def IsTwoConnectedPieceFamily {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (r : ℕ) (P : Finset (Finset V)) : Prop :=
  (P : Set (Finset V)).Pairwise Disjoint ∧
    ∀ A ∈ P, r < A.card ∧ TwoConnected (G.induce (A : Set V))

theorem IsTwoConnectedPieceFamily.nonempty {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ} {P : Finset (Finset V)}
    (hP : IsTwoConnectedPieceFamily G r P) {A : Finset V} (hA : A ∈ P) : A.Nonempty :=
  card_pos.mp ((Nat.zero_le r).trans_lt (hP.2 A hA).1)

def liftPieces {V : Type*} [DecidableEq V] (S : Finset V) (P : Finset (Finset S)) :
    Finset (Finset V) :=
  P.map (Finset.mapEmbedding (Function.Embedding.subtype (fun v => v ∈ S))).toEmbedding

theorem mem_liftPieces {V : Type*} [DecidableEq V] (S : Finset V) (P : Finset (Finset S))
    (A : Finset V) : A ∈ liftPieces S P ↔
      ∃ T ∈ P, T.map (Function.Embedding.subtype (fun v => v ∈ S)) = A := by
  exact Finset.mem_map

theorem subset_of_mem_liftPieces {V : Type*} [DecidableEq V]
    {S : Finset V} {P : Finset (Finset S)} {A : Finset V} (hA : A ∈ liftPieces S P) : A ⊆ S := by
  obtain ⟨T, _, rfl⟩ := (mem_liftPieces S P A).mp hA
  intro x hx
  obtain ⟨y, _, hyx⟩ := mem_map.mp hx
  exact hyx ▸ y.property

theorem IsTwoConnectedPieceFamily.lift {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ} {S : Finset V} {P : Finset (Finset S)}
    (hP : IsTwoConnectedPieceFamily (G.induce (S : Set V)) r P) :
    IsTwoConnectedPieceFamily G r (liftPieces S P) := by
  constructor
  · intro A hA B hB hAB
    obtain ⟨T, hT, rfl⟩ := (mem_liftPieces S P A).mp hA
    obtain ⟨U, hU, rfl⟩ := (mem_liftPieces S P B).mp hB
    apply (Finset.disjoint_map _).mpr
    exact hP.1 hT hU (fun h => hAB (congrArg (Finset.map _) h))
  · intro A hA
    obtain ⟨T, hT, rfl⟩ := (mem_liftPieces S P A).mp hA
    refine ⟨by simpa only [card_map] using (hP.2 T hT).1, ?_⟩
    exact (hP.2 T hT).2.iso (induceFinsetMapIso G S T)

theorem sum_edges_liftPieces {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (P : Finset (Finset S)) :
    (∑ A ∈ liftPieces S P, (G.induce (A : Set V)).edgeFinset.card) =
      ∑ T ∈ P, ((G.induce (S : Set V)).induce (T : Set S)).edgeFinset.card := by
  rw [liftPieces, sum_map]
  apply sum_congr rfl
  intro T _
  exact (induceFinsetMapIso G S T).card_edgeFinset_eq.symm

theorem disjoint_liftPieces {V : Type*} [DecidableEq V]
    {S T : Finset V} (hST : Disjoint S T) (P : Finset (Finset S)) (Q : Finset (Finset T))
    (hP : ∀ A ∈ P, A.Nonempty) : Disjoint (liftPieces S P) (liftPieces T Q) := by
  rw [Finset.disjoint_left]
  intro A hAP hAQ
  have hAS := subset_of_mem_liftPieces hAP
  have hAT := subset_of_mem_liftPieces hAQ
  obtain ⟨U, hU, rfl⟩ := (mem_liftPieces S P A).mp hAP
  obtain ⟨x, hx⟩ := hP U hU
  have hxmap : x.val ∈ U.map (Function.Embedding.subtype (fun v => v ∈ S)) :=
    mem_map.mpr ⟨x, hx, rfl⟩
  exact Finset.disjoint_left.mp hST (hAS hxmap) (hAT hxmap)

theorem IsTwoConnectedPieceFamily.union {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ} {P Q : Finset (Finset V)}
    (hP : IsTwoConnectedPieceFamily G r P) (hQ : IsTwoConnectedPieceFamily G r Q)
    (hcross : ∀ A ∈ P, ∀ B ∈ Q, Disjoint A B) :
    IsTwoConnectedPieceFamily G r (P ∪ Q) := by
  constructor
  · intro A hA B hB hAB
    rcases mem_union.mp hA with hAP | hAQ <;> rcases mem_union.mp hB with hBP | hBQ
    · exact hP.1 hAP hBP hAB
    · exact hcross A hAP B hBQ
    · exact (hcross B hBP A hAQ).symm
    · exact hQ.1 hAQ hBQ hAB
  · intro A hA
    exact (mem_union.mp hA).elim (hP.2 A) (hQ.2 A)

#print axioms IsTwoConnectedPieceFamily.lift
#print axioms sum_edges_liftPieces

end Erdos556
