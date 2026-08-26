import ErdosProblems.Erdos556.PieceGraph
import ErdosProblems.Erdos556.SurvivingCore

/-!
# Hereditary edge bounds on disjoint pieces

Hereditary density bounds on induced pieces add without loss when their
vertex sets are disjoint. The resulting bound also covers isolated vertices.
-/

namespace Erdos556

open SimpleGraph Finset

theorem hereditary_density_of_induce {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (d : ℝ)
    (h : ∀ T : Finset A, (((G.induce (A : Set V)).induce (T : Set A)).edgeFinset.card : ℝ) ≤
      d * T.card) :
    ∀ S : Finset V, S ⊆ A → ((G.induce (S : Set V)).edgeFinset.card : ℝ) ≤ d * S.card := by
  classical
  intro S hS
  let T : Finset A := S.subtype (fun v => v ∈ A)
  have hmap : T.map (Function.Embedding.subtype (fun v => v ∈ A)) = S :=
    subtype_map_of_mem (fun v hv => hS hv)
  have hcard : T.card = S.card := by
    have hc := congrArg Finset.card hmap
    simpa only [card_map] using hc
  let e : (G.induce (A : Set V)).induce (T : Set A) ≃g G.induce (S : Set V) :=
    (induceFinsetMapIso G A T).trans (induceSetCongr G _ _ (congrArg (fun U : Finset V =>
      (U : Set V)) hmap))
  have hT := h T
  rw [e.card_edgeFinset_eq, hcard] at hT
  exact hT

theorem edge_count_induce_pieceGraph_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset (Finset V))
    [DecidableRel (pieceGraph G P).Adj] (S : Finset V) :
    ((pieceGraph G P).induce (S : Set V)).edgeFinset.card ≤
      ∑ A ∈ P, (G.induce (↑(A ∩ S) : Set V)).edgeFinset.card := by
  classical
  let E (A : Finset V) := G.edgeFinset.filter (fun e => e.toFinset ⊆ A ∩ S)
  let F := (pieceGraph G P).edgeFinset.filter (fun e => e.toFinset ⊆ S)
  have hcover : F ⊆ P.biUnion E := by
    intro e he
    obtain ⟨he, hS⟩ := mem_filter.mp he
    rcases e with ⟨⟨u, v⟩⟩
    rw [mem_edgeFinset, mem_edgeSet] at he
    obtain ⟨huv, A, hA, hu, hv⟩ := he
    apply mem_biUnion.mpr
    refine ⟨A, hA, mem_filter.mpr ⟨?_, ?_⟩⟩
    · simpa using huv
    · have huS : u ∈ S := hS (by simp)
      have hvS : v ∈ S := hS (by simp)
      simpa only [Sym2.toFinset_mk_eq, insert_subset_iff, singleton_subset_iff, mem_inter]
        using And.intro (And.intro hu huS) (And.intro hv hvS)
  calc
    ((pieceGraph G P).induce (S : Set V)).edgeFinset.card = F.card :=
      ((pieceGraph G P).card_filter_edgeFinset_toFinset_subset S).symm
    _ ≤ (P.biUnion E).card := card_le_card hcover
    _ ≤ ∑ A ∈ P, (E A).card := card_biUnion_le
    _ = ∑ A ∈ P, (G.induce (↑(A ∩ S) : Set V)).edgeFinset.card := by
      apply sum_congr rfl
      intro A _
      exact G.card_filter_edgeFinset_toFinset_subset (A ∩ S)

theorem sum_card_inter_le_of_disjoint {V : Type*} [DecidableEq V]
    (P : Finset (Finset V)) (hP : (P : Set (Finset V)).Pairwise Disjoint) (S : Finset V) :
    (∑ A ∈ P, (A ∩ S).card) ≤ S.card := by
  have hdisj : (P : Set (Finset V)).Pairwise fun A B => Disjoint (A ∩ S) (B ∩ S) := by
    intro A hA B hB hAB
    exact (hP hA hB hAB).mono (inter_subset_left) (inter_subset_left)
  rw [← card_biUnion hdisj]
  apply card_le_card
  intro v hv
  obtain ⟨A, _, hvA⟩ := mem_biUnion.mp hv
  exact (mem_inter.mp hvA).2

theorem hereditary_density_pieceGraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset (Finset V))
    [DecidableRel (pieceGraph G P).Adj]
    (hP : (P : Set (Finset V)).Pairwise Disjoint) (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ A ∈ P, ∀ S : Finset V, S ⊆ A →
      ((G.induce (S : Set V)).edgeFinset.card : ℝ) ≤ d * S.card) :
    ∀ S : Finset V, (((pieceGraph G P).induce (S : Set V)).edgeFinset.card : ℝ) ≤ d * S.card := by
  intro S
  have hcard : (∑ A ∈ P, ((A ∩ S).card : ℝ)) ≤ S.card := by
    exact_mod_cast sum_card_inter_le_of_disjoint P hP S
  calc
    (((pieceGraph G P).induce (S : Set V)).edgeFinset.card : ℝ) ≤
        ∑ A ∈ P, ((G.induce (↑(A ∩ S) : Set V)).edgeFinset.card : ℝ) := by
      exact_mod_cast edge_count_induce_pieceGraph_le G P S
    _ ≤ ∑ A ∈ P, d * (A ∩ S).card := by
      apply sum_le_sum
      intro A hA
      exact h A hA (A ∩ S) inter_subset_left
    _ = d * ∑ A ∈ P, ((A ∩ S).card : ℝ) := (mul_sum _ _ _).symm
    _ ≤ d * S.card := mul_le_mul_of_nonneg_left hcard hd

#print axioms hereditary_density_of_induce
#print axioms hereditary_density_pieceGraph

end Erdos556
