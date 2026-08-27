import Arxiv.Arxiv2411_18291.GreedyEmbeddingExistence

/-!
# Degree bounds for the union of greedy embeddings

The simple graph underlying an edge family has degree at most the family's
degree with repetitions. Summing over all new pattern edges therefore gives
an explicit degree bound on the whole graph built by the greedy process.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype I] [Fintype V] [DecidableEq V] {r t : ℕ}

theorem IsGraphBounded.subgraph {G G' : Hypergraph V (r + 1)} {θ : ℝ}
    (hG : IsGraphBounded G θ) (hsub : G' ⊆ G) : IsGraphBounded G' θ := by
  intro S
  have hc : ((G'.filter fun e => S.val ⊆ e.val).card : ℝ) ≤
      (G.filter fun e => S.val ⊆ e.val).card := by
    exact_mod_cast card_le_card (filter_subset_filter _ hsub)
  exact hc.trans_lt (hG S)

omit [Fintype V] in
theorem edgeFamilyGraph_degree_le (E : I → Block V (r + 1)) (S : Finset V) :
    ((univ.image E).filter fun e => S ⊆ e.val).card ≤ familyDegree E S := by
  rw [filter_image]
  exact card_image_le

theorem IsEdgeFamilyBounded.graphBounded {E : I → Block V (r + 1)} {θ : ℝ}
    (hE : IsEdgeFamilyBounded E θ) : IsGraphBounded (univ.image E) θ := by
  intro S
  have hc : (((univ.image E).filter fun e => S.val ⊆ e.val).card : ℝ) ≤
      familyDegree E S.val := by exact_mod_cast edgeFamilyGraph_degree_le E S.val
  exact hc.trans_lt (hE S)

variable [DecidableEq W] {F : Finset W}

def greedyFamilyGraph (F : Finset W) (H : Hypergraph W (r + 1))
    (Ψ : Fin t → W ↪ V) : Hypergraph V (r + 1) :=
  univ.biUnion fun i => mapGraph (Ψ i) (newEdges F H)

omit [Fintype V] in
theorem greedyFamilyGraph_eq_biUnion (F : Finset W) (H : Hypergraph W (r + 1))
    (Ψ : Fin t → W ↪ V) :
    greedyFamilyGraph F H Ψ = (newEdges F H).biUnion
      (fun e => univ.image (fun i => mapBlock (Ψ i) e)) := by
  ext g
  constructor
  · intro hg
    obtain ⟨i, _, hgi⟩ := mem_biUnion.mp hg
    obtain ⟨e, he, heg⟩ := (mem_mapGraph (Ψ i) (newEdges F H) g).mp hgi
    exact mem_biUnion.mpr ⟨e, he, mem_image.mpr ⟨i, mem_univ _, heg⟩⟩
  · intro hg
    obtain ⟨e, he, hge⟩ := mem_biUnion.mp hg
    obtain ⟨i, _, heg⟩ := mem_image.mp hge
    exact mem_biUnion.mpr ⟨i, mem_univ _,
      (mem_mapGraph (Ψ i) (newEdges F H) g).mpr ⟨e, he, heg⟩⟩

theorem IsGreedyFamily.graphBounded_newEdges {Φ : Fin t → F ↪ V}
    {H : Hypergraph W (r + 1)}
    {B : Hypergraph V (r + 1)} {Ψ : (i : Fin t) → EmbeddingExtension (Φ i)} {L θ : ℝ}
    (hΨ : IsGreedyFamily Φ H B Ψ L) (hB : IsGraphBounded B θ) :
    IsGraphBounded (B ∪ greedyFamilyGraph F H (fun i => (Ψ i).val))
      (θ + (newEdges F H).card * L) := by
  have hbound := hB.union_biUnion_degree_le (newEdges F H)
    (fun e => univ.image (fun i => mapBlock (Ψ i).val e)) (fun _ => L)
    (fun e he S => ((hΨ.bounded e he).graphBounded S).le)
  rw [greedyFamilyGraph_eq_biUnion]
  simpa only [sum_const, nsmul_eq_mul] using hbound

theorem IsGreedyFamily.graphBounded {Φ : Fin t → F ↪ V} {H : Hypergraph W (r + 1)}
    {B : Hypergraph V (r + 1)} {Ψ : (i : Fin t) → EmbeddingExtension (Φ i)} {L θ : ℝ}
    (hΨ : IsGreedyFamily Φ H B Ψ L) (hB : IsGraphBounded B θ) (hL : 0 ≤ L) :
    IsGraphBounded (B ∪ greedyFamilyGraph F H (fun i => (Ψ i).val)) (θ + H.card * L) := by
  apply (hΨ.graphBounded_newEdges hB).mono
  have hc : ((newEdges F H).card : ℝ) ≤ H.card := by
    exact_mod_cast (card_filter_le H (fun e => ¬e.val ⊆ F))
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hc hL)

theorem IsGreedyFamily.restrict {Φ : Fin t → F ↪ V} {H H' : Hypergraph W (r + 1)}
    {B : Hypergraph V (r + 1)} {Ψ : (i : Fin t) → EmbeddingExtension (Φ i)} {L : ℝ}
    (hΨ : IsGreedyFamily Φ H B Ψ L) (hH : H' ⊆ H) : IsGreedyFamily Φ H' B Ψ L := by
  have hnew : newEdges F H' ⊆ newEdges F H := filter_subset_filter _ hH
  exact {
    avoids := fun i => (hΨ.avoids i).mono_left (mapGraph_mono _ hnew)
    disjoint := fun i j hij => Disjoint.mono (mapGraph_mono _ hnew)
      (mapGraph_mono _ hnew) (hΨ.disjoint hij)
    bounded := fun e he => hΨ.bounded e (hnew he) }

end Arxiv2411_18291
