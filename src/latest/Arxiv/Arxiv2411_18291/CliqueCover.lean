import Arxiv.Arxiv2411_18291.RootedCliquePattern
import Arxiv.Arxiv2411_18291.GreedyEmbeddingExistence
import Arxiv.Arxiv2411_18291.Decomposition

/-!
# Covering edges by cliques through a reserve

A cover assigns a clique to every input edge. All other edges of the
clique belong to the reserve, and the full cliques are edge-disjoint.
Disjointness of the new edges supplied by the greedy process suffices
when the input edges are distinct and outside the reserve.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V I : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

structure IsCliqueCover (R : Hypergraph V (r + 1)) (E : I → Block V (r + 1))
    (Q : I → Block V q) : Prop where
  punctured : ∀ i, IsPuncturedClique R (E i) (Q i).val
  disjoint : Pairwise fun i j => Disjoint (cliqueEdges (r + 1) (Q i))
    (cliqueEdges (r + 1) (Q j))

theorem punctured_cliques_disjoint (R : Hypergraph V (r + 1))
    {e f : Block V (r + 1)} {P Q : Block V q} (he : e ∉ R) (hf : f ∉ R) (hef : e ≠ f)
    (hP : IsPuncturedClique R e P.val) (hQ : IsPuncturedClique R f Q.val)
    (hnew : Disjoint ((cliqueEdges (r + 1) P).erase e)
      ((cliqueEdges (r + 1) Q).erase f)) :
    Disjoint (cliqueEdges (r + 1) P) (cliqueEdges (r + 1) Q) := by
  apply disjoint_left.mpr
  intro g hgP hgQ
  rcases hP.2 g ((mem_cliqueEdges g P).mp hgP) with hgR | hge
  · exact disjoint_left.mp hnew
      (mem_erase.mpr ⟨fun h => he (h ▸ hgR), hgP⟩)
      (mem_erase.mpr ⟨fun h => hf (h ▸ hgR), hgQ⟩)
  · subst g
    rcases hQ.2 e ((mem_cliqueEdges e Q).mp hgQ) with heR | hef'
    · exact he heR
    · exact hef hef'

theorem IsCliqueCover.injective {R : Hypergraph V (r + 1)}
    {E : I → Block V (r + 1)} {Q : I → Block V q} (hQ : IsCliqueCover R E Q) :
    Function.Injective Q := by
  intro i j hij
  by_contra hne
  have hi : E i ∈ cliqueEdges (r + 1) (Q i) :=
    (mem_cliqueEdges _ _).mpr (hQ.punctured i).1
  exact disjoint_left.mp (hQ.disjoint hne) hi (hij ▸ hi)

theorem IsCliqueCover.subclique_unique {R : Hypergraph V (r + 1)}
    {E : I → Block V (r + 1)} {Q : I → Block V q} (hQ : IsCliqueCover R E Q)
    {s : ℕ} (hrs : r + 1 ≤ s) (P : Block V s) {i j : I}
    (hi : P.val ⊆ (Q i).val) (hj : P.val ⊆ (Q j).val) : i = j := by
  by_contra hij
  obtain ⟨e, he⟩ := cliqueEdges_nonempty hrs P
  have heP := (mem_cliqueEdges e P).mp he
  exact disjoint_left.mp (hQ.disjoint hij)
    ((mem_cliqueEdges _ _).mpr (heP.trans hi)) ((mem_cliqueEdges _ _).mpr (heP.trans hj))

variable [Fintype W] [DecidableEq W] {t : ℕ}

theorem IsGreedyFamily.cliqueCover (F₀ : Block W (r + 1)) (hW : Fintype.card W = q)
    (E : Fin t → Block V (r + 1)) (R B : Hypergraph V (r + 1))
    (Ψ : (i : Fin t) → EmbeddingExtension (edgeRootMap F₀ (E i))) {L : ℝ}
    (hΨ : IsGreedyFamily (fun i => edgeRootMap F₀ (E i)) (complete W (r + 1)) B Ψ L)
    (hE : Function.Injective E) (hER : ∀ i, E i ∉ R)
    (hmem : ∀ i, Ψ i ∈ cliqueCandidateExtensions (edgeRootMap F₀ (E i)) hW R (E i)) :
    IsCliqueCover R E (fun i => embeddingClique hW (Ψ i).val) := by
  have hp : ∀ i, IsPuncturedClique R (E i) (embeddingClique hW (Ψ i).val).val :=
    fun i => (mem_cliqueCandidateExtensions _ _ _ _ _).mp (hmem i)
  refine ⟨hp, ?_⟩
  intro i j hij
  apply punctured_cliques_disjoint R (hER i) (hER j) (fun h => hij (hE h)) (hp i) (hp j)
  have hd := hΨ.disjoint hij
  change Disjoint (mapGraph (Ψ i).val (newEdges F₀.val (complete W (r + 1))))
    (mapGraph (Ψ j).val (newEdges F₀.val (complete W (r + 1)))) at hd
  rw [map_newEdges_complete_eq_erase F₀ hW _ _ (edgeRootMap_usedVertices F₀ (E i)) (Ψ i),
    map_newEdges_complete_eq_erase F₀ hW _ _ (edgeRootMap_usedVertices F₀ (E j)) (Ψ j)] at hd
  exact hd

variable [Fintype I]

omit [Fintype W] [DecidableEq W] in
def cliqueCoverGraph (Q : I → Block V q) : Hypergraph V (r + 1) :=
  univ.biUnion fun i => cliqueEdges (r + 1) (Q i)

omit [Fintype W] [DecidableEq W] in
theorem IsCliqueCover.root_mem {R : Hypergraph V (r + 1)}
    {E : I → Block V (r + 1)} {Q : I → Block V q} (hQ : IsCliqueCover R E Q) (i : I) :
    E i ∈ cliqueCoverGraph Q :=
  mem_biUnion.mpr ⟨i, mem_univ _, (mem_cliqueEdges _ _).mpr (hQ.punctured i).1⟩

omit [Fintype W] [DecidableEq W] in
theorem IsCliqueCover.graph_subset {R L : Hypergraph V (r + 1)}
    {E : I → Block V (r + 1)} {Q : I → Block V q} (hQ : IsCliqueCover R E Q)
    (hE : ∀ i, E i ∈ L) : cliqueCoverGraph Q ⊆ L ∪ R := by
  intro e he
  obtain ⟨i, _, hei⟩ := mem_biUnion.mp he
  rcases (hQ.punctured i).2 e ((mem_cliqueEdges _ _).mp hei) with heR | heE
  · exact mem_union_right _ heR
  · exact mem_union_left _ (heE ▸ hE i)

omit [Fintype W] [DecidableEq W] in
theorem IsCliqueCover.decomposition {R : Hypergraph V (r + 1)}
    {E : I → Block V (r + 1)} {Q : I → Block V q} (hQ : IsCliqueCover R E Q) :
    IsDecomposition (cliqueCoverGraph (r := r) Q) (univ.image Q) := by
  apply (isDecomposition_iff _ _).mpr
  intro e
  by_cases he : e ∈ cliqueCoverGraph Q
  · rw [if_pos he]
    apply card_eq_one_iff_existsUnique.mpr
    obtain ⟨i, _, hei⟩ := mem_biUnion.mp he
    refine ⟨Q i, mem_filter.mpr ⟨mem_image.mpr ⟨i, mem_univ _, rfl⟩,
      (mem_cliqueEdges _ _).mp hei⟩, ?_⟩
    intro P hP
    obtain ⟨hP, heP⟩ := mem_filter.mp hP
    obtain ⟨j, _, rfl⟩ := mem_image.mp hP
    by_cases hji : j = i
    · exact congrArg Q hji
    · exact (disjoint_left.mp (hQ.disjoint hji)
        ((mem_cliqueEdges _ _).mpr heP) hei).elim
  · rw [if_neg he, card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro P hP
    obtain ⟨hP, heP⟩ := mem_filter.mp hP
    obtain ⟨i, _, rfl⟩ := mem_image.mp hP
    exact he (mem_biUnion.mpr ⟨i, mem_univ _, (mem_cliqueEdges _ _).mpr heP⟩)

omit [Fintype W] [DecidableEq W] in
theorem IsCliqueCover.card_cliques {R : Hypergraph V (r + 1)}
    {E : I → Block V (r + 1)} {Q : I → Block V q} (hQ : IsCliqueCover R E Q) :
    (univ.image Q).card = Fintype.card I := by
  rw [card_image_of_injective _ hQ.injective, card_univ]

omit [Fintype W] [DecidableEq W] in
theorem cliqueCoverGraph_reindex {J : Type*} [Fintype J] (f : J ≃ I)
    (Q : I → Block V q) :
    cliqueCoverGraph (r := r) (fun j => Q (f j)) = cliqueCoverGraph Q := by
  ext e
  constructor
  · intro he
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨f j, mem_univ _, hj⟩
  · intro he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨f.symm i, mem_univ _, by simpa only [Equiv.apply_symm_apply] using hi⟩

omit [Fintype W] [DecidableEq W] [Fintype I] in
theorem IsCliqueCover.leave_decomposition {R L : Hypergraph V (r + 1)}
    {Q : L → Block V q} (hQ : IsCliqueCover R (fun e : L => e.val) Q) :
    ∃ G : Hypergraph V (r + 1), ∃ D : Finset (Block V q),
      L ⊆ G ∧ G ⊆ L ∪ R ∧ IsDecomposition G D ∧ D.card = L.card := by
  refine ⟨cliqueCoverGraph Q, univ.image Q, ?_, hQ.graph_subset (fun e => e.property),
    hQ.decomposition, ?_⟩
  · intro e he
    exact hQ.root_mem ⟨e, he⟩
  · simpa only [Fintype.card_coe] using hQ.card_cliques

end Arxiv2411_18291
