import Arxiv.Arxiv2411_18291.VariableFarPartnerIntersections
import Arxiv.Arxiv2411_18291.SignedEdgeForcing
import Arxiv.Arxiv2411_18291.VariableFurtherEliminationPairs

/-!
# The further partners are available and distinct

The positive cliques of the first elimination cannot contain a bad old
edge. Nonnegative boundary therefore forces the corresponding positive
far splitting clique to be present. Frame locality and the same edge
count ensure that distinct selected bad cliques have distinct partners.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W U V : Type*} [Fintype W] [Fintype U] [Fintype V]
variable [DecidableEq W] [DecidableEq U] [DecidableEq V] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {C : Block V q → ℕ} {θ θ' : ℝ}
variable {T : ExchangeSystem U q (r + 1)} {N₀ : Block U q} {e₀ : Block U (r + 1)}
variable {F : VariableSplittingFamily S D B C θ}
variable {E : EliminationFamily T N₀ F.graph F.pairPositive F.pairNegative θ'}

theorem VariableFurtherEliminationPairs.edge_negative (L : VariableFurtherEliminationPairs F E)
    (i : E.badNegative) : L.edge i ∈ cliqueEdges (r + 1) i.val :=
  (mem_inter.mp ((L.old_inter i).symm ▸ mem_singleton_self (L.edge i))).1

theorem VariableFurtherEliminationPairs.edge_old (L : VariableFurtherEliminationPairs F E)
    (i : E.badNegative) : L.edge i ∈ F.graph :=
  (mem_inter.mp ((L.old_inter i).symm ▸ mem_singleton_self (L.edge i))).2

theorem VariableFurtherEliminationPairs.edge_near (L : VariableFurtherEliminationPairs F E)
    (hpair : IsEliminationPair T N₀ e₀) (i : E.badNegative) :
    ∃ Q ∈ F.negativeNear, L.edge i ∈ cliqueEdges (r + 1) Q := by
  obtain ⟨j, _, hj⟩ := mem_biUnion.mp (mem_sdiff.mp i.property).1
  obtain ⟨R, hR, hRi⟩ := (mem_mapGraph _ _ _).mp hj
  have he : L.edge i ∈ cliqueEdges (r + 1) i.val ∩ F.graph :=
    mem_inter.mpr ⟨L.edge_negative i, L.edge_old i⟩
  rw [← hRi, E.negative_copy_inter_original hpair j hR] at he
  exact ⟨F.pairNegative j, j.val.1.property, (mem_inter.mp he).2⟩

theorem VariableFurtherEliminationPairs.equal_partner_equal_edge
    (L : VariableFurtherEliminationPairs F E)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (hlocal : IsPositiveFrameLocal S A) (hcross : IsCrossSimple (r + 1) S.positive S.negative)
    (hpair : IsEliminationPair T N₀ e₀) {i j : E.badNegative}
    (hij : L.positive i = L.positive j) : L.edge i = L.edge j := by
  obtain ⟨Q, hQ, heQ⟩ := L.edge_near hpair i
  obtain ⟨R, hR, heR⟩ := L.edge_near hpair j
  exact F.positiveFar_near_edges_unique hA hlocal hcross (L.positive_mem i) hQ hR
    (L.edge_positive i) heQ (hij.symm ▸ L.edge_positive j) heR

theorem VariableFurtherEliminationPairs.positive_elimination_avoids_edge
    (L : VariableFurtherEliminationPairs F E)
    (hpair : IsEliminationPair T N₀ e₀) (i : E.badNegative)
    {Q : Block V q} (hQ : Q ∈ E.positiveCliques) : L.edge i ∉ cliqueEdges (r + 1) Q := by
  intro heQ
  obtain ⟨j, _, hj⟩ := mem_biUnion.mp hQ
  obtain ⟨R, hR, hRQ⟩ := (mem_mapGraph _ _ _).mp hj
  have hdis : Disjoint (cliqueEdges (r + 1) Q)
      (cliqueEdges (r + 1) (F.pairNegative j)) := by
    have hd : Disjoint (mapGraph (E.embedding j) (cliqueEdges (r + 1) R))
        (mapGraph (E.embedding j) (cliqueEdges (r + 1) N₀)) :=
      (disjoint_map _).mpr (T.eliminationPositive_disjoint_negative hpair.negative_mem hR)
    simpa only [map_cliqueEdges, hRQ, E.negative_root] using hd
  have heOld : L.edge i ∈ cliqueEdges (r + 1) Q ∩ F.graph :=
    mem_inter.mpr ⟨heQ, L.edge_old i⟩
  rw [← hRQ, E.clique_inter_original hpair j R
    (T.negative_decomposition.clique_subset (mem_erase.mp hR).2)] at heOld
  have heP : L.edge i ∈ cliqueEdges (r + 1) (F.pairPositive j) :=
    (mem_union.mp (mem_inter.mp heOld).2).resolve_right
      (fun h => disjoint_left.mp hdis heQ h)
  have hEq := L.positive_unique i (F.pairPositive j)
    (mem_filter.mp j.val.2.property).1 heP
  exact (mem_sdiff.mp (L.positive_mem i)).2 (hEq ▸ j.val.2.property)

theorem VariableFurtherEliminationPairs.positive_unique_first
    (L : VariableFurtherEliminationPairs F E)
    (hpair : IsEliminationPair T N₀ e₀) (P : Finset (Block V q))
    (hP : P ⊆ F.positiveCliques ∪ E.positiveCliques) (i : E.badNegative)
    {Q : Block V q} (hQ : Q ∈ P) (heQ : L.edge i ∈ cliqueEdges (r + 1) Q) :
    Q = L.positive i := by
  rcases mem_union.mp (hP hQ) with hf | he
  · exact L.positive_unique i Q hf heQ
  · exact (L.positive_elimination_avoids_edge hpair i he heQ).elim

theorem VariableFurtherEliminationPairs.partner_forced (L : VariableFurtherEliminationPairs F E)
    (hpair : IsEliminationPair T N₀ e₀) (P N : Finset (Block V q))
    (hP : P ⊆ F.positiveCliques ∪ E.positiveCliques)
    (hnonneg : ∀ e, 0 ≤ boundary (r + 1) (indicator P - indicator N) e)
    (i : E.badNegative) (hi : i.val ∈ N) :
    L.positive i ∈ P ∧ ∀ Q ∈ N, L.edge i ∈ cliqueEdges (r + 1) Q → Q = i.val :=
  signed_edge_partner_forced P N (L.edge i) (L.positive i) i.val hi (L.edge_negative i)
    (hnonneg _) (fun _ hQ heQ => L.positive_unique_first hpair P hP i hQ heQ)

def VariableFurtherEliminationPairs.selected (_L : VariableFurtherEliminationPairs F E)
    (N : Finset (Block V q)) : Finset E.badNegative := univ.filter fun i => i.val ∈ N

theorem VariableFurtherEliminationPairs.selected_negative (L : VariableFurtherEliminationPairs F E)
    (N : Finset (Block V q)) : (L.selected N).image Subtype.val = N ∩ E.badNegative := by
  ext Q
  constructor
  · intro hQ
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hQ
    exact mem_inter.mpr ⟨(mem_filter.mp hi).2, i.property⟩
  · intro hQ
    exact mem_image.mpr ⟨⟨Q, (mem_inter.mp hQ).2⟩,
      mem_filter.mpr ⟨mem_univ _, (mem_inter.mp hQ).1⟩, rfl⟩

theorem VariableFurtherEliminationPairs.selected_positive_subset
    (L : VariableFurtherEliminationPairs F E)
    (hpair : IsEliminationPair T N₀ e₀) (P N : Finset (Block V q))
    (hP : P ⊆ F.positiveCliques ∪ E.positiveCliques)
    (hnonneg : ∀ e, 0 ≤ boundary (r + 1) (indicator P - indicator N) e) :
    (L.selected N).image L.positive ⊆ P := by
  intro Q hQ
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hQ
  exact (L.partner_forced hpair P N hP hnonneg i (mem_filter.mp hi).2).1

theorem VariableFurtherEliminationPairs.selected_positive_injective
    (L : VariableFurtherEliminationPairs F E)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (hlocal : IsPositiveFrameLocal S A) (hcross : IsCrossSimple (r + 1) S.positive S.negative)
    (hpair : IsEliminationPair T N₀ e₀) (P N : Finset (Block V q))
    (hP : P ⊆ F.positiveCliques ∪ E.positiveCliques)
    (hnonneg : ∀ e, 0 ≤ boundary (r + 1) (indicator P - indicator N) e) :
    Set.InjOn L.positive (L.selected N) := by
  intro i hi j hj hij
  have heq := L.equal_partner_equal_edge hA hlocal hcross hpair hij
  have hu := (L.partner_forced hpair P N hP hnonneg i (mem_filter.mp hi).2).2
  exact Subtype.ext (hu j.val (mem_filter.mp hj).2 (heq.symm ▸ L.edge_negative j)).symm

end Arxiv2411_18291
