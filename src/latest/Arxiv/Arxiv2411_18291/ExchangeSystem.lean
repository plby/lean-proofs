import Arxiv.Arxiv2411_18291.ExchangeSeed
import Arxiv.Arxiv2411_18291.PreparedGluing
import Arxiv.Arxiv2411_18291.PreparedInsert

/-! # The evolving pair of decompositions in the exchange construction -/

open Finset

noncomputable section

namespace Arxiv2411_18291

structure ExchangeSystem (V : Type*) [Fintype V] [DecidableEq V] (q r : ℕ) where
  graph : Hypergraph V r
  positive : Finset (Block V q)
  negative : Finset (Block V q)
  positive_decomposition : IsDecomposition graph positive
  negative_decomposition : IsDecomposition graph negative
  disjoint : Disjoint positive negative
  base : Block V q
  base_mem : base ∈ positive

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
variable {q r : ℕ}

def ExchangeSeed.toSystem (E : ExchangeSeed V q r) : ExchangeSystem V q r where
  graph := E.graph
  positive := E.positive
  negative := E.negative
  positive_decomposition := E.positive_decomposition
  negative_decomposition := E.negative_decomposition
  disjoint := E.disjoint
  base := E.positiveClique
  base_mem := E.positive_mem

namespace ExchangeSystem

/-- Attach a seed along a negative clique, retaining the original positive
base clique and both true decompositions. -/
def glue (S : ExchangeSystem V q r) (E : ExchangeSeed W q r)
    (hr : 0 < r) (hqr : r ≤ q) (C : Block V q) (hC : C ∈ S.negative)
    (σ : E.positiveClique.val ≃ C.val) :
    ExchangeSystem (GluedVertex V W E.positiveClique.val) q r where
  graph := mapGraph (glueLeft E.positiveClique.val) S.graph ∪
    mapGraph (glueRight C E.positiveClique σ) E.graph
  positive := mapGraph (glueLeft E.positiveClique.val) S.positive ∪
    (mapGraph (glueRight C E.positiveClique σ) E.positive).erase
      (mapBlock (glueLeft E.positiveClique.val) C)
  negative := mapGraph (glueRight C E.positiveClique σ) E.negative ∪
    (mapGraph (glueLeft E.positiveClique.val) S.negative).erase
      (mapBlock (glueLeft E.positiveClique.val) C)
  positive_decomposition := (vertex_glue_two_decompositions hqr C E.positiveClique σ
    S.positive_decomposition S.negative_decomposition
    E.positive_decomposition E.negative_decomposition hC E.positive_mem).1
  negative_decomposition := (vertex_glue_two_decompositions hqr C E.positiveClique σ
    S.positive_decomposition S.negative_decomposition
    E.positive_decomposition E.negative_decomposition hC E.positive_mem).2
  disjoint := by
    apply glue_families_disjoint hr hqr
      (S.positive_decomposition.map _) (S.negative_decomposition.map _)
      (E.positive_decomposition.map _) (E.negative_decomposition.map _)
    · exact (disjoint_map _).mpr S.disjoint
    · exact (disjoint_map _).mpr E.disjoint
    · exact (mem_mapGraph _ S.negative _).mpr ⟨C, hC, rfl⟩
    · exact glued_graph_intersection C E.positiveClique σ S.graph E.graph
        (S.negative_decomposition.clique_subset hC)
        (E.positive_decomposition.clique_subset E.positive_mem)
  base := mapBlock (glueLeft E.positiveClique.val) S.base
  base_mem := mem_union.mpr (Or.inl ((mem_mapGraph _ S.positive _).mpr
    ⟨S.base, S.base_mem, rfl⟩))

theorem glue_card_le (S : ExchangeSystem V q r) (E : ExchangeSeed W q r)
    (hr : 0 < r) (hqr : r ≤ q) (C : Block V q) (hC : C ∈ S.negative)
    (σ : E.positiveClique.val ≃ C.val) :
    (S.glue E hr hqr C hC σ).graph.card ≤ S.graph.card + E.graph.card := by
  exact (card_union_le _ _).trans_eq (by rw [card_mapGraph, card_mapGraph])

theorem glue_negative_mem (S : ExchangeSystem V q r) (E : ExchangeSeed W q r)
    (hr : 0 < r) (hqr : r ≤ q) (C : Block V q) (hC : C ∈ S.negative)
    (σ : E.positiveClique.val ≃ C.val) :
    mapBlock (glueRight C E.positiveClique σ) E.negativeClique ∈
      (S.glue E hr hqr C hC σ).negative :=
  mem_union.mpr (Or.inl ((mem_mapGraph _ E.negative _).mpr
    ⟨E.negativeClique, E.negative_mem, rfl⟩))

end ExchangeSystem

/-- Bundle the finite vertex type so that induction may add fresh vertices. -/
structure FiniteExchangeSystem (q r : ℕ) where
  Vertex : Type
  [fintypeVertex : Fintype Vertex]
  [decidableVertex : DecidableEq Vertex]
  system : ExchangeSystem Vertex q r

attribute [instance] FiniteExchangeSystem.fintypeVertex FiniteExchangeSystem.decidableVertex

def ExchangeSystem.toFinite {V : Type} [Fintype V] [DecidableEq V]
    (S : ExchangeSystem V q r) : FiniteExchangeSystem q r where
  Vertex := V
  system := S

end Arxiv2411_18291
