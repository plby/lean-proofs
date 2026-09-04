import ErdosProblems.Erdos746.Model

/-!
# Fixed-set external-neighbour counting

This file supplies the exact finite counting lemma used in the expansion
union bound.  If `S` and `U` are disjoint vertex sets, then the `|S||U|`
edges between them are all forbidden whenever the external neighbourhood of
`S` is contained in the complement of `U`.  Consequently, in the uniform
`m`-edge model the number of such samples is exactly a binomial coefficient
from the remaining edge set.
-/

open scoped Sym2

namespace Erdos746

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The external neighbourhood of a finite vertex set.  This is definitionally
the same construction used by the deterministic Pósa module, but the counting
module is deliberately independent of that larger proof. -/
def externalNeighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Finset V :=
  (S.biUnion fun u ↦ Finset.univ.filter (G.Adj u)) \ S

@[simp]
theorem mem_externalNeighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {S : Finset V} {v : V} :
    v ∈ externalNeighborFinset G S ↔ v ∉ S ∧ ∃ u ∈ S, G.Adj u v := by
  simp [externalNeighborFinset, SimpleGraph.adj_comm, and_comm]

/-! ## Generic fixed-layer counting -/

/-- The subtype model and the ordinary `powersetCard` finset have identical
filtered counts. -/
theorem card_fixedEdgeGraph_filter_eq {n m : ℕ} (P : Finset (Edge n) → Prop) :
    ((Finset.univ : Finset (FixedEdgeGraph n m)).filter (fun G ↦ P G.1)).card =
      (((Edge n).attach.powersetCard m).filter P).card := by
  classical
  let valEmb : FixedEdgeGraph n m ↪ Finset (Edge n) :=
    ⟨Subtype.val, Subtype.val_injective⟩
  rw [← Finset.card_map valEmb]
  congr 1
  ext A
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Subtype.exists,
    Set.powersetCard.mem_iff, exists_and_left, Finset.mem_powersetCard]
  constructor
  · rintro ⟨B, hPB, hBcard, rfl⟩
    exact ⟨⟨fun e _ ↦ Finset.mem_attach _ e, hBcard⟩, hPB⟩
  · rintro ⟨⟨hAattach, hAcard⟩, hPA⟩
    exact ⟨A, hPA, hAcard, rfl⟩

/-- Exact count of the `m`-subsets which avoid a prescribed edge set. -/
theorem card_fixedEdgeGraph_avoiding {n m : ℕ} (F : Finset (Edge n)) :
    ((Finset.univ : Finset (FixedEdgeGraph n m)).filter
        (fun G ↦ Disjoint G.1 F)).card =
      (edgeCount n - F.card).choose m := by
  classical
  have hfilter :
      ((Edge n).attach.powersetCard m).filter
          (fun A ↦ Disjoint A F) =
        ((Edge n).attach \ F).powersetCard m := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_powersetCard,
      Finset.subset_sdiff]
    tauto
  calc
    ((Finset.univ : Finset (FixedEdgeGraph n m)).filter
        (fun G ↦ Disjoint G.1 F)).card =
        (((Edge n).attach.powersetCard m).filter
          (fun A ↦ Disjoint A F)).card :=
      by
        convert
          (card_fixedEdgeGraph_filter_eq (n := n) (m := m)
            (fun A ↦ Disjoint A F)) using 1 <;>
          apply congrArg Finset.card <;> ext x <;> simp
    _ = (((Edge n).attach \ F).powersetCard m).card := by
      rw [hfilter]
    _ = (edgeCount n - F.card).choose m := by
      have hcardAttach : (Edge n).attach.card = edgeCount n := by
        rw [Finset.card_attach, ← Fintype.card_coe, card_edge]
      rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset]
      · rw [hcardAttach]
      · exact fun e _ ↦ Finset.mem_attach (Edge n) e

/-! ## The complete cut between two disjoint vertex sets -/

/-- The edge joining an ordered pair from two disjoint vertex sets.  The
disjointness makes the pair non-diagonal, so it is an element of `Edge n`. -/
def edgeBetween {n : ℕ} {S U : Finset (Fin n)} (hSU : Disjoint S U)
    (q : ↑(S ×ˢ U)) : Edge n := by
  have hq := Finset.mem_product.mp q.2
  have hne : q.1.1 ≠ q.1.2 := by
    intro heq
    exact (Finset.disjoint_left.mp hSU hq.1) (heq ▸ hq.2)
  refine ⟨s(q.1.1, q.1.2), ?_⟩
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
    SimpleGraph.top_adj]
  exact hne

theorem edgeBetween_injective {n : ℕ} {S U : Finset (Fin n)}
    (hSU : Disjoint S U) : Function.Injective (edgeBetween hSU) := by
  intro q r hqr
  have hval : s(q.1.1, q.1.2) = s(r.1.1, r.1.2) :=
    congrArg Subtype.val hqr
  rw [Sym2.eq_iff] at hval
  rcases hval with hval | hswap
  · apply Subtype.ext
    exact Prod.ext hval.1 hval.2
  · have hq := Finset.mem_product.mp q.2
    have hr := Finset.mem_product.mp r.2
    exact False.elim ((Finset.disjoint_left.mp hSU hq.1) (hswap.1 ▸ hr.2))

/-- The finite set of all edges between `S` and `U`. -/
def crossingEdges {n : ℕ} (S U : Finset (Fin n)) (hSU : Disjoint S U) :
    Finset (Edge n) :=
  (Finset.univ : Finset ↑(S ×ˢ U)).image (edgeBetween hSU)

/-- A complete cut has the expected product cardinality. -/
@[simp]
theorem card_crossingEdges {n : ℕ} (S U : Finset (Fin n))
    (hSU : Disjoint S U) :
    (crossingEdges S U hSU).card = S.card * U.card := by
  rw [crossingEdges, Finset.card_image_of_injective _
    (edgeBetween_injective hSU), Finset.card_univ, Fintype.card_coe,
    Finset.card_product]

/-- Membership in the cut edge set is exactly representation by a pair with
one endpoint in each side. -/
theorem mem_crossingEdges_iff {n : ℕ} {S U : Finset (Fin n)}
    (hSU : Disjoint S U) (e : Edge n) :
    e ∈ crossingEdges S U hSU ↔
      ∃ a ∈ S, ∃ b ∈ U, (e : Sym2 (Fin n)) = s(a, b) := by
  constructor
  · intro he
    rw [crossingEdges, Finset.mem_image] at he
    obtain ⟨q, -, rfl⟩ := he
    have hq := Finset.mem_product.mp q.2
    exact ⟨q.1.1, hq.1, q.1.2, hq.2, rfl⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [crossingEdges, Finset.mem_image]
    let q : ↑(S ×ˢ U) := ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩⟩
    refine ⟨q, Finset.mem_univ _, ?_⟩
    apply Subtype.ext
    exact hab.symm

/-- The edge-subset presentation and graph adjacency agree on a cut edge. -/
theorem edgeBetween_mem_iff_adj {n m : ℕ} {S U : Finset (Fin n)}
    (hSU : Disjoint S U) (G : FixedEdgeGraph n m) (q : ↑(S ×ˢ U)) :
    edgeBetween hSU q ∈ G.1 ↔
      (FixedEdgeGraph.graph G).Adj q.1.1 q.1.2 := by
  rw [← SimpleGraph.mem_edgeSet, FixedEdgeGraph.edgeSet_graph]
  change edgeBetween hSU q ∈ G.1 ↔
    s(q.1.1, q.1.2) ∈ G.1.map (edgeEmbedding n)
  rw [Finset.mem_map]
  constructor
  · intro he
    exact ⟨edgeBetween hSU q, he, rfl⟩
  · rintro ⟨e, he, heq⟩
    have he' : e = edgeBetween hSU q := by
      apply Subtype.ext
      exact heq
    simpa [he'] using he

/-- Avoiding all cut edges is equivalent to having no external neighbour of
`S` in `U`. -/
theorem disjoint_crossingEdges_iff {n m : ℕ} {S U : Finset (Fin n)}
    (hSU : Disjoint S U) (G : FixedEdgeGraph n m) :
    Disjoint G.1 (crossingEdges S U hSU) ↔
      Disjoint U (externalNeighborFinset (FixedEdgeGraph.graph G) S) := by
  constructor
  · intro hcut
    rw [Finset.disjoint_left]
    intro b hbU hbN
    rw [mem_externalNeighborFinset] at hbN
    obtain ⟨hbS, a, haS, hab⟩ := hbN
    let q : ↑(S ×ˢ U) :=
      ⟨(a, b), Finset.mem_product.mpr ⟨haS, hbU⟩⟩
    have hmemG : edgeBetween hSU q ∈ G.1 :=
      (edgeBetween_mem_iff_adj hSU G q).2 hab
    exact (Finset.disjoint_left.mp hcut hmemG)
      (by simp [crossingEdges, q])
  · intro hneigh
    rw [Finset.disjoint_left]
    intro e heG hecut
    rw [mem_crossingEdges_iff hSU] at hecut
    obtain ⟨a, haS, b, hbU, heab⟩ := hecut
    let q : ↑(S ×ˢ U) :=
      ⟨(a, b), Finset.mem_product.mpr ⟨haS, hbU⟩⟩
    have heq : e = edgeBetween hSU q := by
      apply Subtype.ext
      exact heab
    have hab : (FixedEdgeGraph.graph G).Adj a b :=
      (edgeBetween_mem_iff_adj hSU G q).1 (heq ▸ heG)
    have hbS : b ∉ S := Finset.disjoint_left.mp hSU.symm hbU
    have hbN : b ∈ externalNeighborFinset (FixedEdgeGraph.graph G) S :=
      mem_externalNeighborFinset.mpr ⟨hbS, a, haS, hab⟩
    exact (Finset.disjoint_left.mp hneigh hbU) hbN

/-- Exact count when a prescribed outside set contains no neighbour of `S`. -/
theorem card_fixedEdgeGraph_disjoint_externalNeighbor {n m : ℕ}
    (S U : Finset (Fin n)) (hSU : Disjoint S U) :
    ((Finset.univ : Finset (FixedEdgeGraph n m)).filter
      (fun G ↦ Disjoint U
        (externalNeighborFinset (FixedEdgeGraph.graph G) S))).card =
      (edgeCount n - S.card * U.card).choose m := by
  have hevents :
      (Finset.univ : Finset (FixedEdgeGraph n m)).filter
          (fun G ↦ Disjoint U
            (externalNeighborFinset (FixedEdgeGraph.graph G) S)) =
        Finset.univ.filter
          (fun G ↦ Disjoint G.1 (crossingEdges S U hSU)) := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (disjoint_crossingEdges_iff hSU G).symm
  rw [hevents, card_fixedEdgeGraph_avoiding, card_crossingEdges]

/-- Vertices outside both `S` and a proposed neighbourhood `T`. -/
def outsideVertices {n : ℕ} (S T : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ \ (S ∪ T)

theorem disjoint_left_outsideVertices {n : ℕ} (S T : Finset (Fin n)) :
    Disjoint S (outsideVertices S T) := by
  rw [Finset.disjoint_left]
  intro v hvS hvout
  exact (Finset.mem_sdiff.mp hvout).2 (Finset.mem_union_left T hvS)

theorem card_outsideVertices {n : ℕ} {S T : Finset (Fin n)}
    (hST : Disjoint S T) :
    (outsideVertices S T).card = n - (S.card + T.card) := by
  rw [outsideVertices, Finset.card_sdiff_of_subset]
  · rw [Finset.card_univ, Fintype.card_fin,
      Finset.card_union_of_disjoint hST]
  · exact Finset.subset_univ _

/-- A proposed set `T` contains the whole external neighbourhood exactly when
the complementary outside set contains none of it. -/
theorem externalNeighbor_subset_iff_disjoint_outside {n m : ℕ}
    (S T : Finset (Fin n)) (G : FixedEdgeGraph n m) :
    externalNeighborFinset (FixedEdgeGraph.graph G) S ⊆ T ↔
      Disjoint (outsideVertices S T)
        (externalNeighborFinset (FixedEdgeGraph.graph G) S) := by
  constructor
  · intro hsub
    rw [Finset.disjoint_left]
    intro v hvout hvN
    exact (Finset.mem_sdiff.mp hvout).2
      (Finset.mem_union_right S (hsub hvN))
  · intro hdisj v hvN
    by_contra hvT
    have hvS : v ∉ S := (mem_externalNeighborFinset.mp hvN).1
    have hvout : v ∈ outsideVertices S T := by
      simp [outsideVertices, hvS, hvT]
    exact (Finset.disjoint_left.mp hdisj hvout) hvN

/-- **Sharp fixed-set containment count.**  If `S` and `T` are disjoint,
the number of `m`-edge graphs whose external neighbourhood of `S` lies in
`T` is exactly the number of ways to choose all `m` edges after deleting the
`|S|(n-|S|-|T|)` forbidden cut edges. -/
theorem card_fixedEdgeGraph_externalNeighbor_subset {n m : ℕ}
    (S T : Finset (Fin n)) (hST : Disjoint S T) :
    ((Finset.univ : Finset (FixedEdgeGraph n m)).filter
      (fun G ↦
        externalNeighborFinset (FixedEdgeGraph.graph G) S ⊆ T)).card =
      (edgeCount n - S.card * (n - (S.card + T.card))).choose m := by
  have hevents :
      (Finset.univ : Finset (FixedEdgeGraph n m)).filter
          (fun G ↦ externalNeighborFinset
            (FixedEdgeGraph.graph G) S ⊆ T) =
        Finset.univ.filter (fun G ↦
          Disjoint (outsideVertices S T)
            (externalNeighborFinset (FixedEdgeGraph.graph G) S)) := by
    ext G
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact externalNeighbor_subset_iff_disjoint_outside S T G
  rw [hevents,
    card_fixedEdgeGraph_disjoint_externalNeighbor S (outsideVertices S T)
      (disjoint_left_outsideVertices S T),
    card_outsideVertices hST]

/-! ## Union bound for a fixed bad set -/

theorem disjoint_externalNeighborFinset {n m : ℕ}
    (S : Finset (Fin n)) (G : FixedEdgeGraph n m) :
    Disjoint S (externalNeighborFinset (FixedEdgeGraph.graph G) S) := by
  rw [Finset.disjoint_left]
  intro v hvS hvN
  exact (mem_externalNeighborFinset.mp hvN).1 hvS

/-- All possible external-neighbour witnesses of size strictly below `2|S|`. -/
def smallNeighborWitnesses {n : ℕ} (S : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  Finset.univ.filter fun T ↦ Disjoint S T ∧ T.card < 2 * S.card

/-- There are exactly `choose (n-|S|) r` disjoint proposed neighbour sets
of cardinality `r` (provided `r` is in the small-neighbour range). -/
theorem card_smallNeighborWitnesses_filter_card {n r : ℕ}
    (S : Finset (Fin n)) (hr : r < 2 * S.card) :
    ((smallNeighborWitnesses S).filter (fun T ↦ T.card = r)).card =
      (n - S.card).choose r := by
  have heq :
      (smallNeighborWitnesses S).filter (fun T ↦ T.card = r) =
        Sᶜ.powersetCard r := by
    ext T
    simp only [smallNeighborWitnesses, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hST, -⟩, hcard⟩
      refine ⟨?_, hcard⟩
      exact Finset.subset_compl_iff_disjoint_right.mpr hST.symm
    · rintro ⟨hsub, hcard⟩
      refine ⟨⟨?_, hcard ▸ hr⟩, hcard⟩
      exact (Finset.subset_compl_iff_disjoint_right.mp hsub).symm
  rw [heq, Finset.card_powersetCard, Finset.card_compl]
  simp

/-- Samples for which the external neighbourhood of `S` is contained in `T`. -/
def neighborContainedSamples {n m : ℕ} (S T : Finset (Fin n)) :
    Finset (FixedEdgeGraph n m) :=
  Finset.univ.filter fun G ↦
    externalNeighborFinset (FixedEdgeGraph.graph G) S ⊆ T

/-- Samples for which `S` fails two-expansion. -/
def badNeighborSamples {n m : ℕ} (S : Finset (Fin n)) :
    Finset (FixedEdgeGraph n m) :=
  Finset.univ.filter fun G ↦
    (externalNeighborFinset (FixedEdgeGraph.graph G) S).card < 2 * S.card

theorem badNeighborSamples_subset_biUnion {n m : ℕ} (S : Finset (Fin n)) :
    badNeighborSamples (m := m) S ⊆
      (smallNeighborWitnesses S).biUnion
        (neighborContainedSamples (m := m) S) := by
  intro G hG
  rw [badNeighborSamples, Finset.mem_filter] at hG
  let T := externalNeighborFinset (FixedEdgeGraph.graph G) S
  rw [Finset.mem_biUnion]
  refine ⟨T, ?_, ?_⟩
  · rw [smallNeighborWitnesses, Finset.mem_filter]
    exact ⟨Finset.mem_univ T,
      disjoint_externalNeighborFinset S G, hG.2⟩
  · rw [neighborContainedSamples, Finset.mem_filter]
    exact ⟨Finset.mem_univ G, Finset.Subset.rfl⟩

/-- **Explicit fixed-set bad-neighbourhood bound.**

The summand is the exact count for a proposed neighbour set `T`; the only
loss is the finite union bound over possible `T`.  Grouping this sum by
`r = |T|` gives the standard
`choose (n-|S|) r * choose (N-|S|(n-|S|-r)) m` expression. -/
theorem card_badNeighborSamples_le {n m : ℕ} (S : Finset (Fin n)) :
    (badNeighborSamples (m := m) S).card ≤
      ∑ T ∈ smallNeighborWitnesses S,
        (edgeCount n - S.card * (n - (S.card + T.card))).choose m := by
  calc
    (badNeighborSamples (m := m) S).card ≤
        ((smallNeighborWitnesses S).biUnion
          (neighborContainedSamples (m := m) S)).card :=
      Finset.card_le_card (badNeighborSamples_subset_biUnion S)
    _ ≤ ∑ T ∈ smallNeighborWitnesses S,
          (neighborContainedSamples (m := m) S T).card :=
      Finset.card_biUnion_le
    _ = ∑ T ∈ smallNeighborWitnesses S,
          (edgeCount n - S.card * (n - (S.card + T.card))).choose m := by
      apply Finset.sum_congr rfl
      intro T hT
      have hST : Disjoint S T :=
        (Finset.mem_filter.mp hT).2.1
      exact card_fixedEdgeGraph_externalNeighbor_subset S T hST

end

end Erdos746
