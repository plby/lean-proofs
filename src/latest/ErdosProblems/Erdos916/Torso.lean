import ErdosProblems.Erdos916.Blocks

/-!
# Separations and torsos for Erdős Problem 916

This file contains the finite bookkeeping used when a density induction is
split at a cut vertex.  If `K` is a component of `G - c`, the two vertex sets
are `K ∪ {c}` and the complement of `K`.  They intersect only in `c`; no edge
crosses their strict parts.  Consequently their vertex counts add to `n + 1`
and their edge counts add to `m`.

-/

open scoped Sym2

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

namespace CutDensity

open ComponentEndBlock

/-- The component side of `G - c`, as a finite set of ambient vertices. -/
noncomputable def sideFinset (c : V)
    (K : (deleteVertex G c).ConnectedComponent) : Finset V := by
  classical
  exact (side c K).toFinset

/-- The first cut piece: one component of `G - c`, with `c` put back. -/
noncomputable def piece (c : V)
    (K : (deleteVertex G c).ConnectedComponent) : Finset V :=
  insert c (sideFinset G c K)

/-- The complementary cut piece.  It contains `c`, since `c` is not on the
component side. -/
noncomputable def remainder (c : V)
    (K : (deleteVertex G c).ConnectedComponent) : Finset V :=
  Finset.univ \ sideFinset G c K

@[simp] theorem coe_sideFinset (c : V)
    (K : (deleteVertex G c).ConnectedComponent) :
    (sideFinset G c K : Set V) = side c K := by
  classical
  simp [sideFinset]

@[simp] theorem mem_piece_iff {c v : V}
    {K : (deleteVertex G c).ConnectedComponent} :
    v ∈ piece G c K ↔ v = c ∨ v ∈ side c K := by
  classical
  simp [piece, sideFinset]

@[simp] theorem mem_remainder_iff {c v : V}
    {K : (deleteVertex G c).ConnectedComponent} :
    v ∈ remainder G c K ↔ v ∉ side c K := by
  classical
  simp [remainder, sideFinset]

@[simp] theorem coe_piece (c : V)
    (K : (deleteVertex G c).ConnectedComponent) :
    (piece G c K : Set V) = verts c K := by
  ext v
  simp [verts]

@[simp] theorem coe_remainder (c : V)
    (K : (deleteVertex G c).ConnectedComponent) :
    (remainder G c K : Set V) = (side c K)ᶜ := by
  ext v
  simp

theorem cut_mem_piece (c : V) (K : (deleteVertex G c).ConnectedComponent) :
    c ∈ piece G c K := by simp

theorem cut_mem_remainder (c : V) (K : (deleteVertex G c).ConnectedComponent) :
    c ∈ remainder G c K := by
  simp [ComponentEndBlock.cut_not_mem_side (G := G)]

theorem piece_inter_remainder (c : V)
    (K : (deleteVertex G c).ConnectedComponent) :
    piece G c K ∩ remainder G c K = {c} := by
  ext v
  by_cases hvc : v = c
  · subst v
    simp [ComponentEndBlock.cut_not_mem_side (G := G)]
  · simp [hvc]

theorem piece_union_remainder (c : V)
    (K : (deleteVertex G c).ConnectedComponent) :
    piece G c K ∪ remainder G c K = Finset.univ := by
  ext v
  by_cases hv : v ∈ side c K <;> simp [hv]

/-- The two cut pieces count the cut vertex twice and every other vertex once. -/
theorem card_piece_add_card_remainder (c : V)
    (K : (deleteVertex G c).ConnectedComponent) :
    (piece G c K).card + (remainder G c K).card = Fintype.card V + 1 := by
  have hunion := Finset.card_union_add_card_inter (piece G c K) (remainder G c K)
  rw [piece_union_remainder, piece_inter_remainder] at hunion
  simp only [Finset.card_univ, Finset.card_singleton] at hunion
  omega

/-- Every ambient edge lies in at least one of the two cut pieces. -/
theorem edge_mem_piece_or_remainder {c u v : V}
    (K : (deleteVertex G c).ConnectedComponent) (huv : G.Adj u v) :
    ({u, v} : Finset V) ⊆ piece G c K ∨
      ({u, v} : Finset V) ⊆ remainder G c K := by
  by_cases hu : u ∈ side c K
  · left
    have hv : v ∈ verts c K :=
      ComponentEndBlock.neighborSet_subset_verts (G := G) K hu huv
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    constructor
    · exact (mem_piece_iff (G := G)).mpr (Or.inr hu)
    · change v ∈ (piece G c K : Set V)
      rw [coe_piece]
      exact hv
  · by_cases hv : v ∈ side c K
    · left
      have hu' : u ∈ verts c K :=
        ComponentEndBlock.neighborSet_subset_verts (G := G) K hv huv.symm
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      constructor
      · change u ∈ (piece G c K : Set V)
        rw [coe_piece]
        exact hu'
      · exact (mem_piece_iff (G := G)).mpr (Or.inr hv)
    · right
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨(mem_remainder_iff (G := G)).mpr hu,
        (mem_remainder_iff (G := G)).mpr hv⟩

/-- No ambient edge belongs to both induced cut pieces: their only common
vertex is `c`, and a simple graph has no loop at `c`. -/
theorem edge_piece_remainder_disjoint (c : V)
    (K : (deleteVertex G c).ConnectedComponent) :
    Disjoint
      (G.edgeFinset ∩ (piece G c K).sym2)
      (G.edgeFinset ∩ (remainder G c K).sym2) := by
  apply Finset.disjoint_left.2
  intro e heA heB
  cases e using Sym2.inductionOn with
  | _ u v =>
    simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset,
      Finset.mk_mem_sym2_iff] at heA heB
    have hu : u = c := by
      have humem : u ∈ piece G c K ∩ remainder G c K :=
        Finset.mem_inter.mpr ⟨heA.2.1, heB.2.1⟩
      rw [piece_inter_remainder (G := G) c K] at humem
      simpa using humem
    have hv : v = c := by
      have hvmem : v ∈ piece G c K ∩ remainder G c K :=
        Finset.mem_inter.mpr ⟨heA.2.2, heB.2.2⟩
      rw [piece_inter_remainder (G := G) c K] at hvmem
      simpa using hvmem
    exact heA.1.ne (hu.trans hv.symm)

/-- The ambient edge set is the union of the edge sets supported by the two
cut pieces. -/
theorem edge_piece_union_remainder (c : V)
    (K : (deleteVertex G c).ConnectedComponent) :
    (G.edgeFinset ∩ (piece G c K).sym2) ∪
        (G.edgeFinset ∩ (remainder G c K).sym2) = G.edgeFinset := by
  ext e
  constructor
  · simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  · intro he
    cases e using Sym2.inductionOn with
    | _ u v =>
      have huv : G.Adj u v := by simpa using he
      rcases edge_mem_piece_or_remainder (G := G) K huv with hA | hB
      · apply Finset.mem_union.mpr
        left
        simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset,
          Finset.mk_mem_sym2_iff]
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff] at hA
        exact ⟨huv, hA⟩
      · apply Finset.mem_union.mpr
        right
        simp only [Finset.mem_inter, SimpleGraph.mem_edgeFinset,
          Finset.mk_mem_sym2_iff]
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff] at hB
        exact ⟨huv, hB⟩

/-- The two induced cut pieces partition the ambient edges. -/
theorem card_edges_piece_add_card_edges_remainder (c : V)
    (K : (deleteVertex G c).ConnectedComponent) :
    (G.induce (piece G c K : Set V)).edgeFinset.card +
        (G.induce (remainder G c K : Set V)).edgeFinset.card =
      G.edgeFinset.card := by
  have hcards := congrArg Finset.card
    (edge_piece_union_remainder (G := G) c K)
  rw [Finset.card_union_of_disjoint
    (edge_piece_remainder_disjoint (G := G) c K)] at hcards
  have hAcard := G.card_filter_edgeFinset_toFinset_subset (piece G c K)
  have hBcard := G.card_filter_edgeFinset_toFinset_subset (remainder G c K)
  rw [G.filter_edgeFinset_toFinset_subset] at hAcard hBcard
  omega

/-- The complementary cut piece is proper because the chosen component side
is nonempty. -/
theorem remainder_ne_univ (c : V)
    (K : (deleteVertex G c).ConnectedComponent) :
    remainder G c K ≠ Finset.univ := by
  obtain ⟨v, hv⟩ := ComponentEndBlock.side_nonempty (G := G) c K
  intro h
  have : v ∈ remainder G c K := by rw [h]; simp
  exact ((mem_remainder_iff (G := G)).mp this) hv

/-- At a genuine cut vertex, every individual component piece is proper. -/
theorem piece_ne_univ {c : V} (hc : IsCutVertex G c)
    (K : (deleteVertex G c).ConnectedComponent) :
    piece G c K ≠ Finset.univ := by
  obtain ⟨u, v, huv⟩ := (isCutVertex_iff_exists_not_reachable G c).mp hc
  have huvcomp :
      (deleteVertex G c).connectedComponentMk u ≠
        (deleteVertex G c).connectedComponentMk v := by
    intro h
    exact huv (SimpleGraph.ConnectedComponent.exact h)
  by_cases hKu : K = (deleteVertex G c).connectedComponentMk u
  · intro hfull
    have hvpiece : v.1 ∈ piece G c K := by rw [hfull]; simp
    rw [mem_piece_iff] at hvpiece
    rcases hvpiece with hvc | hvside
    · exact v.2 hvc
    · obtain ⟨hvc, hvK⟩ := hvside
      have hvcomp :
          (deleteVertex G c).connectedComponentMk v = K := by
        simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff,
          Subtype.coe_eta] using hvK
      exact huvcomp (hKu.symm.trans hvcomp.symm)
  · intro hfull
    have hupiece : u.1 ∈ piece G c K := by rw [hfull]; simp
    rw [mem_piece_iff] at hupiece
    rcases hupiece with huc | huside
    · exact u.2 huc
    · obtain ⟨huc, huK⟩ := huside
      apply hKu
      have hucomp :
          (deleteVertex G c).connectedComponentMk u = K := by
        simpa only [SimpleGraph.ConnectedComponent.mem_supp_iff,
          Subtype.coe_eta] using huK
      exact hucomp.symm

/-- The selected component piece is connected. -/
theorem piece_connected (hG : G.Connected) (c : V)
    (K : (deleteVertex G c).ConnectedComponent) :
    (G.induce (piece G c K : Set V)).Connected := by
  rw [coe_piece]
  exact ComponentEndBlock.verts_connected hG K

/-- Density splits across a cut vertex: if `m + 2 ≥ 2n`, then one of the two
proper induced pieces satisfies the same inequality. -/
theorem cut_dense_piece (hG : G.Connected) {c : V} (hc : IsCutVertex G c)
    (K : (deleteVertex G c).ConnectedComponent)
    (hdense : 2 * Fintype.card V ≤ G.edgeFinset.card + 2) :
    (piece G c K ≠ Finset.univ) ∧
    (remainder G c K ≠ Finset.univ) ∧
    ((2 * Fintype.card (piece G c K) ≤
        (G.induce (piece G c K : Set V)).edgeFinset.card + 2) ∨
      (2 * Fintype.card (remainder G c K) ≤
        (G.induce (remainder G c K : Set V)).edgeFinset.card + 2)) := by
  refine ⟨piece_ne_univ (G := G) hc K, remainder_ne_univ (G := G) c K, ?_⟩
  have hv := card_piece_add_card_remainder (G := G) c K
  have he := card_edges_piece_add_card_edges_remainder (G := G) c K
  simp only [Fintype.card_coe] at hv ⊢
  omega

end CutDensity

end Erdos916
