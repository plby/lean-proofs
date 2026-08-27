import Arxiv.Arxiv2411_18291.AlignedGluing

/-!
# The protected-family invariant for repeated clique exchange

Each prepared edge has a negative clique and a region containing every host
edge or negative clique that touches its private vertices. Regions avoid the
private vertices of the other prepared cliques. These conditions imply the
frame admissibility required in `lem:OO` and prevent later attachment
interfaces from touching previously prepared private vertices.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V] {q r : ℕ} {ι : Type*}

structure PreparedFamily (G : Hypergraph V r) (D : Finset (Block V q))
    (B : Block V q) (s : Finset ι) (edge : ι → Block V r) where
  clique : ι → Block V q
  region : ι → Finset V
  clique_mem : ∀ i ∈ s, clique i ∈ D
  edge_subset : ∀ i ∈ s, (edge i).val ⊆ (clique i).val
  clique_subset : ∀ i ∈ s, (clique i).val ⊆ region i
  region_base : ∀ i ∈ s, region i ∩ B.val = (edge i).val
  separated : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (region i) ((clique j).val \ B.val)
  edge_local : ∀ i ∈ s, ∀ e ∈ G,
    ¬Disjoint e.val ((clique i).val \ B.val) → e.val ⊆ region i
  clique_local : ∀ i ∈ s, ∀ Q ∈ D,
    ¬Disjoint Q.val ((clique i).val \ B.val) → Q.val ⊆ region i

namespace PreparedFamily

variable {G : Hypergraph V r} {D : Finset (Block V q)} {B : Block V q}
variable {s : Finset ι} {edge : ι → Block V r}

def empty (G : Hypergraph V r) (D : Finset (Block V q)) (B : Block V q)
    (edge : ι → Block V r) : PreparedFamily G D B ∅ edge where
  clique := fun _ => B
  region := fun _ => ∅
  clique_mem := by simp
  edge_subset := by simp
  clique_subset := by simp
  region_base := by simp
  separated := by simp
  edge_local := by simp
  clique_local := by simp

theorem edge_base (P : PreparedFamily G D B s edge) {i : ι} (hi : i ∈ s) :
    (edge i).val ⊆ B.val := by
  rw [← P.region_base i hi]
  exact inter_subset_right

theorem clique_inter_base (P : PreparedFamily G D B s edge) {i : ι} (hi : i ∈ s) :
    (P.clique i).val ∩ B.val = (edge i).val := by
  apply subset_antisymm
  · intro v hv
    rw [← P.region_base i hi]
    exact mem_inter.mpr ⟨P.clique_subset i hi (mem_inter.mp hv).1, (mem_inter.mp hv).2⟩
  · exact subset_inter (P.edge_subset i hi) (P.edge_base hi)

theorem private_nonempty (P : PreparedFamily G D B s edge) (hqr : r < q)
    {i : ι} (hi : i ∈ s) : ((P.clique i).val \ B.val).Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro h
  have hNB := sdiff_eq_empty_iff_subset.mp h
  have hNE : (P.clique i).val ⊆ (edge i).val := by
    rw [← P.clique_inter_base hi]
    exact subset_inter Subset.rfl hNB
  have hc := card_le_card hNE
  rw [(P.clique i).property, (edge i).property] at hc
  omega

/-- The negative clique through a new base edge avoids every previously
prepared private set. -/
theorem avoids_interface (P : PreparedFamily G D B s edge)
    (hinj : Function.Injective edge) {j : ι} (hj : j ∉ s)
    (hjB : (edge j).val ⊆ B.val) {C : Block V q} (hC : C ∈ D)
    (hjC : (edge j).val ⊆ C.val) :
    ∀ i ∈ s, Disjoint C.val ((P.clique i).val \ B.val) := by
  intro i hi
  by_contra hcontact
  have hCR := P.clique_local i hi C hC hcontact
  have he : (edge j).val ⊆ (edge i).val := by
    rw [← P.region_base i hi]
    exact subset_inter (hjC.trans hCR) hjB
  have hji : edge j = edge i :=
    Subtype.ext (eq_of_subset_of_card_le he (by rw [(edge i).property, (edge j).property]))
  exact hj (hinj hji ▸ hi)

def frame (P : PreparedFamily G D B s edge) : Finset V :=
  B.val ∪ s.biUnion (fun i => (P.clique i).val)

theorem region_inter_frame_subset (P : PreparedFamily G D B s edge)
    {i : ι} (hi : i ∈ s) : P.region i ∩ P.frame ⊆ (P.clique i).val := by
  intro v hv
  obtain ⟨hvR, hvF⟩ := mem_inter.mp hv
  by_cases hvB : v ∈ B.val
  · apply P.edge_subset i hi
    rw [← P.region_base i hi]
    exact mem_inter.mpr ⟨hvR, hvB⟩
  · obtain ⟨j, hj, hvN⟩ := mem_biUnion.mp ((mem_union.mp hvF).resolve_left hvB)
    by_cases hij : i = j
    · simpa only [hij] using hvN
    · exact (Finset.disjoint_left.mp (P.separated i hi j hj hij)
        hvR (mem_sdiff.mpr ⟨hvN, hvB⟩)).elim

/-- The frame condition in part (ii) of the exchange lemma. -/
theorem admissible (P : PreparedFamily G D B s edge) {e : Block V r} (he : e ∈ G) :
    e.val ∩ P.frame ⊆ B.val ∨ ∃ i ∈ s, e.val ∩ P.frame ⊆ (P.clique i).val := by
  by_cases h : e.val ∩ P.frame ⊆ B.val
  · exact Or.inl h
  · obtain ⟨v, hv, hvB⟩ := Finset.not_subset.mp h
    obtain ⟨hve, hvF⟩ := mem_inter.mp hv
    obtain ⟨i, hi, hvN⟩ := mem_biUnion.mp ((mem_union.mp hvF).resolve_left hvB)
    have hcontact : ¬Disjoint e.val ((P.clique i).val \ B.val) := by
      intro hd
      exact Finset.disjoint_left.mp hd hve (mem_sdiff.mpr ⟨hvN, hvB⟩)
    have her := P.edge_local i hi e he hcontact
    refine Or.inr ⟨i, hi, ?_⟩
    intro x hx
    exact P.region_inter_frame_subset hi
      (mem_inter.mpr ⟨her (mem_inter.mp hx).1, (mem_inter.mp hx).2⟩)

theorem private_pairwise (P : PreparedFamily G D B s edge) :
    (s : Set ι).Pairwise fun i j =>
      Disjoint ((P.clique i).val \ B.val) ((P.clique j).val \ B.val) := by
  intro i hi j hj hij
  exact disjoint_of_subset_left (sdiff_subset.trans (P.clique_subset i hi))
    (P.separated i hi j hj hij)

variable [Fintype V] in
theorem clique_edge_inter (P : PreparedFamily G D B s edge) {i : ι} (hi : i ∈ s) :
    cliqueEdges r (P.clique i) ∩ cliqueEdges r B = {edge i} :=
  cliqueEdges_inter_eq_singleton _ _ _ (P.clique_inter_base hi)

variable {W : Type*} [DecidableEq W]

/-- Relabel all prepared cliques and their protecting regions simultaneously. -/
def map (P : PreparedFamily G D B s edge) (f : V ↪ W) :
    PreparedFamily (mapGraph f G) (mapGraph f D) (mapBlock f B) s
      (fun i => mapBlock f (edge i)) where
  clique := fun i => mapBlock f (P.clique i)
  region := fun i => (P.region i).map f
  clique_mem := by
    intro i hi
    exact (mem_mapGraph f D _).mpr ⟨P.clique i, P.clique_mem i hi, rfl⟩
  edge_subset := by
    intro i hi
    exact (mapBlock_subset_mapBlock f _ _).mpr (P.edge_subset i hi)
  clique_subset := by
    intro i hi
    exact map_subset_map.mpr (P.clique_subset i hi)
  region_base := by
    intro i hi
    change (P.region i).map f ∩ B.val.map f = (edge i).val.map f
    rw [← map_inter, P.region_base i hi]
  separated := by
    intro i hi j hj hij
    change Disjoint ((P.region i).map f) ((P.clique j).val.map f \ B.val.map f)
    rw [← map_sdiff, disjoint_map]
    exact P.separated i hi j hj hij
  edge_local := by
    intro i hi e he hcontact
    obtain ⟨a, ha, rfl⟩ := (mem_mapGraph f G e).mp he
    change ¬Disjoint (a.val.map f) ((P.clique i).val.map f \ B.val.map f) at hcontact
    rw [← map_sdiff, disjoint_map] at hcontact
    exact map_subset_map.mpr (P.edge_local i hi a ha hcontact)
  clique_local := by
    intro i hi Q hQ hcontact
    obtain ⟨C, hC, rfl⟩ := (mem_mapGraph f D Q).mp hQ
    change ¬Disjoint (C.val.map f) ((P.clique i).val.map f \ B.val.map f) at hcontact
    rw [← map_sdiff, disjoint_map] at hcontact
    exact map_subset_map.mpr (P.clique_local i hi C hC hcontact)

end PreparedFamily

end Arxiv2411_18291
