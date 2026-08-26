import ErdosProblems.Erdos547.ShrubColours

/-!
# Degree forcing and padding arms in a fine partition
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph

variable {U : Type*} [Fintype U] [DecidableEq U] {T : SimpleGraph U}
  [DecidableRel T.Adj] {r : U} {ℓ : ℕ} {col : T.Coloring (Fin 2)}

theorem exists_shrub_of_not_seed (P : FineTreePartition T r ℓ col) {u : U}
    (hu : u ∉ P.seeds) : ∃ C ∈ P.shrubs, u ∈ C := by
  have hmem : u ∈ P.seeds ∪ P.shrubs.biUnion id := by rw [P.cover]; exact Finset.mem_univ _
  exact Finset.mem_biUnion.mp ((Finset.mem_union.mp hmem).resolve_left hu)

theorem degree_add_one_le_of_not_seed (P : FineTreePartition T r ℓ col) {u : U}
    (hu : u ∉ P.seeds) : T.degree u + 1 ≤ ℓ + P.seeds.card := by
  classical
  obtain ⟨C, hC, huC⟩ := P.exists_shrub_of_not_seed hu
  have hsub : T.neighborFinset u ⊆ C.erase u ∪ P.seeds := by
    intro v hv
    have huv := (T.mem_neighborFinset u v).mp hv
    rcases P.edge_exit C hC u huC v huv with hvC | hvS
    · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨huv.ne', hvC⟩)
    · exact Finset.mem_union_right _ hvS
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [T.card_neighborFinset_eq_degree] at hc
  have he := Finset.card_erase_add_one huC
  have hs := P.shrub_size C hC
  omega

theorem mem_seeds_of_large_degree (P : FineTreePartition T r ℓ col) {u : U}
    (hu : ℓ + P.seeds.card ≤ T.degree u) : u ∈ P.seeds := by
  by_contra hn
  have hh := P.degree_add_one_le_of_not_seed hn
  omega

theorem two_path_vertices_in_parts (P : FineTreePartition T r ℓ col) {z w y : U}
    (hz : z ∈ P.seeds) (hw : w ∉ P.seeds) (hzy : z ≠ y)
    (hzw : T.Adj z w) (hwy : T.Adj w y) :
    w ∈ P.nearVertices (col z) ∧ y ∈ P.farVertices (col z) := by
  classical
  obtain ⟨C, hC, hwC⟩ := P.exists_shrub_of_not_seed hw
  have hdz : 0 < degreeIn T C z :=
    Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hwC, hzw⟩⟩
  have hy : y ∉ P.seeds := by
    intro hyS
    have hdy : 0 < degreeIn T C y :=
      Finset.card_pos.mpr ⟨w, Finset.mem_filter.mpr ⟨hwC, hwy.symm⟩⟩
    have hl := P.attachment_distance C hC z hz y hyS hdz hdy hzy
    have hs := SimpleGraph.dist_le (Walk.cons hzw (Walk.cons hwy Walk.nil))
    have htwo : T.dist z y ≤ 2 := hs
    omega
  have hyC : y ∈ C := (P.edge_exit C hC w hwC y hwy).resolve_right hy
  have hfamily : C ∈ P.shrubsOfColour (col z) :=
    Finset.mem_filter.mpr ⟨hC, fun v hv hdv ↦ P.attachment_colour C hC v hv z hz hdv hdz⟩
  have hwV : w ∈ P.shrubVertices (col z) := Finset.mem_biUnion.mpr ⟨C, hfamily, hwC⟩
  have hyV : y ∈ P.shrubVertices (col z) := Finset.mem_biUnion.mpr ⟨C, hfamily, hyC⟩
  have hcol1 := col.valid hzw
  have hcol2 := col.valid hwy
  have hcoly : col y = col z := by
    apply Fin.ext
    have h1 : (col z).val ≠ (col w).val := fun he ↦ hcol1 (Fin.ext he)
    have h2 : (col w).val ≠ (col y).val := fun he ↦ hcol2 (Fin.ext he)
    have hzlt := (col z).isLt
    have hwlt := (col w).isLt
    have hylt := (col y).isLt
    omega
  exact ⟨Finset.mem_filter.mpr ⟨hwV, hcol1.symm⟩, Finset.mem_filter.mpr ⟨hyV, hcoly⟩⟩

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.mem_seeds_of_large_degree
#print axioms Erdos547.FineTreePartition.two_path_vertices_in_parts
