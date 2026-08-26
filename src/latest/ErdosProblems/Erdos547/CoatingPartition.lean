import ErdosProblems.Erdos547.CoatingGeometry
import ErdosProblems.Erdos547.IndexedArmsCount

/-!
# A padded tree has four large shrub parts
-/

namespace Erdos547

open Finset SimpleGraph

open scoped Classical in
theorem exists_coating_partition_at_scale {U : Type*} [Fintype U] [DecidableEq U]
    (T : SimpleGraph U) [DecidableRel T.Adj] (hT : T.IsTree)
    (col : T.Coloring (Fin 2)) (r : U) (hr : col r = 0)
    (m ℓ K a : ℕ) (hℓ : 2 ≤ ℓ) (hℓn : ℓ ≤ Fintype.card (CoatedVertex U m))
    (hK : 180 * Fintype.card (CoatedVertex U m) ≤ ℓ * K)
    (hroom : ℓ + K ≤ m) (hparts : a + K ≤ m) :
    ∃ P : FineTreePartition (coatedTree T r m) (coatingSeed r m 0) ℓ (coatedTreeColour col r m),
      P.seeds.card ≤ K ∧ ∀ i : Fin 2, a ≤ (P.nearVertices i).card ∧ a ≤ (P.farVertices i).card := by
  classical
  obtain ⟨P⟩ := nonempty_fine_tree_partition (coatedTree T r m) (coatedTree_isTree T hT r m)
    (coatingSeed r m 0) ℓ hℓ hℓn (coatedTreeColour col r m)
  have hcut : P.seeds.card ≤ K := by
    have hh := P.seeds_bound.trans hK
    by_contra hn
    have hm := Nat.mul_le_mul_left ℓ (show K + 1 ≤ P.seeds.card by omega)
    nlinarith only [hh, hm, hℓ]
  have hseeds (i : Fin 2) : coatingSeed r m i ∈ P.seeds := by
    apply P.mem_seeds_of_large_degree
    exact (Nat.add_le_add_left hcut ℓ).trans (hroom.trans (coatingSeed_degree_lower T r m i))
  refine ⟨P, hcut, ?_⟩
  intro i
  have hbound := P.indexed_two_paths_part_lower (coatingSeed r m i) (hseeds i)
    (coatingMiddle i) (coatingEnd i) (coatingMiddle_injective i) (coatingEnd_injective i)
    (coatingSeed_ne_end r m i) (coatedTree_adj_seed_middle T r m i)
    (coatedTree_adj_middle_end T r m i)
  rw [coatedTreeColour_seed col r hr m i, Fintype.card_fin] at hbound
  constructor <;> omega

end Erdos547

#print axioms Erdos547.exists_coating_partition_at_scale
