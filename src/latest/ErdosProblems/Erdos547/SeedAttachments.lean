import ErdosProblems.Erdos547.IndexedShrubSums
import ErdosProblems.Erdos547.ClusterImageCount

/-!
# The one or two attachment seeds as a finite subset of the seed type
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph

variable {U : Type*} [Fintype U] [DecidableEq U] {T : SimpleGraph U}
  [DecidableRel T.Adj] {r : U} {ℓ : ℕ} {col : T.Coloring (Fin 2)}
variable (P : FineTreePartition T r ℓ col)

noncomputable def attachmentSeeds (S : ↥P.shrubs) : Finset ↥P.seeds :=
  Finset.univ.filter (fun z ↦ 0 < degreeIn T S.val z.val)

theorem attachmentSeeds_card (S : ↥P.shrubs) : (P.attachmentSeeds S).card ≤ 2 := by
  rw [attachmentSeeds, card_coe_filter_univ P.seeds (fun z ↦ 0 < degreeIn T S.val z)]
  exact P.attachment_count S.val S.property

theorem attachmentSeeds_colour (S : ↥P.shrubs) (z : ↥P.seeds) (hz : z ∈ P.attachmentSeeds S) :
    col z.val = P.shrubColour S := by
  exact (Finset.mem_filter.mp (P.mem_shrubsOfColour S)).2 z.val z.property
    (Finset.mem_filter.mp hz).2

theorem primary_mem_attachmentSeeds (S : ↥P.shrubs) (D : ShrubRootData T P.seeds S.val) :
    D.seed ∈ P.attachmentSeeds S := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, Finset.card_pos.mpr
    ⟨D.root.val, Finset.mem_filter.mpr ⟨D.root.property, D.primary_edge⟩⟩⟩

theorem secondary_mem_attachmentSeeds (S : ↥P.shrubs) (D : ShrubRootData T P.seeds S.val)
    (z : ↥P.seeds × ↥S.val) (hz : D.second = some z) : z.1 ∈ P.attachmentSeeds S := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, Finset.card_pos.mpr
    ⟨z.2.val, Finset.mem_filter.mpr ⟨z.2.property, D.secondary_edge z hz⟩⟩⟩

end Erdos547.FineTreePartition
