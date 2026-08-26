import ErdosProblems.Erdos547.ShrubRoots
import ErdosProblems.Erdos547.ShrubColours

/-!
# Root parity agrees with the near and far shrub parts
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph

variable {U : Type*} [Fintype U] [DecidableEq U] {T : SimpleGraph U}
  [DecidableRel T.Adj] {r : U} {ℓ : ℕ} {col : T.Coloring (Fin 2)}
variable (P : FineTreePartition T r ℓ col)

theorem shrub_seed_colour (c : Fin 2) (S : Finset U) (hS : S ∈ P.shrubsOfColour c)
    (D : ShrubRootData T P.seeds S) : col D.seed.val = c := by
  classical
  apply (Finset.mem_filter.mp hS).2 D.seed.val D.seed.property
  exact Finset.card_pos.mpr ⟨D.root.val,
    Finset.mem_filter.mpr ⟨D.root.property, D.primary_edge⟩⟩

theorem shrub_root_colour_ne (c : Fin 2) (S : Finset U) (hS : S ∈ P.shrubsOfColour c)
    (D : ShrubRootData T P.seeds S) : col D.root.val ≠ c := by
  have hh := (col.valid D.primary_edge).symm
  rwa [P.shrub_seed_colour c S hS D] at hh

theorem shrub_root_even_iff_near (c : Fin 2) (S : Finset U) (hS : S ∈ P.shrubsOfColour c)
    (D : ShrubRootData T P.seeds S) (v : ↥S) :
    (T.induce (S : Set U)).dist D.root v % 2 = 0 ↔ col v.val ≠ c := by
  let cS : (T.induce (S : Set U)).Coloring (Fin 2) := {
    toFun := fun z ↦ col z.val
    map_rel' := fun h ↦ col.valid h
  }
  rw [dist_even_iff_colour_eq _ D.rooted.isTree.connected.preconnected cS D.root v]
  change col D.root.val = col v.val ↔ col v.val ≠ c
  have hne := P.shrub_root_colour_ne c S hS D
  omega

open scoped Classical in
theorem near_shrub_size_positive (c : Fin 2) (S : Finset U) (hS : S ∈ P.shrubsOfColour c) :
    0 < (S.filter (fun v ↦ col v ≠ c)).card := by
  classical
  obtain ⟨z, hz, hdz⟩ := P.has_attachment S (Finset.mem_filter.mp hS).1
  have hcolz := (Finset.mem_filter.mp hS).2 z hz hdz
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hdz
  obtain ⟨hvS, hzv⟩ := Finset.mem_filter.mp hv
  have hne := (col.valid hzv).symm
  rw [hcolz] at hne
  exact Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hvS, hne⟩⟩

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.shrub_root_even_iff_near
