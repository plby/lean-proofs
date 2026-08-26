import ErdosProblems.Erdos547.ShrubRoots
import ErdosProblems.Erdos547.AdventitiousCount

/-!
# Counting the adventitious roots in an arbitrary choice of shrub root data
-/

namespace Erdos547

open Finset SimpleGraph

theorem ShrubRootData.secondary_seed_ne {U : Type*} {T : SimpleGraph U}
    {W S : Finset U} (D : ShrubRootData T W S) (hT : T.IsAcyclic) (hdis : Disjoint S W)
    {z : ↥W × ↥S} (hz : D.second = some z) : z.1 ≠ D.seed := by
  intro he
  have hsec := D.secondary_edge z hz
  rw [he] at hsec
  have hroot : D.root = z.2 := by
    apply Subtype.ext
    exact unique_attachment_to_connected hT (S : Set U) D.rooted.isTree.connected.preconnected
      (fun hmem ↦ Finset.disjoint_left.mp hdis hmem D.seed.property)
      D.root.property z.2.property D.primary_edge hsec
  have hdist := D.rooted.distance_lower z.2 (by rw [hz]; rfl)
  rw [hroot, SimpleGraph.dist_self] at hdist
  omega

namespace FineTreePartition

variable {U : Type*} [Fintype U] [DecidableEq U] {T : SimpleGraph U}
  [DecidableRel T.Adj] {r : U} {ℓ : ℕ} {col : T.Coloring (Fin 2)}
variable (P : FineTreePartition T r ℓ col)

theorem secondary_implies_two_attachments (hT : T.IsTree) (S : Finset U) (hS : S ∈ P.shrubs)
    (D : ShrubRootData T P.seeds S) (hsecond : D.second.isSome) :
    2 ≤ (P.seeds.filter (fun z ↦ 0 < degreeIn T S z)).card := by
  classical
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp hsecond
  have hprim : D.seed.val ∈ P.seeds.filter (fun z ↦ 0 < degreeIn T S z) := by
    refine Finset.mem_filter.mpr ⟨D.seed.property, ?_⟩
    exact Finset.card_pos.mpr ⟨D.root.val,
      Finset.mem_filter.mpr ⟨D.root.property, D.primary_edge⟩⟩
  have hsec : z.1.val ∈ P.seeds.filter (fun z ↦ 0 < degreeIn T S z) := by
    refine Finset.mem_filter.mpr ⟨z.1.property, ?_⟩
    exact Finset.card_pos.mpr ⟨z.2.val,
      Finset.mem_filter.mpr ⟨z.2.property, D.secondary_edge z hz⟩⟩
  have hne : D.seed.val ≠ z.1.val := fun he ↦
    D.secondary_seed_ne hT.isAcyclic (P.disjoint_seeds S hS) hz (Subtype.ext he.symm)
  exact Finset.one_lt_card.mpr ⟨D.seed.val, hprim, z.1.val, hsec, hne⟩

open scoped Classical in
theorem second_roots_add_one_le_seeds (hT : T.IsTree)
    (D : ∀ S : ↥P.shrubs, ShrubRootData T P.seeds S.val) :
    (((Finset.univ : Finset ↥P.shrubs).filter (fun S ↦ (D S).second.isSome)).card) + 1 ≤
      P.seeds.card := by
  classical
  let A := (Finset.univ : Finset ↥P.shrubs).filter (fun S ↦ (D S).second.isSome)
  let B := P.shrubs.filter (fun S ↦ 2 ≤
    (P.seeds.filter (fun z ↦ 0 < degreeIn T S z)).card)
  have hsub : A.image Subtype.val ⊆ B := by
    intro S hS
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_filter.mpr ⟨Q.property,
      P.secondary_implies_two_attachments hT Q.val Q.property (D Q) (Finset.mem_filter.mp hQ).2⟩
  have hcard : A.card ≤ B.card := by
    rw [← Finset.card_image_of_injective A Subtype.val_injective]
    exact Finset.card_le_card hsub
  have hbound := P.two_attachment_shrubs_add_one_le_seeds hT
  change B.card + 1 ≤ P.seeds.card at hbound
  change A.card + 1 ≤ P.seeds.card
  omega

end FineTreePartition

end Erdos547

#print axioms Erdos547.FineTreePartition.second_roots_add_one_le_seeds
