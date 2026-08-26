import ErdosProblems.Erdos547.ShrubRootColours

/-!
# Indexing shrubs and the domain of a partial shrub embedding
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph

variable {U : Type*} [Fintype U] [DecidableEq U] {T : SimpleGraph U}
  [DecidableRel T.Adj] {r : U} {ℓ : ℕ} {col : T.Coloring (Fin 2)}
variable (P : FineTreePartition T r ℓ col)

noncomputable def shrubColour (S : ↥P.shrubs) : Fin 2 :=
  (P.exists_unique_shrub_colour S.property).choose

theorem mem_shrubsOfColour (S : ↥P.shrubs) : S.val ∈ P.shrubsOfColour (P.shrubColour S) :=
  (P.exists_unique_shrub_colour S.property).choose_spec.1

noncomputable def nearPart (S : ↥P.shrubs) : Finset U :=
  by classical exact S.val.filter (fun v ↦ col v ≠ P.shrubColour S)

noncomputable def farPart (S : ↥P.shrubs) : Finset U :=
  by classical exact S.val.filter (fun v ↦ col v = P.shrubColour S)

theorem parts_card (S : ↥P.shrubs) :
    (P.nearPart S).card + (P.farPart S).card = S.val.card := by
  classical
  simpa only [nearPart, farPart, Nat.add_comm] using
    Finset.card_filter_add_card_filter_not (s := S.val) (fun v ↦ col v = P.shrubColour S)

theorem nearPart_nonempty (S : ↥P.shrubs) : (P.nearPart S).Nonempty :=
  Finset.card_pos.mp (P.near_shrub_size_positive _ _ (P.mem_shrubsOfColour S))

def shrubDomain (E : Finset ↥P.shrubs) : Finset U := P.seeds ∪ E.biUnion Subtype.val

theorem seeds_subset_shrubDomain (E : Finset ↥P.shrubs) : P.seeds ⊆ P.shrubDomain E :=
  Finset.subset_union_left

theorem shrub_subset_domain {E : Finset ↥P.shrubs} {S : ↥P.shrubs} (hS : S ∈ E) :
    S.val ⊆ P.shrubDomain E := by
  intro v hv
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨S, hS, hv⟩)

theorem shrubDomain_mono {E F : Finset ↥P.shrubs} (h : E ⊆ F) :
    P.shrubDomain E ⊆ P.shrubDomain F := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact P.seeds_subset_shrubDomain F hv
  · obtain ⟨S, hS, hvS⟩ := Finset.mem_biUnion.mp hv
    exact P.shrub_subset_domain (h hS) hvS

@[simp] theorem shrubDomain_empty : P.shrubDomain ∅ = P.seeds := by
  simp [shrubDomain]

@[simp] theorem shrubDomain_insert (S : ↥P.shrubs) (E : Finset ↥P.shrubs) :
    P.shrubDomain (insert S E) = P.shrubDomain E ∪ S.val := by
  simp only [shrubDomain, Finset.biUnion_insert]
  ac_rfl

theorem shrubDomain_disjoint {E : Finset ↥P.shrubs} {S : ↥P.shrubs} (hS : S ∉ E) :
    Disjoint (P.shrubDomain E) S.val := by
  apply Finset.disjoint_left.mpr
  intro v hv hvS
  rcases Finset.mem_union.mp hv with hv | hv
  · exact Finset.disjoint_left.mp (P.disjoint_seeds S.val S.property) hvS hv
  · obtain ⟨A, hA, hvA⟩ := Finset.mem_biUnion.mp hv
    have hAS : A.val ≠ S.val := fun he ↦ hS ((Subtype.ext he) ▸ hA)
    exact Finset.disjoint_left.mp
      (P.disjoint_shrubs A.val A.property S.val S.property hAS) hvA hvS

theorem shrubDomain_univ : P.shrubDomain Finset.univ = Finset.univ := by
  have he : (Finset.univ : Finset ↥P.shrubs).biUnion Subtype.val = P.shrubs.biUnion id := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Subtype.exists, id_eq]
    constructor <;> rintro ⟨a, ha, hv⟩ <;> exact ⟨a, ha, hv⟩
  rw [shrubDomain, he, P.cover]

end Erdos547.FineTreePartition
