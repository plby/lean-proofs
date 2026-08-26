import ErdosProblems.Erdos547.PartitionPadding

/-!
# Counting the contribution of disjoint indexed padding arms
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph

variable {U I : Type*} [Fintype U] [DecidableEq U] [Fintype I] {T : SimpleGraph U}
  [DecidableRel T.Adj] {r : U} {ℓ : ℕ} {col : T.Coloring (Fin 2)}

theorem indexed_two_paths_part_lower (P : FineTreePartition T r ℓ col) (z : U)
    (hz : z ∈ P.seeds) (w y : I → U) (hw : Function.Injective w) (hy : Function.Injective y)
    (hne : ∀ i, z ≠ y i) (hzw : ∀ i, T.Adj z (w i)) (hwy : ∀ i, T.Adj (w i) (y i)) :
    Fintype.card I ≤ (P.nearVertices (col z)).card + P.seeds.card ∧
      Fintype.card I ≤ (P.farVertices (col z)).card + P.seeds.card := by
  classical
  let good := (Finset.univ : Finset I).filter (fun i ↦ w i ∉ P.seeds)
  let bad := (Finset.univ : Finset I).filter (fun i ↦ w i ∈ P.seeds)
  have hbad : bad.card ≤ P.seeds.card := by
    have hsub : bad.image w ⊆ P.seeds := by
      intro u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact (Finset.mem_filter.mp hi).2
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ hw] at hh
  have hsplit : bad.card + good.card = Fintype.card I := by
    simpa only [bad, good, Finset.card_univ] using
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset I))
        (fun i ↦ w i ∈ P.seeds)
  have hparts (i : I) (hi : i ∈ good) :
      w i ∈ P.nearVertices (col z) ∧ y i ∈ P.farVertices (col z) :=
    P.two_path_vertices_in_parts hz (Finset.mem_filter.mp hi).2 (hne i) (hzw i) (hwy i)
  have hnear : good.card ≤ (P.nearVertices (col z)).card := by
    have hsub : good.image w ⊆ P.nearVertices (col z) := by
      intro u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact (hparts i hi).1
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ hw] at hh
  have hfar : good.card ≤ (P.farVertices (col z)).card := by
    have hsub : good.image y ⊆ P.farVertices (col z) := by
      intro u hu
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
      exact (hparts i hi).2
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ hy] at hh
  constructor <;> omega

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.indexed_two_paths_part_lower
