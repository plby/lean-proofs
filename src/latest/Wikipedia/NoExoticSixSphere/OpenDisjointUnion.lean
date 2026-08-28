import Mathlib.Topology.Homeomorph.Lemmas

/-!
# An open disjoint union has its actual coproduct topology

The literal component inclusions form a continuous open bijection from the
topological coproduct to the original union subtype.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.OpenDisjointUnion

variable {ι X : Type*} [TopologicalSpace X] (U : ι → Set X)

def inclusion : C((Σ i, U i), ⋃ i, U i) where
  toFun x := ⟨x.2.val, mem_iUnion.mpr ⟨x.1, x.2.property⟩⟩
  continuous_toFun := continuous_sigma (fun _ ↦ continuous_subtype_val.subtype_mk _)

theorem injective_inclusion (hd : Pairwise (Disjoint on U)) : Injective (inclusion U) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ he
  have hv : x.val = y.val := congrArg Subtype.val he
  have hij : i = j := by
    by_contra hne
    exact disjoint_left.mp (hd hne) x.property (hv.symm ▸ y.property)
  subst j
  have hxy : x = y := Subtype.ext hv
  cases hxy
  rfl

theorem surjective_inclusion : Surjective (inclusion U) := by
  rintro ⟨x, hx⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  exact ⟨⟨i, ⟨x, hi⟩⟩, rfl⟩

theorem isOpenMap_inclusion (hU : ∀ i, IsOpen (U i)) : IsOpenMap (inclusion U) := by
  apply isOpenMap_sigma.mpr
  intro i
  exact (hU i).isOpenEmbedding_subtypeVal.isOpenMap.subtype_mk
    (fun x ↦ mem_iUnion.mpr ⟨i, x.property⟩)

def homeomorph (hU : ∀ i, IsOpen (U i)) (hd : Pairwise (Disjoint on U)) :
    (Σ i, U i) ≃ₜ ⋃ i, U i := by
  let e := Equiv.ofBijective (inclusion U) ⟨injective_inclusion U hd, surjective_inclusion U⟩
  exact e.toHomeomorphOfContinuousOpen (inclusion U).continuous (isOpenMap_inclusion U hU)

theorem homeomorph_apply (hU : ∀ i, IsOpen (U i)) (hd : Pairwise (Disjoint on U))
    (i : ι) (x : U i) : (homeomorph U hU hd ⟨i, x⟩).val = x.val := rfl

def intersectionHomeomorph (T : Set X) (hT : IsOpen T)
    (hU : ∀ i, IsOpen (U i)) (hd : Pairwise (Disjoint on U)) :
    (Σ i, (T ∩ U i : Set X)) ≃ₜ (T ∩ ⋃ i, U i : Set X) :=
  (homeomorph (fun i ↦ T ∩ U i) (fun i ↦ hT.inter (hU i))
    (fun _ _ hne ↦ (hd hne).mono inter_subset_right inter_subset_right)).trans
      (Homeomorph.setCongr (by rw [inter_iUnion]))

theorem intersectionHomeomorph_apply (T : Set X) (hT : IsOpen T)
    (hU : ∀ i, IsOpen (U i)) (hd : Pairwise (Disjoint on U))
    (i : ι) (x : (T ∩ U i : Set X)) :
    (intersectionHomeomorph U T hT hU hd ⟨i, x⟩).val = x.val := rfl

end NoExoticSixSphere.OpenDisjointUnion
