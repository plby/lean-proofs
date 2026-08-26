import ErdosProblems.Erdos73.CycleDeletionConnected

/-! Build deletion-one-connected supports by gluing pieces along at least two vertices. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def DeletionOneConnected (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ X : Finset V, X.card < 2 → (G.induce ((S \ X : Finset V) : Set V)).Connected

theorem DeletionOneConnected.of_cycle {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    DeletionOneConnected G c.support.toFinset := cycle_support_sdiff_connected c hc

theorem DeletionOneConnected.union {S T : Finset V}
    (hS : DeletionOneConnected G S) (hT : DeletionOneConnected G T)
    (hST : 2 ≤ (S ∩ T).card) : DeletionOneConnected G (S ∪ T) := by
  intro X hX
  have hex : ∃ v ∈ S ∩ T, v ∉ X := by
    by_contra hn
    push Not at hn
    have hh := card_le_card (show S ∩ T ⊆ X from hn)
    omega
  obtain ⟨v, hv, hvX⟩ := hex
  have hcommon : (((S \ X : Finset V) : Set V) ∩ ((T \ X : Finset V) : Set V)).Nonempty :=
    ⟨v, mem_sdiff.mpr ⟨(mem_inter.mp hv).1, hvX⟩,
      mem_sdiff.mpr ⟨(mem_inter.mp hv).2, hvX⟩⟩
  have hconn := SimpleGraph.induce_union_connected (hS X hX).preconnected
    (hT X hX).preconnected hcommon
  have heq : ((S \ X : Finset V) : Set V) ∪ ((T \ X : Finset V) : Set V) =
      (((S ∪ T) \ X : Finset V) : Set V) := by
    ext x
    simp only [Set.mem_union, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_union]
    tauto
  rwa [heq] at hconn

theorem DeletionOneConnected.induced_delete_preconnected {S : Finset V}
    (hS : DeletionOneConnected G S) (X : Finset (S : Set V)) (hX : X.card < 2) :
    ((G.induce (S : Set V)).induce (X : Set (S : Set V))ᶜ).Preconnected := by
  let Y := X.image Subtype.val
  have hY : Y.card < 2 := card_image_le.trans_lt hX
  let f : G.induce ((S \ Y : Finset V) : Set V) →g
      (G.induce (S : Set V)).induce (X : Set (S : Set V))ᶜ := {
    toFun := fun x => ⟨⟨x.val, (mem_sdiff.mp x.property).1⟩, by
      intro hx
      exact (mem_sdiff.mp x.property).2 (mem_image.mpr ⟨_, hx, rfl⟩)⟩
    map_rel' := fun h => h }
  have hf : Function.Surjective f := by
    intro z
    have hzY : z.val.val ∉ Y := by
      intro hz
      obtain ⟨w, hw, he⟩ := mem_image.mp hz
      have hh : w = z.val := Subtype.ext he
      exact z.property (hh ▸ hw)
    exact ⟨⟨z.val.val, mem_sdiff.mpr ⟨z.val.property, hzY⟩⟩, rfl⟩
  exact (hS Y hY).preconnected.map f hf

end
end Erdos73
