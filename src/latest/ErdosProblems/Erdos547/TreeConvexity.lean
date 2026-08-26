import ErdosProblems.Erdos547.RootedPieces

/-!
# Convexity of connected induced subgraphs of a forest
-/

namespace Erdos547

open SimpleGraph

variable {U : Type*} (T : SimpleGraph U)

theorem forest_path_subset_of_preconnected (hT : T.IsAcyclic) (S : Set U)
    (hS : (T.induce S).Preconnected) {a b : U} (ha : a ∈ S) (hb : b ∈ S)
    (p : T.Walk a b) (hp : p.IsPath) : ∀ u ∈ p.support, u ∈ S := by
  obtain ⟨q, hq⟩ := hS.exists_isPath ⟨a, ha⟩ ⟨b, hb⟩
  let f : (T.induce S) →g T := { toFun := Subtype.val, map_rel' := fun h ↦ h }
  have heq : p = q.map f :=
    congrArg Subtype.val ((hT.subsingleton_path a b).elim
      ⟨p, hp⟩ ⟨q.map f, hq.map Subtype.val_injective⟩)
  intro u hu
  have hu' : u ∈ (q.map f).support := heq ▸ hu
  rw [Walk.support_map] at hu'
  obtain ⟨v, _, hval⟩ := List.mem_map.mp hu'
  have hf : f v = v.val := rfl
  exact (hf.symm.trans hval) ▸ v.property

theorem forest_preconnected_inter (hT : T.IsAcyclic) (A B : Set U)
    (hA : (T.induce A).Preconnected) (hB : (T.induce B).Preconnected) :
    (T.induce (A ∩ B)).Preconnected := by
  intro a b
  obtain ⟨q, hq⟩ := hA.exists_isPath ⟨a.val, a.property.1⟩ ⟨b.val, b.property.1⟩
  let f : (T.induce A) →g T := { toFun := Subtype.val, map_rel' := fun h ↦ h }
  let p := q.map f
  have hp : p.IsPath := hq.map Subtype.val_injective
  have hpa := forest_path_subset_of_preconnected T hT A hA a.property.1 b.property.1 p hp
  have hpb := forest_path_subset_of_preconnected T hT B hB a.property.2 b.property.2 p hp
  have hs : ∀ u ∈ p.support, u ∈ A ∩ B := fun u hu ↦ ⟨hpa u hu, hpb u hu⟩
  exact (p.induce (A ∩ B) hs).reachable

theorem forest_connected_inter (hT : T.IsAcyclic) (A B : Set U)
    (hA : (T.induce A).Preconnected) (hB : (T.induce B).Preconnected)
    (hne : (A ∩ B).Nonempty) : (T.induce (A ∩ B)).Connected := by
  letI : Nonempty ↥(A ∩ B) := hne.to_subtype
  exact ⟨forest_preconnected_inter T hT A B hA hB⟩

end Erdos547

#print axioms Erdos547.forest_connected_inter
