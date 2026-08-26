import ErdosProblems.Erdos547.TreeConvexity

/-!
# The path through a connected piece between two attachments
-/

namespace Erdos547

open SimpleGraph

variable {U : Type*} (T : SimpleGraph U)

theorem forest_path_length_eq_dist (hT : T.IsAcyclic) {u v : U}
    (p : T.Walk u v) (hp : p.IsPath) : p.length = T.dist u v := by
  obtain ⟨q, hq, hqd⟩ := p.reachable.exists_path_of_dist
  have he := (hT.subsingleton_path u v).elim ⟨p, hp⟩ ⟨q, hq⟩
  exact (congrArg (fun q : T.Path u v ↦ q.val.length) he).trans hqd

theorem exists_path_through_connected_piece (hT : T.IsAcyclic) (C : Set U)
    (hC : (T.induce C).Preconnected) {u v a b : U} (hu : u ∉ C) (hv : v ∉ C)
    (huv : u ≠ v) (ha : a ∈ C) (hb : b ∈ C) (hua : T.Adj u a) (hvb : T.Adj v b) :
    ∃ p : T.Walk u v, p.IsPath ∧ 2 ≤ p.length ∧
      ∀ w ∈ p.support, w = u ∨ w = v ∨ w ∈ C := by
  obtain ⟨q, hq⟩ := hC.exists_isPath ⟨a, ha⟩ ⟨b, hb⟩
  let f : (T.induce C) →g T := { toFun := Subtype.val, map_rel' := fun h ↦ h }
  let t := q.map f
  have ht : t.IsPath := hq.map Subtype.val_injective
  have hs := forest_path_subset_of_preconnected T hT C hC ha hb t ht
  have hu' : u ∉ t.support := fun hh ↦ hu (hs u hh)
  have hv' : v ∉ (t.cons hua).support := by
    intro hh
    simp only [Walk.support_cons, List.mem_cons] at hh
    rcases hh with hh | hh
    · exact huv hh.symm
    · exact hv (hs v hh)
  refine ⟨(t.cons hua).concat hvb.symm, (ht.cons hu').concat hv' hvb.symm, ?_, ?_⟩
  · simp only [Walk.length_concat, Walk.length_cons]
    omega
  · intro w hw
    simp only [Walk.support_concat, Walk.support_cons, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with (rfl | hw) | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (hs w hw))
    · exact Or.inr (Or.inl rfl)

end Erdos547

#print axioms Erdos547.exists_path_through_connected_piece
