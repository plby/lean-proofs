import ErdosProblems.Erdos73.SubdivisionConnectivity

/-! A finite union of path supports with a common endpoint is connected. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

theorem connected_induce_rooted_pathUnion {I V : Type*} {G : SimpleGraph V}
    (s : Finset I) (P : I → GraphPath G) (root : V) (hroot : ∀ i ∈ s, (P i).source = root) :
    (G.induce (↑(insert root (s.biUnion (fun i => (P i).vertexSet))) : Set V)).Connected := by
  let R := insert root (s.biUnion (fun i => (P i).vertexSet))
  have hr : root ∈ R := mem_insert_self _ _
  have hP (i : I) (hi : i ∈ s) : (P i).vertexSet ⊆ R := by
    intro x hx
    exact mem_insert_of_mem (mem_biUnion.mpr ⟨i, hi, hx⟩)
  have hreach (x : (R : Set V)) : (G.induce (R : Set V)).Reachable x ⟨root, hr⟩ := by
    rcases mem_insert.mp x.property with hx | hx
    · have he : x = ⟨root, hr⟩ := Subtype.ext hx
      rw [he]
    · obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
      have hri : root ∈ (P i).vertexSet := (hroot i hi) ▸ (P i).source_mem_vertexSet
      exact GraphSubdivisionModel.path_reachable_in_superset (P i) (hP i hi) hxi hri
  letI : Nonempty (R : Set V) := ⟨⟨root, hr⟩⟩
  exact ⟨fun x y => (hreach x).trans (hreach y).symm⟩

end
end Erdos73
