import ErdosProblems.Erdos547.AttachmentPath
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# A copy of a tree in a forest preserves distances
-/

namespace Erdos547

open SimpleGraph

theorem tree_copy_dist_eq {U V : Type*} {T : SimpleGraph U} {G : SimpleGraph V}
    (hT : T.IsTree) (hG : G.IsAcyclic) (f : T.Copy G) (u v : U) :
    G.dist (f u) (f v) = T.dist u v := by
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath u v
  have hleft := forest_path_length_eq_dist G hG (p.map f.toHom) (hp.map f.injective)
  have hright := forest_path_length_eq_dist T hT.isAcyclic p hp
  rw [Walk.length_map] at hleft
  exact hleft.symm.trans hright

end Erdos547

#print axioms Erdos547.tree_copy_dist_eq
