/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.RootTwoPathReinsert

/-! Injective selection and outward orientation of pendant two-paths. -/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim617RootPaths.RootTwoPathSystem

open SimpleGraph

variable {V I J : Type*} [Fintype V] [DecidableEq V] [Fintype I] [Fintype J]
variable {T : SimpleGraph V}

def reindex (D : RootTwoPathSystem T I) (f : J → I) (hf : Function.Injective f) :
    RootTwoPathSystem T J where
  parent j := D.parent (f j)
  middle j := D.middle (f j)
  leaf j := D.leaf (f j)
  middle_injective := D.middle_injective.comp hf
  leaf_injective := D.leaf_injective.comp hf
  middle_ne_leaf j k := D.middle_ne_leaf (f j) (f k)
  parent_ne_middle j k := D.parent_ne_middle (f j) (f k)
  parent_ne_leaf j k := D.parent_ne_leaf (f j) (f k)
  parent_middle_adj j := D.parent_middle_adj (f j)
  middle_leaf_adj j := D.middle_leaf_adj (f j)
  middle_neighbors j := D.middle_neighbors (f j)
  leaf_neighbors j := D.leaf_neighbors (f j)

theorem leafDist_of_ne_root (D : RootTwoPathSystem T I) (hT : T.IsTree)
    (root : V) (hleaf : ∀ i, D.leaf i ≠ root) (i : I) :
    T.dist root (D.middle i) + 1 = T.dist root (D.leaf i) := by
  let p := Erdos547b.TreePartition.parent hT root (hleaf i)
  have hpAdj : T.Adj (D.leaf i) p :=
    (Erdos547b.TreePartition.parent_adj hT root (hleaf i)).symm
  have hpEq : p = D.middle i := D.leaf_neighbors i p hpAdj
  simpa only [← hpEq] using Erdos547b.TreePartition.parent_dist_add_one hT root (hleaf i)

theorem parentDist_of_ne_root (D : RootTwoPathSystem T I) (hT : T.IsTree)
    (root : V) (hmiddle : ∀ i, D.middle i ≠ root) (hleaf : ∀ i, D.leaf i ≠ root)
    (i : I) : T.dist root (D.parent i) + 1 = T.dist root (D.middle i) := by
  let p := Erdos547b.TreePartition.parent hT root (hmiddle i)
  have hpAdj : T.Adj (D.middle i) p :=
    (Erdos547b.TreePartition.parent_adj hT root (hmiddle i)).symm
  have hpDist : T.dist root p + 1 = T.dist root (D.middle i) :=
    Erdos547b.TreePartition.parent_dist_add_one hT root (hmiddle i)
  rcases D.middle_neighbors i p hpAdj with hp | hp
  · simpa only [hp] using hpDist
  · have hl := D.leafDist_of_ne_root hT root hleaf i
    rw [hp] at hpDist
    omega

/-- Deleting all middle/leaf pairs saves exactly two vertices per path. -/
theorem core_card_add_twice [DecidableEq I] (D : RootTwoPathSystem T I) :
    Fintype.card {x // x ∉ D.middleSet} + 2 * Fintype.card I = Fintype.card V := by
  classical
  have hl : D.leafSet.card = Fintype.card I := by
    rw [leafSet, Finset.card_image_of_injective _ D.leaf_injective, Finset.card_univ]
  have hmi : Function.Injective D.middleVertex := by
    intro i j h
    exact D.middle_injective (congrArg Subtype.val h)
  have hm : D.middleSet.card = Fintype.card I := by
    rw [middleSet, Finset.card_image_of_injective _ hmi, Finset.card_univ]
  have hlb := Finset.card_le_univ D.leafSet
  have hmb := Finset.card_le_univ D.middleSet
  rw [Fintype.card_subtype_compl, Fintype.card_coe,
    Fintype.card_subtype_compl, Fintype.card_coe, hl, hm]
  rw [Fintype.card_subtype_compl, Fintype.card_coe, hl, hm] at hmb
  rw [hl] at hlb
  omega

end Erdos547b.ZhaoClaim617RootPaths.RootTwoPathSystem

#print axioms Erdos547b.ZhaoClaim617RootPaths.RootTwoPathSystem.reindex
#print axioms Erdos547b.ZhaoClaim617RootPaths.RootTwoPathSystem.parentDist_of_ne_root
#print axioms Erdos547b.ZhaoClaim617RootPaths.RootTwoPathSystem.core_card_add_twice
