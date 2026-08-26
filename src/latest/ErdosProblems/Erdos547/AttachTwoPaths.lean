import ErdosProblems.Erdos547.AttachLeavesColour
import ErdosProblems.Erdos547.TreeCopyDistance

/-!
# Attaching length-two paths at prescribed vertices
-/

namespace Erdos547

open SimpleGraph

variable {U L : Type*}

def attachTwoPaths (T : SimpleGraph U) (parent : L → U) : SimpleGraph ((U ⊕ L) ⊕ L) :=
  attachLeaves (attachLeaves T parent) (fun l : L ↦ Sum.inr l)

instance attachTwoPaths_decidableAdj (T : SimpleGraph U) [DecidableRel T.Adj]
    [DecidableEq U] [DecidableEq L] (parent : L → U) : DecidableRel (attachTwoPaths T parent).Adj :=
  attachLeaves_decidableAdj _ _

def attachTwoPathsOldCopy (T : SimpleGraph U) (parent : L → U) : T.Copy (attachTwoPaths T parent) :=
  ⟨{ toFun := fun u ↦ Sum.inl (Sum.inl u), map_rel' := fun h ↦ h },
    Sum.inl_injective.comp Sum.inl_injective⟩

theorem attachTwoPaths_isTree [Fintype U] [Fintype L] (T : SimpleGraph U)
    [DecidableRel T.Adj] (parent : L → U) (hT : T.IsTree) : (attachTwoPaths T parent).IsTree := by
  classical
  exact attachLeaves_isTree _ _ (attachLeaves_isTree T parent hT)

theorem attachTwoPaths_dist [Fintype U] [Fintype L] (T : SimpleGraph U)
    [DecidableRel T.Adj] (parent : L → U) (hT : T.IsTree) (u v : U) :
    (attachTwoPaths T parent).dist (Sum.inl (Sum.inl u)) (Sum.inl (Sum.inl v)) = T.dist u v :=
  tree_copy_dist_eq hT (attachTwoPaths_isTree T parent hT).isAcyclic
    (attachTwoPathsOldCopy T parent) u v

def attachTwoPathsColour {T : SimpleGraph U} (parent : L → U) (col : T.Coloring (Fin 2)) :
    (attachTwoPaths T parent).Coloring (Fin 2) :=
  attachLeavesColour (fun l : L ↦ Sum.inr l) (attachLeavesColour parent col)

@[simp] theorem attachTwoPathsColour_old {T : SimpleGraph U} (parent : L → U)
    (col : T.Coloring (Fin 2)) (u : U) :
    attachTwoPathsColour parent col (Sum.inl (Sum.inl u)) = col u := rfl

@[simp] theorem attachTwoPathsColour_middle {T : SimpleGraph U} (parent : L → U)
    (col : T.Coloring (Fin 2)) (l : L) :
    attachTwoPathsColour parent col (Sum.inl (Sum.inr l)) = flipTreeColour (col (parent l)) := rfl

@[simp] theorem attachTwoPathsColour_end {T : SimpleGraph U} (parent : L → U)
    (col : T.Coloring (Fin 2)) (l : L) :
    attachTwoPathsColour parent col (Sum.inr l) = col (parent l) :=
  flipTreeColour_involutive _

end Erdos547

#print axioms Erdos547.attachTwoPaths_isTree
#print axioms Erdos547.attachTwoPaths_dist
