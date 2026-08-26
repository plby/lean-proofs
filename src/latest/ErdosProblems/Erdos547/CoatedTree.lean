import ErdosProblems.Erdos547.AttachTwoPaths

/-!
# An integer tree-padding construction

Add one new cut vertex adjacent to the root, then add `m` length-two paths
at each of these two vertices.  The exact increase is `4*m+1` vertices.
-/

namespace Erdos547

open SimpleGraph

variable {U : Type*}

abbrev CoatedVertex (U : Type*) (m : ℕ) := ((U ⊕ Unit) ⊕ (Fin 2 × Fin m)) ⊕ (Fin 2 × Fin m)

def coatingParent (r : U) (m : ℕ) (l : Fin 2 × Fin m) : U ⊕ Unit :=
  if l.1 = 0 then Sum.inl r else Sum.inr ()

def coatedTree (T : SimpleGraph U) (r : U) (m : ℕ) : SimpleGraph (CoatedVertex U m) :=
  attachTwoPaths (attachLeaves T (fun _ : Unit ↦ r)) (coatingParent r m)

instance coatedTree_decidableAdj (T : SimpleGraph U) [DecidableRel T.Adj] [DecidableEq U]
    (r : U) (m : ℕ) : DecidableRel (coatedTree T r m).Adj :=
  attachTwoPaths_decidableAdj _ _

def coatedTreeOldCopy (T : SimpleGraph U) (r : U) (m : ℕ) : T.Copy (coatedTree T r m) :=
  (attachTwoPathsOldCopy _ (coatingParent r m)).comp
    (attachLeavesOldCopy T (fun _ : Unit ↦ r))

theorem coatedTree_isTree [Fintype U] (T : SimpleGraph U) [DecidableRel T.Adj]
    (hT : T.IsTree) (r : U) (m : ℕ) : (coatedTree T r m).IsTree := by
  classical
  exact attachTwoPaths_isTree _ _ (attachLeaves_isTree T (fun _ : Unit ↦ r) hT)

theorem card_coatedVertex [Fintype U] (m : ℕ) :
    Fintype.card (CoatedVertex U m) = Fintype.card U + 4 * m + 1 := by
  simp only [CoatedVertex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_unit]
  omega

def coatedTreeColour {T : SimpleGraph U} (col : T.Coloring (Fin 2)) (r : U) (m : ℕ) :
    (coatedTree T r m).Coloring (Fin 2) :=
  attachTwoPathsColour (coatingParent r m) (attachLeavesColour (fun _ : Unit ↦ r) col)

@[simp] theorem coatedTreeColour_old {T : SimpleGraph U} (col : T.Coloring (Fin 2))
    (r : U) (m : ℕ) (u : U) : coatedTreeColour col r m (coatedTreeOldCopy T r m u) = col u := rfl

theorem coatedTree_dist [Fintype U] (T : SimpleGraph U) [DecidableRel T.Adj]
    (hT : T.IsTree) (r : U) (m : ℕ) (u v : U) :
    (coatedTree T r m).dist (coatedTreeOldCopy T r m u) (coatedTreeOldCopy T r m v) = T.dist u v :=
  tree_copy_dist_eq hT (coatedTree_isTree T hT r m).isAcyclic (coatedTreeOldCopy T r m) u v

end Erdos547

#print axioms Erdos547.coatedTree_isTree
#print axioms Erdos547.card_coatedVertex
