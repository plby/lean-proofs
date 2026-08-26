import ErdosProblems.Erdos547.GlueCopies
import ErdosProblems.Erdos547.ShrubRoots

/-!
# Extending a partial copy by a whole shrub
-/

namespace Erdos547.FineTreePartition

open Finset SimpleGraph

variable {U V : Type*} [Fintype U] [DecidableEq U] {T : SimpleGraph U}
  [DecidableRel T.Adj] {r : U} {ℓ : ℕ} {col : T.Coloring (Fin 2)}

theorem extend_copy_by_shrub (P : FineTreePartition T r ℓ col) (G : SimpleGraph V)
    (A S : Finset U) (hWA : P.seeds ⊆ A) (hS : S ∈ P.shrubs) (hAS : Disjoint A S)
    (D : ShrubRootData T P.seeds S)
    (f : (T.induce (A : Set U)).Copy G) (g : (T.induce (S : Set U)).Copy G)
    (himages : ∀ x : ↥A, ∀ y : ↥S, f x ≠ g y)
    (hprimary : G.Adj (f ⟨D.seed.val, hWA D.seed.property⟩) (g D.root))
    (hsecondary : ∀ z, D.second = some z →
      G.Adj (f ⟨z.1.val, hWA z.1.property⟩) (g z.2)) :
    ∃ h : (T.induce ((A ∪ S : Finset U) : Set U)).Copy G,
      (∀ x : ↥A, h ⟨x.val, Finset.mem_union_left S x.property⟩ = f x) ∧
      (∀ y : ↥S, h ⟨y.val, Finset.mem_union_right A y.property⟩ = g y) := by
  apply glue_copies T G A S hAS f g himages
  intro x y hxy
  have hxW : x.val ∈ P.seeds :=
    (P.edge_exit S hS y.val y.property x.val hxy.symm).resolve_left
      (fun hxS ↦ Finset.disjoint_left.mp hAS x.property hxS)
  let z : ↥P.seeds := ⟨x.val, hxW⟩
  rcases D.attachments z y hxy with ⟨hz, hy⟩ | hsecond
  · have hval : x.val = D.seed.val := congrArg Subtype.val hz
    have hfx : f x = f ⟨D.seed.val, hWA D.seed.property⟩ :=
      congrArg f (Subtype.ext hval)
    rw [hfx, hy]
    exact hprimary
  · exact hsecondary (z, y) hsecond

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.extend_copy_by_shrub
