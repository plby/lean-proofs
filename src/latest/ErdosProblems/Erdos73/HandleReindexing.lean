import ErdosProblems.Erdos73.ColumnHandleFamilies
import ErdosProblems.Erdos73.ParityGraphTransport

/-! Reindex and orient actual handle families without changing their supports. -/

namespace Erdos73.ColumnHandleFamily
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {V I J : Type*} {G : SimpleGraph V} {c r : ℕ}
variable {S : GraphSubdivisionModel (elementaryWall c r) G}
variable {col : BipartiteColoringOn G S.vertexSet}

def reindex (F : ColumnHandleFamily S col I) (f : J → I) (hf : Function.Injective f) :
    ColumnHandleFamily S col J where
  path := F.path ∘ f
  clean := fun j => F.clean (f j)
  disjoint := fun _ _ hij => F.disjoint (hf.ne hij)
  sourceNail := F.sourceNail ∘ f
  targetNail := F.targetNail ∘ f
  source_eq := fun j => F.source_eq (f j)
  target_eq := fun j => F.target_eq (f j)
  source_boundary := fun j => F.source_boundary (f j)
  target_boundary := fun j => F.target_boundary (f j)

def reverseWhere (F : ColumnHandleFamily S col I) (flip : I → Bool) :
    ColumnHandleFamily S col I where
  path := fun i => if flip i then (F.path i).reverse else F.path i
  clean := fun i => by
    split_ifs
    · exact (F.clean i).reverse
    · exact F.clean i
  disjoint := by
    intro i j hij
    split_ifs <;> simpa only [GraphPath.reverse_vertexSet] using F.disjoint hij
  sourceNail := fun i => if flip i then F.targetNail i else F.sourceNail i
  targetNail := fun i => if flip i then F.sourceNail i else F.targetNail i
  source_eq := fun i => by
    split_ifs
    · exact F.target_eq i
    · exact F.source_eq i
  target_eq := fun i => by
    split_ifs
    · exact F.source_eq i
    · exact F.target_eq i
  source_boundary := fun i => by
    split_ifs
    · exact F.target_boundary i
    · exact F.source_boundary i
  target_boundary := fun i => by
    split_ifs
    · exact F.source_boundary i
    · exact F.target_boundary i

theorem reverseWhere_vertexSet (F : ColumnHandleFamily S col I) (flip : I → Bool) (i : I) :
    ((F.reverseWhere flip).path i).vertexSet = (F.path i).vertexSet := by
  dsimp only [reverseWhere]
  split_ifs <;> simp only [GraphPath.reverse_vertexSet]

def orientByRow (F : ColumnHandleFamily S col I) : ColumnHandleFamily S col I :=
  F.reverseWhere (fun i => decide ((F.targetNail i).val.1.val < (F.sourceNail i).val.1.val))

theorem orientByRow_ordered (F : ColumnHandleFamily S col I) (i : I) :
    (F.orientByRow.sourceNail i).val.1.val ≤ (F.orientByRow.targetNail i).val.1.val := by
  dsimp only [orientByRow, reverseWhere]
  split_ifs with hh <;> simp only [decide_eq_true_eq] at hh <;> omega

end
end Erdos73.ColumnHandleFamily
