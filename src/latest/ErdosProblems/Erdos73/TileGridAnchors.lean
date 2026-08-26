import ErdosProblems.Erdos73.MonochromaticTileSelection
import ErdosProblems.Erdos73.SubdivisionModelComposition
import ErdosProblems.Erdos73.WallGridAnchors
import ErdosProblems.Erdos73.ParityGraphTransport

/-! Monochromatic tiled subwalls retain their original grid-minor anchor and host colouring. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

namespace BrickTileArray

variable {c r C R : ℕ} (A : BrickTileArray c r C R)

def rowIndex (i : Fin r) : Fin R :=
  ⟨12 * A.row i + 4, by have hh := A.row_bound i; omega⟩

def columnEmbedding : Fin (2 * c) ↪ Fin (2 * C) where
  toFun j := ⟨16 * A.column j + 6, by have hh := A.column_bound j; omega⟩
  inj' := by
    intro i j he
    have hh := congrArg Fin.val he
    change 16 * A.column i + 6 = 16 * A.column j + 6 at hh
    exact A.column_strictMono.injective (by omega)

theorem point_rowIndex (z : Fin r × Fin (2 * c)) :
    (A.point z).val.1 = A.rowIndex z.1 := Fin.ext (A.point_row z)

theorem point_columnEmbedding (z : Fin r × Fin (2 * c)) :
    (A.point z).val.2 = A.columnEmbedding z.2 := Fin.ext (A.point_column z)

end BrickTileArray

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {n C R : ℕ}
variable {M : MinorModel (squareGrid n) G}
variable {S : GraphSubdivisionModel (elementaryWall C R) G}

def WallGridAnchor.tile (B : WallGridAnchor M S) {c r : ℕ} (A : BrickTileArray c r C R) :
    WallGridAnchor M (S.compose A.toSubdivisionModel) where
  row := B.row ∘ A.rowIndex
  column := A.columnEmbedding.trans B.column
  branch_mem := by
    intro w
    change S.branchVertex (A.point w.val) ∈
      M.branchSet (B.row (A.rowIndex w.val.1), B.column (A.columnEmbedding w.val.2))
    simpa only [A.point_rowIndex, A.point_columnEmbedding] using B.branch_mem (A.point w.val)

theorem WallGridAnchor.exists_monochromatic_subwall (B : WallGridAnchor M S)
    (col : BipartiteColoringOn G S.vertexSet) (c r : ℕ)
    (hc : 32 * c ≤ C) (hr : 12 * (2 ^ (4 * c) * r) ≤ R) :
    ∃ S' : GraphSubdivisionModel (elementaryWall c r) G,
      Nonempty (WallGridAnchor M S') ∧ S'.vertexSet ⊆ S.vertexSet ∧
      ∃ col' : BipartiteColoringOn G S'.vertexSet, col'.color = col.color ∧
        ∃ b : Bool, ∀ w, col'.color (S'.branchVertex w) = b := by
  obtain ⟨A, b, hb⟩ := exists_monochromatic_tileArray
    (fun w => col.color (S.branchVertex w)) c r hc hr
  let T := S.compose A.toSubdivisionModel
  have hT : T.vertexSet ⊆ S.vertexSet := S.compose_vertexSet_subset A.toSubdivisionModel
  refine ⟨T, ⟨B.tile A⟩, hT, col.mono_support hT, rfl, b, ?_⟩
  intro w
  exact hb w.val

end
end Erdos73
