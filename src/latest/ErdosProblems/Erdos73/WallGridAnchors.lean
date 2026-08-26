import ErdosProblems.Erdos73.ControlledWall
import ErdosProblems.Erdos73.RegularSubwalls
import ErdosProblems.Erdos73.SubdivisionRestriction

/-! Original-grid anchors survive regular subwall restriction and retain haven control. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {n c r : ℕ}

structure WallGridAnchor (M : MinorModel (squareGrid n) G)
    (S : GraphSubdivisionModel (elementaryWall c r) G) where
  row : Fin r → Fin n
  column : Fin (2 * c) ↪ Fin n
  branch_mem : ∀ w, S.branchVertex w ∈ M.branchSet (row w.val.1, column w.val.2)

theorem exists_wallSubdivision_with_gridAnchor {g : ℕ} (M : MinorModel (squareGrid (2 * g)) G) :
    ∃ S : GraphSubdivisionModel (elementaryWall g g) G, Nonempty (WallGridAnchor M S) := by
  obtain ⟨S, hS⟩ := exists_wallSubdivision_anchored_in_grid M
  exact ⟨S, ⟨⟨Fin.castLE (show g ≤ 2 * g by omega), Function.Embedding.refl _, hS⟩⟩⟩

namespace WallGridAnchor

def restrictOffsets {C R : ℕ} {M : MinorModel (squareGrid n) G}
    {S : GraphSubdivisionModel (elementaryWall C R) G} (A : WallGridAnchor M S)
    (a b : ℕ) (hr : 2 * a + r ≤ R) (hc : b + c ≤ C) :
    WallGridAnchor M (S.restrictCopy (elementaryWallCopyOfOffsets a b hr hc)) where
  row i := A.row ⟨2 * a + i.val, by have hi := i.isLt; omega⟩
  column := (show Fin (2 * c) ↪ Fin (2 * C) from
    ⟨fun j => ⟨2 * b + j.val, by have hj := j.isLt; omega⟩, fun j k he => Fin.ext (by
      have hh := congrArg Fin.val he
      change 2 * b + j.val = 2 * b + k.val at hh
      omega)⟩).trans A.column
  branch_mem w := A.branch_mem (elementaryWallCopyOfOffsets a b hr hc w)

theorem no_row_nails_in_smallSide {g : ℕ} {M : MinorModel (squareGrid n) G}
    {S : GraphSubdivisionModel (elementaryWall g g) G} (A : WallGridAnchor M S)
    {β : Finset (Finset V)} {q : ℕ} {h : BrambleHaven G β q}
    (hM : NoGridRowInHavenSmallSide h M) (hg : 2 ≤ g) :
    NoWallRowNailsInHavenSmallSide h S := by
  have hgn : 2 * g ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding A.column
  intro C D hCD hsmall hpoint row
  apply hM.not_subset_smallSide_of_column_hits hCD (by omega) hsmall hpoint
  let e : Fin g ↪ Fin (2 * g) :=
    ⟨fun i => ⟨i.val + 1, by omega⟩, fun i j he => Fin.ext (by
      have hh := congrArg Fin.val he
      change i.val + 1 = j.val + 1 at hh
      omega)⟩
  apply hitsColumns_of_embedding (e.trans A.column)
  intro i
  let w := elementaryWallInteriorNail hg row i
  refine ⟨S.branchVertex w, ?_, branchVertex_mem_wallRowNails S rfl⟩
  exact (mem_gridColumnSupport M (A.column (e i)) _).mpr ⟨A.row row, A.branch_mem w⟩

end WallGridAnchor
end
end Erdos73
