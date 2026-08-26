/- A genuine brick-wall subdivision retaining the original haven orientation. -/
import ErdosProblems.Erdos73.BrickWall
import ErdosProblems.Erdos73.SubcubicSubdivision
import ErdosProblems.Erdos73.GridColumnControl

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Erdos73Infrastructure.SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {g : ℕ}

def wallRowNails (S : GraphSubdivisionModel (elementaryWall g g) G) (r : Fin g) : Finset V :=
  (Finset.univ.filter fun w : ElementaryWallVertex g g => w.val.1 = r).image S.branchVertex

theorem branchVertex_mem_wallRowNails (S : GraphSubdivisionModel (elementaryWall g g) G)
    {w : ElementaryWallVertex g g} {r : Fin g} (hw : w.val.1 = r) :
    S.branchVertex w ∈ wallRowNails S r :=
  Finset.mem_image.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, rfl⟩

def NoWallRowNailsInHavenSmallSide {β : Finset (Finset V)} {q : ℕ}
    (h : BrambleHaven G β q) (S : GraphSubdivisionModel (elementaryWall g g) G) : Prop :=
  ∀ C D : Finset V, IsVertexSeparation G C D → (C ∩ D).card < g →
    h.PointsTo C D → ∀ r : Fin g, ¬ wallRowNails S r ⊆ C

theorem exists_wallSubdivision_anchored_in_grid (M : MinorModel (squareGrid (2 * g)) G) :
    ∃ S : GraphSubdivisionModel (elementaryWall g g) G,
      ∀ w, S.branchVertex w ∈
        M.branchSet (Fin.castLE (show g ≤ 2 * g by omega) w.val.1, w.val.2) := by
  let f := elementaryWallGridCopy (show g ≤ 2 * g by omega) (le_refl (2 * g))
  let N := (MinorModel.of_copy f).trans M
  obtain ⟨S, hS, _⟩ := exists_subdivisionModel_of_subcubic_minor N (elementaryWall_degree_le_three g g)
  refine ⟨S, fun w => ?_⟩
  obtain ⟨z, hz, hvz⟩ := (MinorModel.mem_composeBranchSet (MinorModel.of_copy f) M w _).mp (hS w)
  have hz' : z = f w := Finset.mem_singleton.mp hz
  rw [hz'] at hvz
  exact hvz

theorem noWallRowNailsInHavenSmallSide_of_anchored_grid
    {β : Finset (Finset V)} {q : ℕ} {h : BrambleHaven G β q}
    {M : MinorModel (squareGrid (2 * g)) G} (hM : NoGridRowInHavenSmallSide h M)
    (hg : 2 ≤ g) (S : GraphSubdivisionModel (elementaryWall g g) G)
    (hanchor : ∀ w, S.branchVertex w ∈
      M.branchSet (Fin.castLE (show g ≤ 2 * g by omega) w.val.1, w.val.2)) :
    NoWallRowNailsInHavenSmallSide h S := by
  intro C D hCD hsmall hpoint r
  apply hM.not_subset_smallSide_of_column_hits hCD (by omega) hsmall hpoint
  let e : Fin g ↪ Fin (2 * g) :=
    ⟨fun c => ⟨c.val + 1, by omega⟩, fun c d he => Fin.ext (by
      have hv := congrArg Fin.val he
      change c.val + 1 = d.val + 1 at hv
      omega)⟩
  apply hitsColumns_of_embedding e
  intro c
  let w := elementaryWallInteriorNail hg r c
  refine ⟨S.branchVertex w, ?_, branchVertex_mem_wallRowNails S rfl⟩
  exact (mem_gridColumnSupport M (e c) _).mpr
    ⟨Fin.castLE (show g ≤ 2 * g by omega) r, hanchor w⟩

/-- A sufficiently high-order haven controls an actual wall subdivision.
The conclusion is stronger than merely excluding whole wall rows from
small sides: their nail sets already cannot be contained there. -/
theorem BrambleHaven.exists_wallSubdivision_with_row_control
    {β : Finset (Finset V)} {q : ℕ} (h : BrambleHaven G β q)
    (g : ℕ) (hg : 2 ≤ g) (horder : controlledGridBrambleBound (2 * g) ≤ q) :
    ∃ S : GraphSubdivisionModel (elementaryWall g g) G,
      NoWallRowNailsInHavenSmallSide h S := by
  obtain ⟨M, hM⟩ := h.exists_grid_with_row_control (2 * g) horder
  obtain ⟨S, hS⟩ := exists_wallSubdivision_anchored_in_grid M
  exact ⟨S, noWallRowNailsInHavenSmallSide_of_anchored_grid hM hg S hS⟩

end
end Erdos73
