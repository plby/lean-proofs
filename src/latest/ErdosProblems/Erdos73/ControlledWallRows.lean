import ErdosProblems.Erdos73.SubdivisionConnectivity
import ErdosProblems.Erdos73.WallGridAnchors

/-! Disjoint connected interior rows, each retaining original-grid haven control. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

def interiorWallRowCopy {g : ℕ} (hg : 2 ≤ g) (r : Fin g) :
    (pathGraph g).Copy (elementaryWall g g) where
  toHom := {
    toFun := elementaryWallInteriorNail hg r
    map_rel' := by
      intro i j hij
      refine Or.inl ⟨rfl, pathGraph_adj.mpr ?_⟩
      have hh := pathGraph_adj.mp hij
      change i.val + 1 + 1 = j.val + 1 ∨ j.val + 1 + 1 = i.val + 1
      omega }
  injective' := by
    intro i j he
    apply Fin.ext
    have hh := congrArg (fun w : ElementaryWallVertex g g => w.val.2.val) he
    change i.val + 1 = j.val + 1 at hh
    omega

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {g : ℕ}

def interiorWallRowSupport (S : GraphSubdivisionModel (elementaryWall g g) G)
    (hg : 2 ≤ g) (r : Fin g) : Finset V := (S.restrictCopy (interiorWallRowCopy hg r)).vertexSet

theorem interiorNail_mem_rowSupport (S : GraphSubdivisionModel (elementaryWall g g) G)
    (hg : 2 ≤ g) (r i : Fin g) :
    S.branchVertex (elementaryWallInteriorNail hg r i) ∈ interiorWallRowSupport S hg r :=
  (S.restrictCopy (interiorWallRowCopy hg r)).branch_mem_supportOver (Finset.mem_univ i)

theorem interiorWallRowSupport_connected (S : GraphSubdivisionModel (elementaryWall g g) G)
    (hg : 2 ≤ g) (r : Fin g) :
    (G.induce (interiorWallRowSupport S hg r : Set V)).Connected := by
  apply (S.restrictCopy (interiorWallRowCopy hg r)).connected_supportOver
  have : NeZero g := ⟨by omega⟩
  have heq : ((Finset.univ : Finset (Fin g)) : Set (Fin g)) = Set.univ := by
    ext i
    exact iff_true_intro (Finset.mem_univ i)
  rw [heq]
  exact ((pathGraph g).induceUnivIso.connected_iff).mpr ⟨pathGraph_preconnected g⟩

theorem interiorWallRowSupport_disjoint (S : GraphSubdivisionModel (elementaryWall g g) G)
    (hg : 2 ≤ g) : Pairwise (fun r s =>
      Disjoint (interiorWallRowSupport S hg r) (interiorWallRowSupport S hg s)) := by
  intro r s hrs
  apply S.restrictCopy_vertexSet_disjoint
  apply Finset.disjoint_left.mpr
  intro w hwR hwS
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hwR
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hwS
  have he := congrArg (fun w : ElementaryWallVertex g g => w.val.1) (hi.trans hj.symm)
  exact hrs he

theorem WallGridAnchor.interiorRow_not_subset_smallSide {n : ℕ}
    {M : MinorModel (squareGrid n) G} {S : GraphSubdivisionModel (elementaryWall g g) G}
    (A : WallGridAnchor M S) {β : Finset (Finset V)} {q : ℕ} {h : BrambleHaven G β q}
    (hM : NoGridRowInHavenSmallSide h M) (hg : 2 ≤ g)
    {C D : Finset V} (hCD : IsVertexSeparation G C D) (hsmall : (C ∩ D).card < g)
    (hpoint : h.PointsTo C D) (r : Fin g) : ¬ interiorWallRowSupport S hg r ⊆ C := by
  have hgn : 2 * g ≤ n := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding A.column
  apply hM.not_subset_smallSide_of_column_hits hCD (by omega) hsmall hpoint
  let e : Fin g ↪ Fin (2 * g) :=
    ⟨fun i => ⟨i.val + 1, by omega⟩, fun i j he => Fin.ext (by
      have hh := congrArg Fin.val he
      change i.val + 1 = j.val + 1 at hh
      omega)⟩
  apply hitsColumns_of_embedding (e.trans A.column)
  intro i
  refine ⟨S.branchVertex (elementaryWallInteriorNail hg r i), ?_, interiorNail_mem_rowSupport S hg r i⟩
  exact (mem_gridColumnSupport M (A.column (e i)) _).mpr
    ⟨A.row r, A.branch_mem (elementaryWallInteriorNail hg r i)⟩

end
end Erdos73
