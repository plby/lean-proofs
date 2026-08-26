import ErdosProblems.Erdos73.BrickWall
import ErdosProblems.Erdos73.FiniteSequencePath
import ErdosProblems.Erdos73.SubdivisionPaths
import ErdosProblems.Erdos73.SubdivisionAnchors

/-! Explicit horizontal intervals, including retained boundary vertices. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {c r : ℕ}

def brickRowVertices (b : Fin r) : Finset (ElementaryWallVertex c r) :=
  univ.filter (fun w => w.val.1 = b)

theorem brickRowVertices_disjoint {a b : Fin r} (hab : a ≠ b) :
    Disjoint (brickRowVertices (c := c) a) (brickRowVertices b) := by
  apply Finset.disjoint_left.mpr
  intro w hwa hwb
  exact hab ((mem_filter.mp hwa).2.symm.trans (mem_filter.mp hwb).2)

def brickHorizontalVertex (u v : ElementaryWallVertex c r) (hrow : u.val.1 = v.val.1)
    (huv : u.val.2.val ≤ v.val.2.val) (i : Fin (v.val.2.val - u.val.2.val + 1)) :
    ElementaryWallVertex c r := by
  let x : Fin r × Fin (2 * c) := (u.val.1, ⟨u.val.2.val + i.val, by
    have hv := v.val.2.isLt
    have hi := i.isLt
    omega⟩)
  refine ⟨x, ?_⟩
  by_cases hxu : x = u.val
  · exact hxu ▸ u.property
  by_cases hxv : x = v.val
  · exact hxv ▸ v.property
  apply rawBrickWall_degree_ge_two_of_interior x
  · have hcol : u.val.2.val + i.val ≠ u.val.2.val := by
      intro he
      exact hxu (Prod.ext rfl (Fin.ext he))
    change 0 < u.val.2.val + i.val
    omega
  · have hcol : u.val.2.val + i.val ≠ v.val.2.val := by
      intro he
      exact hxv (Prod.ext hrow (Fin.ext he))
    have hv := v.val.2.isLt
    have hi := i.isLt
    change u.val.2.val + i.val + 1 < 2 * c
    omega

theorem brickHorizontalVertex_injective (u v : ElementaryWallVertex c r) (hrow huv) :
    Function.Injective (brickHorizontalVertex u v hrow huv) := by
  intro i j he
  have hh := congrArg (fun w : ElementaryWallVertex c r => w.val.2.val) he
  change u.val.2.val + i.val = u.val.2.val + j.val at hh
  exact Fin.ext (by omega)

theorem brickHorizontalVertex_adj (u v : ElementaryWallVertex c r) (hrow huv)
    (i : ℕ) (hi : i + 1 < v.val.2.val - u.val.2.val + 1) :
    (elementaryWall c r).Adj
      (brickHorizontalVertex u v hrow huv ⟨i, by omega⟩)
      (brickHorizontalVertex u v hrow huv ⟨i + 1, hi⟩) := by
  apply Or.inl
  refine ⟨rfl, pathGraph_adj.mpr (Or.inl ?_)⟩
  change u.val.2.val + i + 1 = u.val.2.val + (i + 1)
  omega

theorem exists_brick_horizontal_interval_path_of_le (u v : ElementaryWallVertex c r)
    (hrow : u.val.1 = v.val.1) (huv : u.val.2.val ≤ v.val.2.val) :
    ∃ P : GraphPath (elementaryWall c r), P.source = u ∧ P.target = v ∧
      (∀ w ∈ P.vertexSet, w.val.1 = u.val.1 ∧
        u.val.2.val ≤ w.val.2.val ∧ w.val.2.val ≤ v.val.2.val) := by
  let f := brickHorizontalVertex u v hrow huv
  let hf := brickHorizontalVertex_injective u v hrow huv
  let ha := brickHorizontalVertex_adj u v hrow huv
  let P := GraphPath.ofSequence f hf ha
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [GraphPath.ofSequence_source]
    apply Subtype.ext
    exact Prod.ext rfl (Fin.ext (by change u.val.2.val + 0 = u.val.2.val; omega))
  · rw [GraphPath.ofSequence_target]
    apply Subtype.ext
    exact Prod.ext hrow (Fin.ext (by
      change u.val.2.val + (v.val.2.val - u.val.2.val) = v.val.2.val
      omega))
  · intro w hw
    obtain ⟨i, rfl⟩ := (GraphPath.mem_ofSequence_vertexSet f hf ha w).mp hw
    refine ⟨rfl, ?_, ?_⟩
    · change u.val.2.val ≤ u.val.2.val + i.val
      omega
    · have hi := i.isLt
      change u.val.2.val + i.val ≤ v.val.2.val
      omega

theorem exists_brick_horizontal_path_bounded (u v : ElementaryWallVertex c r)
    (hrow : u.val.1 = v.val.1) (l h : ℕ)
    (hu : l ≤ u.val.2.val ∧ u.val.2.val ≤ h)
    (hv : l ≤ v.val.2.val ∧ v.val.2.val ≤ h) :
    ∃ P : GraphPath (elementaryWall c r), P.source = u ∧ P.target = v ∧
      (∀ w ∈ P.vertexSet, w.val.1 = u.val.1 ∧ l ≤ w.val.2.val ∧ w.val.2.val ≤ h) := by
  by_cases huv : u.val.2.val ≤ v.val.2.val
  · obtain ⟨P, hs, ht, hP⟩ := exists_brick_horizontal_interval_path_of_le u v hrow huv
    exact ⟨P, hs, ht, fun w hw => ⟨(hP w hw).1,
      hu.1.trans (hP w hw).2.1, (hP w hw).2.2.trans hv.2⟩⟩
  obtain ⟨P, hs, ht, hP⟩ :=
    exists_brick_horizontal_interval_path_of_le v u hrow.symm (by omega)
  refine ⟨P.reverse, ht, hs, ?_⟩
  intro w hw
  rw [GraphPath.reverse_vertexSet] at hw
  exact ⟨(hP w hw).1.trans hrow.symm, hv.1.trans (hP w hw).2.1,
    (hP w hw).2.2.trans hu.2⟩

theorem exists_brick_horizontal_path_of_le (u v : ElementaryWallVertex c r)
    (hrow : u.val.1 = v.val.1) (huv : u.val.2.val ≤ v.val.2.val) :
    ∃ P : GraphPath (elementaryWall c r), P.source = u ∧ P.target = v ∧
      P.vertexSet ⊆ brickRowVertices u.val.1 := by
  obtain ⟨P, hs, ht, hP⟩ := exists_brick_horizontal_interval_path_of_le u v hrow huv
  exact ⟨P, hs, ht, fun w hw => mem_filter.mpr ⟨mem_univ _, (hP w hw).1⟩⟩

theorem exists_brick_horizontal_path (u v : ElementaryWallVertex c r)
    (hrow : u.val.1 = v.val.1) :
    ∃ P : GraphPath (elementaryWall c r), P.source = u ∧ P.target = v ∧
      P.vertexSet ⊆ brickRowVertices u.val.1 := by
  by_cases huv : u.val.2.val ≤ v.val.2.val
  · exact exists_brick_horizontal_path_of_le u v hrow huv
  obtain ⟨P, hs, ht, hP⟩ := exists_brick_horizontal_path_of_le v u hrow.symm (by omega)
  exact ⟨P.reverse, ht, hs, by simpa only [GraphPath.reverse_vertexSet, hrow] using hP⟩

theorem GraphSubdivisionModel.exists_horizontal_path {V : Type*} {G : SimpleGraph V}
    (S : GraphSubdivisionModel (elementaryWall c r) G) (u v : ElementaryWallVertex c r)
    (hrow : u.val.1 = v.val.1) :
    ∃ P : GraphPath G, P.source = S.branchVertex u ∧ P.target = S.branchVertex v ∧
      P.vertexSet ⊆ S.supportOver (brickRowVertices u.val.1) := by
  obtain ⟨Q, hs, ht, hQ⟩ := exists_brick_horizontal_path u v hrow
  obtain ⟨P, hPs, hPt, hP⟩ := S.exists_path_with_walkSupport Q.walk Q.isPath
  refine ⟨P, hPs.trans (congrArg S.branchVertex hs), hPt.trans (congrArg S.branchVertex ht), ?_⟩
  rw [hP]
  apply (S.walkSupport_subset_supportOver Q.walk).trans (S.supportOver_mono ?_)
  simpa only [GraphPath.vertexSet, Finset.subset_iff, List.mem_toFinset] using hQ

end
end Erdos73
