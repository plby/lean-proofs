import ErdosProblems.Erdos73.SubdivisionTreeRegions
import ErdosProblems.Erdos73.PathCutParity

/-! Split each long subdivision corridor at its first internal vertex, retaining exact incidences. -/

namespace Erdos73.GraphSubdivisionModel
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {W V : Type*} [Fintype W] [LinearOrder W] [Fintype V]
variable {H : SimpleGraph W} {G : SimpleGraph V} (S : GraphSubdivisionModel H G)

theorem edgePath_length_pos (e : OrientedEdge H) : 0 < (S.edgePath e).walk.length := by
  by_contra hn
  have hh := Walk.eq_of_length_eq_zero (show (S.edgePath e).walk.length = 0 by omega)
  have he : S.branchVertex e.lo = S.branchVertex e.hi :=
    (S.source_eq e).symm.trans (hh.trans (S.target_eq e))
  exact (ne_of_lt e.lo_lt_hi) (S.injective he)

theorem edgePath_length_two_le_of_even (h : ∀ e, Even (S.edgePath e).walk.length)
    (e : OrientedEdge H) : 2 ≤ (S.edgePath e).walk.length := by
  have hp := S.edgePath_length_pos e
  have he := h e
  rw [Nat.even_iff] at he
  omega

def firstInternal (e : OrientedEdge H) : V := (S.edgePath e).walk.getVert 1

theorem firstInternal_mem (e : OrientedEdge H) : S.firstInternal e ∈ (S.edgePath e).vertexSet :=
  List.mem_toFinset.mpr ((S.edgePath e).walk.getVert_mem_support 1)

theorem firstInternal_not_branch (hlong : ∀ e, 2 ≤ (S.edgePath e).walk.length)
    (e : OrientedEdge H) (w : W) : S.firstInternal e ≠ S.branchVertex w := by
  intro he
  have hi := hlong e
  rcases S.branch_on_path e w (he ▸ S.firstInternal_mem e) with hw | hw
  · have hh : (S.edgePath e).walk.getVert 1 = (S.edgePath e).source :=
      he.trans ((congrArg S.branchVertex hw).trans (S.source_eq e).symm)
    have hz := ((S.edgePath e).isPath.getVert_eq_start_iff (by omega)).mp hh
    omega
  · have hh : (S.edgePath e).walk.getVert 1 = (S.edgePath e).target :=
      he.trans ((congrArg S.branchVertex hw).trans (S.target_eq e).symm)
    have hz := ((S.edgePath e).isPath.getVert_eq_end_iff (by omega)).mp hh
    omega

theorem firstInternal_injective (hlong : ∀ e, 2 ≤ (S.edgePath e).walk.length) :
    Function.Injective S.firstInternal := by
  intro e f he
  by_contra hef
  have hf : S.firstInternal e ∈ (S.edgePath f).vertexSet := he ▸ S.firstInternal_mem f
  obtain ⟨w, hw, _, _⟩ := S.intersection hef _ (S.firstInternal_mem e) hf
  exact S.firstInternal_not_branch hlong e w hw

def halfPath (e : OrientedEdge H) (side : Bool) : GraphPath G :=
  if side then ((S.edgePath e).dropUntil (S.firstInternal_mem e)).reverse
  else (S.edgePath e).takeUntil (S.firstInternal_mem e)

def halfEndpoint (e : OrientedEdge H) (side : Bool) : W := if side then e.hi else e.lo

theorem halfPath_source (e : OrientedEdge H) (side : Bool) :
    (S.halfPath e side).source = S.branchVertex (halfEndpoint e side) := by
  cases side <;> simp only [halfPath, halfEndpoint, Bool.false_eq_true, ↓reduceIte,
    GraphPath.reverse_source, GraphPath.takeUntil_source, GraphPath.dropUntil_target,
    S.source_eq, S.target_eq]

theorem halfPath_target (e : OrientedEdge H) (side : Bool) :
    (S.halfPath e side).target = S.firstInternal e := by
  cases side <;> simp only [halfPath, Bool.false_eq_true, ↓reduceIte,
    GraphPath.reverse_target, GraphPath.takeUntil_target, GraphPath.dropUntil_source]

theorem halfPath_subset (e : OrientedEdge H) (side : Bool) :
    (S.halfPath e side).vertexSet ⊆ (S.edgePath e).vertexSet := by
  cases side
  · exact (S.edgePath e).takeUntil_vertexSet_subset (S.firstInternal_mem e)
  · simpa only [halfPath, ↓reduceIte, GraphPath.reverse_vertexSet] using
      (S.edgePath e).dropUntil_vertexSet_subset (S.firstInternal_mem e)

theorem halfPaths_intersection (e : OrientedEdge H) {side side' : Bool} (hne : side ≠ side')
    {x : V} (hx : x ∈ (S.halfPath e side).vertexSet) (hx' : x ∈ (S.halfPath e side').vertexSet) :
    x = S.firstInternal e := by
  cases side <;> cases side' <;> try contradiction
  · exact Erdos73.GraphPath.takeUntil_dropUntil_intersection (S.edgePath e) (S.firstInternal_mem e)
      hx (by simpa only [halfPath, ↓reduceIte, GraphPath.reverse_vertexSet] using hx')
  · exact Erdos73.GraphPath.takeUntil_dropUntil_intersection (S.edgePath e) (S.firstInternal_mem e)
      hx' (by simpa only [halfPath, ↓reduceIte, GraphPath.reverse_vertexSet] using hx)

theorem branch_on_halfPath (hlong : ∀ e, 2 ≤ (S.edgePath e).walk.length)
    (e : OrientedEdge H) (side : Bool) (w : W) (hw : S.branchVertex w ∈ (S.halfPath e side).vertexSet) :
    w = halfEndpoint e side := by
  have he := S.branch_on_path e w (S.halfPath_subset e side hw)
  cases side
  · rcases he with he | he
    · exact he
    · have hother : S.branchVertex w ∈ (S.halfPath e true).vertexSet := by
        have hs := S.halfPath_source e true
        simp only [halfEndpoint, if_pos rfl, ite_true] at hs
        rw [he, ← hs]
        exact (S.halfPath e true).source_mem_vertexSet
      have hh := S.halfPaths_intersection e (by decide : false ≠ true) hw hother
      exact (S.firstInternal_not_branch hlong e w hh.symm).elim
  · rcases he with he | he
    · have hother : S.branchVertex w ∈ (S.halfPath e false).vertexSet := by
        have hs := S.halfPath_source e false
        simp only [halfEndpoint, Bool.false_eq_true, if_false] at hs
        rw [he, ← hs]
        exact (S.halfPath e false).source_mem_vertexSet
      have hh := S.halfPaths_intersection e (by decide : true ≠ false) hw hother
      exact (S.firstInternal_not_branch hlong e w hh.symm).elim
    · exact he

theorem firstInternal_on_halfPath (hlong : ∀ e, 2 ≤ (S.edgePath e).walk.length)
    (e f : OrientedEdge H) (side : Bool)
    (hf : S.firstInternal f ∈ (S.halfPath e side).vertexSet) : f = e := by
  by_contra hne
  obtain ⟨w, hw, _, _⟩ := S.intersection hne _ (S.firstInternal_mem f) (S.halfPath_subset e side hf)
  exact S.firstInternal_not_branch hlong f w hw

theorem halfPath_odd (heven : ∀ e, Even (S.edgePath e).walk.length)
    (e : OrientedEdge H) (side : Bool) : Odd (S.halfPath e side).walk.length := by
  have hp := S.edgePath_length_pos e
  have hh := Erdos73.GraphPath.odd_parts_of_even_path_odd_cut (S.edgePath e) (S.firstInternal_mem e)
    (show 1 ≤ (S.edgePath e).walk.length by omega) rfl (heven e) (by decide : Odd 1)
  cases side
  · exact hh.1
  · rw [halfPath, if_pos rfl]
    change Odd (((S.edgePath e).dropUntil (S.firstInternal_mem e)).walk.reverse.length)
    rw [_root_.SimpleGraph.Walk.length_reverse]
    exact hh.2

end
end Erdos73.GraphSubdivisionModel
