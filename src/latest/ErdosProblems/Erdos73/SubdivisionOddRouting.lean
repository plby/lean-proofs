import ErdosProblems.Erdos73.SubcubicSubdivision

/-! Actual subdivision models with odd corridors yield the explicit odd-subdivision copy. -/

namespace Erdos73.GraphSubdivisionModel
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {W V : Type*} [Fintype W] [LinearOrder W] [Fintype V]
variable {H : SimpleGraph W} {G : SimpleGraph V}
variable (S : GraphSubdivisionModel H G) (t : OrientedEdge H → ℕ)
variable (hlen : ∀ e, (S.edgePath e).walk.length = 2 * t e + 1)

def oddRoutingVertex : OddSubdivisionVertex H t → V
  | Sum.inl w => S.branchVertex w
  | Sum.inr ⟨e, i⟩ => (S.edgePath e).walk.getVert (i.val + 1)

include hlen in
theorem internal_getVert_not_branch (e : OrientedEdge H) (i : Fin (2 * t e)) (w : W) :
    (S.edgePath e).walk.getVert (i.val + 1) ≠ S.branchVertex w := by
  intro he
  have hi : i.val + 1 < (S.edgePath e).walk.length := by
    rw [hlen]
    have hh := i.isLt
    omega
  have hm : (S.edgePath e).walk.getVert (i.val + 1) ∈ (S.edgePath e).vertexSet :=
    List.mem_toFinset.mpr ((S.edgePath e).walk.getVert_mem_support _)
  rcases S.branch_on_path e w (he ▸ hm) with hw | hw
  · have hs := he.trans ((congrArg S.branchVertex hw).trans (S.source_eq e).symm)
    have hz := (S.edgePath e).isPath.getVert_eq_start_iff hi.le |>.mp hs
    omega
  · have ht := he.trans ((congrArg S.branchVertex hw).trans (S.target_eq e).symm)
    have hz := (S.edgePath e).isPath.getVert_eq_end_iff hi.le |>.mp ht
    omega

include hlen in
theorem oddRoutingVertex_injective : Function.Injective (S.oddRoutingVertex t) := by
  intro x y he
  cases x with
  | inl w =>
    cases y with
    | inl z => exact congrArg Sum.inl (S.injective he)
    | inr a =>
      rcases a with ⟨e, i⟩
      exact (S.internal_getVert_not_branch t hlen e i w he.symm).elim
  | inr a =>
    rcases a with ⟨e, i⟩
    cases y with
    | inl w => exact (S.internal_getVert_not_branch t hlen e i w he).elim
    | inr b =>
      rcases b with ⟨f, j⟩
      have hi : i.val + 1 ≤ (S.edgePath e).walk.length := by
        rw [hlen]; have hh := i.isLt; omega
      have hj : j.val + 1 ≤ (S.edgePath f).walk.length := by
        rw [hlen]; have hh := j.isLt; omega
      by_cases hef : e = f
      · subst f
        have hij := (S.edgePath e).isPath.getVert_injOn hi hj he
        have hij' : i = j := Fin.ext (by omega)
        subst j
        rfl
      · have hxe : (S.edgePath e).walk.getVert (i.val + 1) ∈ (S.edgePath e).vertexSet :=
          List.mem_toFinset.mpr ((S.edgePath e).walk.getVert_mem_support _)
        have hxf : (S.edgePath e).walk.getVert (i.val + 1) ∈ (S.edgePath f).vertexSet := by
          change (S.edgePath e).walk.getVert (i.val + 1) =
            (S.edgePath f).walk.getVert (j.val + 1) at he
          rw [he]
          exact List.mem_toFinset.mpr ((S.edgePath f).walk.getVert_mem_support _)
        obtain ⟨w, hw, _, _⟩ := S.intersection hef _ hxe hxf
        exact (S.internal_getVert_not_branch t hlen e i w hw).elim

include hlen in
theorem oddRoutingVertex_path (e : OrientedEdge H) (i : Fin (2 * t e + 2)) :
    S.oddRoutingVertex t (oddSubdivisionPathVertex t e i) = (S.edgePath e).walk.getVert i.val := by
  induction i using Fin.cases with
  | zero =>
    simp only [oddSubdivisionPathVertex_zero, oddRoutingVertex, Fin.val_zero, Walk.getVert_zero]
    exact (S.source_eq e).symm
  | succ i =>
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, oddSubdivisionPathVertex_last]
      change S.branchVertex e.hi = (S.edgePath e).walk.getVert (2 * t e + 1)
      rw [← hlen, Walk.getVert_length]
      exact (S.target_eq e).symm
    | cast i =>
      rw [oddSubdivisionPathVertex_internal]
      rfl

def toOddSubdivisionRoutingOfLengths : OddSubdivisionRouting H G where
  t := t
  vertex := S.oddRoutingVertex t
  vertex_injective := S.oddRoutingVertex_injective t hlen
  map_path_adj := by
    intro e i j hij
    rw [S.oddRoutingVertex_path t hlen, S.oddRoutingVertex_path t hlen]
    rcases pathGraph_adj.mp hij with hij | hij
    · have hi : i.val < (S.edgePath e).walk.length := by
        rw [hlen]; have hj := j.isLt; omega
      simpa only [hij] using (S.edgePath e).walk.adj_getVert_succ hi
    · have hj : j.val < (S.edgePath e).walk.length := by
        rw [hlen]; have hi := i.isLt; omega
      simpa only [hij] using ((S.edgePath e).walk.adj_getVert_succ hj).symm

theorem exists_oddSubdivisionRouting (hodd : ∀ e, Odd (S.edgePath e).walk.length) :
    Nonempty (OddSubdivisionRouting H G) := by
  have hex (e : OrientedEdge H) : ∃ s, (S.edgePath e).walk.length = 2 * s + 1 := by
    obtain ⟨s, hs⟩ := hodd e
    exact ⟨s, by omega⟩
  choose s hs using hex
  exact ⟨S.toOddSubdivisionRoutingOfLengths s hs⟩

theorem hasIndependenceDefectAtLeast_of_odd
    (hodd : ∀ e, Odd (S.edgePath e).walk.length) (r : ℕ)
    (hH : 2 * H.indepNum + r ≤ Fintype.card W) : HasIndependenceDefectAtLeast r G := by
  obtain ⟨R⟩ := S.exists_oddSubdivisionRouting hodd
  exact (oddSubdivision_hasIndependenceDefectAtLeast R.t r hH).map_copy R.toCopy

end
end Erdos73.GraphSubdivisionModel
