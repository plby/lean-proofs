/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim616

/-!
# Minimal current edge maps for the coordinate Claim 6.16 backend

Only the indexed accessible `M_out` family needs retyping: the `M_1` and
`M_b` allocators already use subtypes of literal original matching edges.
This module avoids the obsolete coarse HostPools API.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoClaim616CoordinateEdgeMaps

open Finset Fintype SimpleGraph
open Erdos547b.ZhaoStability
open Erdos547b.ZhaoLemma611Full
open Erdos547b.ZhaoClaim616

universe u

theorem edgeFinsetSubgraph_edge_mem_parent
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M))
    {e : Sym2 K} (he : e ∈ (edgeFinsetSubgraph M L S).edgeSet) :
    e ∈ M.edgeSet := by
  have hsub : (edgeFinsetSubgraph M L S).Adj e.out.1 e.out.2 := by
    rw [← Subgraph.mem_edgeSet]
    simpa only [e.out_eq] using he
  obtain ⟨f, _hf, h | h⟩ := (edgeFinsetSubgraph_adj M L S).mp hsub
  · have hef : e = f.1 := by
      calc
        e = s(e.out.1, e.out.2) := e.out_eq.symm
        _ = s(orientedEndpoint M L f 0, orientedEndpoint M L f 1) := by
          rw [h.1, h.2]
        _ = f.1 := orientedEndpoint_pair_eq M L f
    simpa only [hef] using f.2
  · have hef : e = f.1 := by
      calc
        e = s(e.out.1, e.out.2) := e.out_eq.symm
        _ = s(orientedEndpoint M L f 1, orientedEndpoint M L f 0) := by
          rw [h.1, h.2]
        _ = s(orientedEndpoint M L f 0, orientedEndpoint M L f 1) :=
          Sym2.eq_swap
        _ = f.1 := orientedEndpoint_pair_eq M L f
    simpa only [hef] using f.2

theorem edgeFinsetSubgraph_edge_selected_witness
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M))
    {e : Sym2 K} (he : e ∈ (edgeFinsetSubgraph M L S).edgeSet) :
    ∃ f ∈ S, e = f.1 := by
  have hsub : (edgeFinsetSubgraph M L S).Adj e.out.1 e.out.2 := by
    rw [← Subgraph.mem_edgeSet]
    simpa only [e.out_eq] using he
  obtain ⟨f, hf, h | h⟩ := (edgeFinsetSubgraph_adj M L S).mp hsub
  · refine ⟨f, hf, ?_⟩
    calc
      e = s(e.out.1, e.out.2) := e.out_eq.symm
      _ = s(orientedEndpoint M L f 0, orientedEndpoint M L f 1) := by
        rw [h.1, h.2]
      _ = f.1 := orientedEndpoint_pair_eq M L f
  · refine ⟨f, hf, ?_⟩
    calc
      e = s(e.out.1, e.out.2) := e.out_eq.symm
      _ = s(orientedEndpoint M L f 1, orientedEndpoint M L f 0) := by
        rw [h.1, h.2]
      _ = s(orientedEndpoint M L f 0, orientedEndpoint M L f 1) :=
        Sym2.eq_swap
      _ = f.1 := orientedEndpoint_pair_eq M L f

def originalEdgeOfSubmatchingIndex
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M))
    (e : Fin (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset.card) :
    MatchingEdge M :=
  ⟨finsetValue (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset e,
    edgeFinsetSubgraph_edge_mem_parent M L S
      ((edgeFinsetSubgraph M L S).edgeSet.toFinite.mem_toFinset.mp
        (finsetValue_mem
          (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset e))⟩

@[simp] theorem originalEdgeOfSubmatchingIndex_val
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M))
    (e : Fin (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset.card) :
    (originalEdgeOfSubmatchingIndex M L S e).1 =
      finsetValue (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset e :=
  rfl

theorem originalEdgeOfSubmatchingIndex_injective
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M)) :
    Function.Injective (originalEdgeOfSubmatchingIndex M L S) := by
  intro e f hef
  apply finsetValue_injective
    (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset
  have hval := congrArg (fun z : MatchingEdge M ↦ z.1) hef
  simpa only [originalEdgeOfSubmatchingIndex_val] using hval

theorem originalEdgeOfSubmatchingIndex_mem
    {K : Type u} [Fintype K] [DecidableEq K]
    {R : SimpleGraph K} [DecidableRel R.Adj]
    (M : R.Subgraph) (L : Finset K) (S : Finset (MatchingEdge M))
    (e : Fin (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset.card) :
    originalEdgeOfSubmatchingIndex M L S e ∈ S := by
  obtain ⟨f, hf, hef⟩ := edgeFinsetSubgraph_edge_selected_witness M L S
    ((edgeFinsetSubgraph M L S).edgeSet.toFinite.mem_toFinset.mp
      (finsetValue_mem
        (edgeFinsetSubgraph M L S).edgeSet.toFinite.toFinset e))
  have heq : originalEdgeOfSubmatchingIndex M L S e = f := Subtype.ext hef
  simpa only [heq] using hf

section

variable {K : Type u} [Fintype K] [DecidableEq K]
variable {R : SimpleGraph K} [DecidableRel R.Adj]
variable {L O : Finset K} {miss lowerV1 upperV1 upperV2 mbBound : ℕ}
variable {C67 : Claim67Certificate R L miss}
variable {degreeA : Finset (MatchingEdge C67.M) → ℝ}
variable
  (D : MatchingDecomposition L O miss C67 lowerV1 upperV1 upperV2 mbBound
    degreeA)

def moutOriginalEdge
    (e : Fin D.Mout.edgeSet.toFinite.toFinset.card) : MatchingEdge C67.M :=
  originalEdgeOfSubmatchingIndex C67.M L
    (allMatchingEdges C67.M \ D.minEdges) e

@[simp] theorem moutOriginalEdge_val
    (e : Fin D.Mout.edgeSet.toFinite.toFinset.card) :
    (moutOriginalEdge D e).1 =
      finsetValue D.Mout.edgeSet.toFinite.toFinset e :=
  rfl

theorem moutOriginalEdge_injective : Function.Injective (moutOriginalEdge D) :=
  originalEdgeOfSubmatchingIndex_injective C67.M L
    (allMatchingEdges C67.M \ D.minEdges)

theorem moutOriginalEdge_mem
    (e : Fin D.Mout.edgeSet.toFinite.toFinset.card) :
    moutOriginalEdge D e ∈ allMatchingEdges C67.M \ D.minEdges :=
  originalEdgeOfSubmatchingIndex_mem C67.M L
    (allMatchingEdges C67.M \ D.minEdges) e

end

end Erdos547b.ZhaoClaim616CoordinateEdgeMaps

#print axioms Erdos547b.ZhaoClaim616CoordinateEdgeMaps.moutOriginalEdge_injective
