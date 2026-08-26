import ErdosProblems.Erdos73.AntipodalPortGraph
import ErdosProblems.Erdos73.EdgePortAssignment

/-! Select and orient actual disjoint paths for the simple antipodal quotient. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {N : ℕ} {U W V : Type*} [Fintype U] [LinearOrder U] [Fintype V]
variable {G : SimpleGraph V}

theorem GraphPath.orientBetween_length (P : GraphPath G) {x y : V}
    (h : P.Connects {x} {y}) : (P.orientBetween h).walk.length = P.walk.length := by
  by_cases hdir : P.source ∈ ({x} : Finset V) ∧ P.target ∈ ({y} : Finset V)
  · have he : P.orientBetween h = P := by
      dsimp only [GraphPath.orientBetween, GraphPath.orient]
      exact if_pos hdir
    exact congrArg (fun Q : GraphPath G => Q.walk.length) he
  · have he : P.orientBetween h = P.reverse := by
      dsimp only [GraphPath.orientBetween, GraphPath.orient]
      exact if_neg hdir
    exact (congrArg (fun Q : GraphPath G => Q.walk.length) he).trans P.walk.length_reverse

theorem exists_antipodal_edge_paths (label : Fin (2 * N) → U)
    (nails : Fin (2 * N) → W) (branch : W → V) (P : Fin N → GraphPath G)
    (hs : ∀ i, (P i).source = branch (nails (firstPort i)))
    (ht : ∀ i, (P i).target = branch (nails (secondPort i)))
    (hodd : ∀ i, Odd (P i).walk.length)
    (hdis : Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet))
    (Z : Finset V) (hclean : ∀ i x, x ∈ (P i).vertexSet → x ∈ Z →
      x = (P i).source ∨ x = (P i).target) :
    ∃ Q : OrientedEdge (antipodalPortGraph label) → GraphPath G,
      (∀ e, (Q e).source = branch (nails (antipodalEdgeSource label e))) ∧
      (∀ e, (Q e).target = branch (nails (antipodalEdgeTarget label e))) ∧
      (∀ e, Odd (Q e).walk.length) ∧
      Pairwise (fun e f => Disjoint (Q e).vertexSet (Q f).vertexSet) ∧
      (∀ e x, x ∈ (Q e).vertexSet → x ∈ Z → x = (Q e).source ∨ x = (Q e).target) := by
  have hconn (e : OrientedEdge (antipodalPortGraph label)) :
      (P (antipodalEdgeIndex label e)).Connects
        {branch (nails (antipodalEdgeSource label e))}
        {branch (nails (antipodalEdgeTarget label e))} := by
    simp only [GraphPath.Connects, mem_singleton, hs, ht]
    dsimp only [antipodalEdgeSource, antipodalEdgeTarget]
    split_ifs <;> simp
  let Q (e : OrientedEdge (antipodalPortGraph label)) :=
    (P (antipodalEdgeIndex label e)).orientBetween (hconn e)
  have hset (e : OrientedEdge (antipodalPortGraph label)) :
      (Q e).vertexSet = (P (antipodalEdgeIndex label e)).vertexSet :=
    GraphPath.orientBetween_vertexSet _ _
  refine ⟨Q, fun _ => GraphPath.orientBetween_source _ _,
    fun _ => GraphPath.orientBetween_target _ _, ?_, ?_, ?_⟩
  · intro e
    change Odd ((P (antipodalEdgeIndex label e)).orientBetween (hconn e)).walk.length
    rw [GraphPath.orientBetween_length]
    exact hodd _
  · intro e f hef
    rw [hset, hset]
    exact hdis (fun he => hef (antipodalEdgeIndex_injective label he))
  · intro e x hx hZ
    rw [hset] at hx
    exact (GraphPath.orient_isEndpoint _ (hconn e)).mpr (hclean _ x hx hZ)

end
end Erdos73
