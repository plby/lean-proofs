import ErdosProblems.Erdos73.AntipodalPortPaths
import ErdosProblems.Erdos73.NoncrossingLeftRegions
import ErdosProblems.Erdos73.NoncrossingRightRegions
import ErdosProblems.Erdos73.NoncrossingBoundaryRegions

/-! Actual defect witnesses from routed antipodal port words. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {N : ℕ} {U W V : Type*} [Fintype U] [LinearOrder U]
variable [Fintype W] [LinearOrder W] [Fintype V]
variable {H : SimpleGraph W} {G : SimpleGraph V}

theorem hasIndependenceDefectAtLeast_of_antipodal_regions
    (S : GraphSubdivisionModel H G) (col : BipartiteColoringOn G S.vertexSet)
    (b : Bool) (hb : ∀ w, col.color (S.branchVertex w) = b)
    (label : Fin (2 * N) → U) (hsurj : Function.Surjective label)
    (nails : Fin (2 * N) → W) (R : U → Finset W)
    (hR : Pairwise (fun u v => Disjoint (R u) (R v)))
    (hports : ∀ i, nails i ∈ R (label i)) (hconn : ∀ u, (H.induce (R u : Set W)).Connected)
    (P : Fin N → GraphPath G)
    (hs : ∀ i, (P i).source = S.branchVertex (nails (firstPort i)))
    (ht : ∀ i, (P i).target = S.branchVertex (nails (secondPort i)))
    (hodd : ∀ i, Odd (P i).walk.length)
    (hdis : Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet))
    (hclean : ∀ i x, x ∈ (P i).vertexSet → x ∈ S.vertexSet →
      x = (P i).source ∨ x = (P i).target)
    (r : ℕ) (hF : 2 * (antipodalPortGraph label).indepNum + r ≤ Fintype.card U) :
    HasIndependenceDefectAtLeast r G := by
  let s (e : OrientedEdge (antipodalPortGraph label)) := nails (antipodalEdgeSource label e)
  let t (e : OrientedEdge (antipodalPortGraph label)) := nails (antipodalEdgeTarget label e)
  let d (u : U) := nails (portWordFirst label hsurj u)
  have hsR (e : OrientedEdge (antipodalPortGraph label)) : s e ∈ R e.lo := by
    have hh := hports (antipodalEdgeSource label e)
    rw [antipodalEdgeSource_label label e] at hh
    exact hh
  have htR (e : OrientedEdge (antipodalPortGraph label)) : t e ∈ R e.hi := by
    have hh := hports (antipodalEdgeTarget label e)
    rw [antipodalEdgeTarget_label label e] at hh
    exact hh
  have hdR (u : U) : d u ∈ R u := by
    have hh := hports (portWordFirst label hsurj u)
    rw [portWordFirst_label label hsurj u] at hh
    exact hh
  obtain ⟨Q, hQs, hQt, hQo, hQd, hQc⟩ := exists_antipodal_edge_paths
    label nails S.branchVertex P hs ht hodd hdis S.vertexSet hclean
  apply hasIndependenceDefectAtLeast_of_regions_and_links S col b hb R hR hconn
    (edgePortAssignment s t d) (edgePortAssignment_mem R s t d hsR htR hdR) Q
    (fun e => ?_) (fun e => ?_) hQo hQd hQc r hF
  · rw [edgePortAssignment_lo]
    exact hQs e
  · rw [edgePortAssignment_hi]
    exact hQt e

variable {c rows : ℕ}

theorem hasIndependenceDefectAtLeast_of_left_antipodal_word
    (S : GraphSubdivisionModel (elementaryWall c rows) G)
    (col : BipartiteColoringOn G S.vertexSet)
    (b : Bool) (hb : ∀ w, col.color (S.branchVertex w) = b)
    (label : Fin (2 * N) → U) (hsurj : Function.Surjective label)
    (hNC : NoncrossingPortWord label) (nails : Fin (2 * N) → ElementaryWallVertex c rows)
    (hmono : StrictMono (fun i => (nails i).val.1.val))
    (hleft : ∀ i, (nails i).val.2.val ≤ 1) (hc : 2 * N + 2 ≤ c)
    (P : Fin N → GraphPath G)
    (hs : ∀ i, (P i).source = S.branchVertex (nails (firstPort i)))
    (ht : ∀ i, (P i).target = S.branchVertex (nails (secondPort i)))
    (hodd : ∀ i, Odd (P i).walk.length)
    (hdis : Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet))
    (hclean : ∀ i x, x ∈ (P i).vertexSet → x ∈ S.vertexSet →
      x = (P i).source ∨ x = (P i).target)
    (r : ℕ) (hF : 2 * (antipodalPortGraph label).indepNum + r ≤ Fintype.card U) :
    HasIndependenceDefectAtLeast r G := by
  obtain ⟨R, hR, hports, hconn⟩ :=
    exists_disjoint_noncrossing_left_regions label hsurj hNC nails hmono hleft hc
  exact hasIndependenceDefectAtLeast_of_antipodal_regions S col b hb label hsurj nails
    R hR hports hconn P hs ht hodd hdis hclean r hF

theorem hasIndependenceDefectAtLeast_of_right_antipodal_word
    (S : GraphSubdivisionModel (elementaryWall c rows) G)
    (col : BipartiteColoringOn G S.vertexSet)
    (b : Bool) (hb : ∀ w, col.color (S.branchVertex w) = b)
    (label : Fin (2 * N) → U) (hsurj : Function.Surjective label)
    (hNC : NoncrossingPortWord label) (nails : Fin (2 * N) → ElementaryWallVertex c rows)
    (hmono : StrictMono (fun i => (nails i).val.1.val))
    (hright : ∀ i, 2 * (c - 1) ≤ (nails i).val.2.val) (hc : 2 * N + 2 ≤ c)
    (hrows : Odd rows) (P : Fin N → GraphPath G)
    (hs : ∀ i, (P i).source = S.branchVertex (nails (firstPort i)))
    (ht : ∀ i, (P i).target = S.branchVertex (nails (secondPort i)))
    (hodd : ∀ i, Odd (P i).walk.length)
    (hdis : Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet))
    (hclean : ∀ i x, x ∈ (P i).vertexSet → x ∈ S.vertexSet →
      x = (P i).source ∨ x = (P i).target)
    (r : ℕ) (hF : 2 * (antipodalPortGraph label).indepNum + r ≤ Fintype.card U) :
    HasIndependenceDefectAtLeast r G := by
  obtain ⟨R, hR, hports, hconn⟩ :=
    exists_disjoint_noncrossing_right_regions label hsurj hNC nails hmono hright hc hrows
  exact hasIndependenceDefectAtLeast_of_antipodal_regions S col b hb label hsurj nails
    R hR hports hconn P hs ht hodd hdis hclean r hF

theorem hasIndependenceDefectAtLeast_of_boundary_antipodal_word
    (S : GraphSubdivisionModel (elementaryWall c rows) G)
    (col : BipartiteColoringOn G S.vertexSet)
    (b : Bool) (hb : ∀ w, col.color (S.branchVertex w) = b)
    (label : Fin (2 * N) → U) (hsurj : Function.Surjective label)
    (hNC : NoncrossingPortWord label) (nails : Fin (2 * N) → ElementaryWallVertex c rows)
    (leftSide : Fin (2 * N) → Bool) (L : ℕ)
    (hmono : StrictMono (twoSidePortRank nails leftSide L))
    (hrows : ∀ i, (nails i).val.1.val ≤ L)
    (hleft : ∀ i, leftSide i = true → (nails i).val.2.val ≤ 1)
    (hright : ∀ i, leftSide i = false → 2 * (c - 1) ≤ (nails i).val.2.val)
    (hc : 2 * (2 * N) + 3 ≤ c) (hr : uCombBase L (2 * N) < rows)
    (P : Fin N → GraphPath G)
    (hs : ∀ i, (P i).source = S.branchVertex (nails (firstPort i)))
    (ht : ∀ i, (P i).target = S.branchVertex (nails (secondPort i)))
    (hodd : ∀ i, Odd (P i).walk.length)
    (hdis : Pairwise (fun i j => Disjoint (P i).vertexSet (P j).vertexSet))
    (hclean : ∀ i x, x ∈ (P i).vertexSet → x ∈ S.vertexSet →
      x = (P i).source ∨ x = (P i).target)
    (r : ℕ) (hF : 2 * (antipodalPortGraph label).indepNum + r ≤ Fintype.card U) :
    HasIndependenceDefectAtLeast r G := by
  obtain ⟨R, hR, hports, hconn⟩ := exists_disjoint_noncrossing_boundary_regions
    label hsurj hNC nails leftSide hmono hrows hleft hright hc hr
  exact hasIndependenceDefectAtLeast_of_antipodal_regions S col b hb label hsurj nails
    R hR hports hconn P hs ht hodd hdis hclean r hF

end
end Erdos73
