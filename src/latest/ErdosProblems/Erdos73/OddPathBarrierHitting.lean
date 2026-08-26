import ErdosProblems.Erdos73.OddPathBarrierCutsets
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-! The barrier deletion meets every augmenting path in the doubled graph. -/

namespace Erdos73.OddPathBarrierWitness

open SimpleGraph Finset Erdos556 OddPathVertex
open Erdos73Infrastructure.SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {A : Finset V} {k : ℕ}

open scoped Classical in
theorem not_surviving_augmentingPath (B : OddPathBarrierWitness G A k)
    {P : GraphPath (oddPathAuxiliary G A)}
    (hP : IsMatchingAugmentingPath (oddPathBaseMatching A) P)
    (hsurv : ∀ x ∈ P.vertexSet, projection x ∉ B.deletion) : False := by
  have hsupp := B.surviving_augmentingPath_supported hP hsurv
  let J := P.walk.toSubgraph.spanningCoe
  let c : J.Coloring Bool := SimpleGraph.Coloring.mk
    (fun x => decide (x ∈ B.representatives)) (by
      intro x y hxy he
      have hedge : s(x, y) ∈ P.edgeSet := List.mem_toFinset.mpr
        (Walk.adj_toSubgraph_iff_mem_edges.mp hxy)
      obtain ⟨hxP, hyP⟩ := P.endpoints_mem_vertexSet_of_edgeSet hedge
      have heq : (x ∈ B.representatives) ↔ (y ∈ B.representatives) := decide_eq_decide.mp he
      have hxyG := P.edgeSet_subset_edgeSet hedge
      by_cases hxZ : x ∈ B.representatives
      · exact B.representatives_independent hxZ (heq.mp hxZ) hxyG
      · have hyZ : y ∉ B.representatives := fun hy => hxZ (heq.mpr hy)
        have hxW := (Finset.mem_union.mp (hsupp hxP)).resolve_left hxZ
        have hyW := (Finset.mem_union.mp (hsupp hyP)).resolve_left hyZ
        exact B.surviving_removed_independent (hsurv x hxP) (hsurv y hyP) hxW hyW hxyG)
  have hedge (e : Sym2 (OddPathVertex A)) (he : e ∈ P.walk.edges) : e ∈ J.edgeSet := by
    rw [Subgraph.edgeSet_spanningCoe]
    exact P.walk.mem_edges_toSubgraph.mpr he
  let p := P.walk.transfer J hedge
  have hsource : c P.source = true := by
    exact decide_eq_true (B.survives_terminal_mem_representatives
      (hsurv _ P.source_mem_vertexSet) (oddPathAugmenting_source_terminal hP))
  have htarget : c P.target = true := by
    exact decide_eq_true (B.survives_terminal_mem_representatives
      (hsurv _ P.target_mem_vertexSet) (oddPathAugmenting_target_terminal hP))
  have heven : Even p.length := (c.even_length_iff_congr p).mpr (by rw [hsource, htarget])
  have hlength : p.length = P.walk.length := Walk.length_transfer _ _
  rw [hlength] at heven
  exact (Nat.not_even_iff_odd.mpr (hP.odd_length (oddPathBaseMatching_isMatching G A))) heven

end Erdos73.OddPathBarrierWitness
