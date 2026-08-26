import ErdosProblems.Erdos547.ReducedGraph
import ErdosProblems.Erdos547.AllocationOperations

/-!
# Regular-pair and density information carried by reduced edges
-/

namespace Erdos547

open Finset SimpleGraph

theorem reducedDensity_le_density {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ε d : ℝ) (X Y : Finset V) :
    reducedDensity G ε d X Y ≤ (G.edgeDensity X Y : ℝ) := by
  classical
  unfold reducedDensity
  split_ifs
  · exact le_rfl
  · exact_mod_cast G.edgeDensity_nonneg X Y

namespace EquitableRegularPartition

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  [DecidableRel G.Adj] {ε : ℝ} (R : EquitableRegularPartition G ε)

theorem index_disjoint (i j : ↥R.clusters) (hij : i ≠ j) : Disjoint i.val j.val :=
  R.disjoint i.val i.property j.val j.property (fun h ↦ hij (Subtype.ext h))

theorem reduced_pair (d : ℝ) (i j : ↥R.clusters) (hij : (R.reducedGraph d).Adj i j) :
    G.IsUniform ε i.val j.val ∧ Disjoint i.val j.val ∧ d ≤ (G.edgeDensity i.val j.val : ℝ) :=
  ⟨hij.2.1, R.disjoint i.val i.property j.val j.property hij.1, hij.2.2⟩

theorem reduced_weight_le_density (d : ℝ) (i j : ↥R.clusters) :
    (R.reducedWeights d).weight i j ≤ (G.edgeDensity i.val j.val : ℝ) :=
  reducedDensity_le_density G ε d i.val j.val

end EquitableRegularPartition

namespace DPRS.SkewMatching

theorem Fits.adj_of_outLoad_pos {I : Type*} [Fintype I] {K : SimpleGraph I} {γ : ℝ}
    {σ : SkewMatching K γ} {w : EdgeWeights K} {a : I} (hfit : σ.Fits w a)
    (i : I) (hi : 0 < σ.outLoad i) : K.Adj a i := by
  by_contra hn
  have hh := hfit i
  rw [w.supported a i hn] at hh
  exact (not_le_of_gt hi) hh

end DPRS.SkewMatching
end Erdos547
