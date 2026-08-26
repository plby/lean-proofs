import ErdosProblems.Erdos547.ClusterVertexDegrees
import ErdosProblems.Erdos547.ReducedMinimumDegree

/-!
# Maximum weighted degree from a positive proportion of high-degree vertices
-/

namespace Erdos547.EquitableRegularPartition

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {ε : ℝ}
variable (P : EquitableRegularPartition G ε)

theorem reduced_degree_lower_of_typical (hε : 0 ≤ ε) (d : ℝ) (hd : 0 ≤ d)
    (δ : ℝ) (hδ : 0 ≤ δ) (X : ↥P.clusters) (v : V)
    (hv : ((P.upperExceptionalPairs X.val v).card : ℝ) ≤ δ * P.clusters.card) :
    (G.degree v : ℝ) - ((4 * ε + d + δ) * Fintype.card V + 2 * P.clusterSize) ≤
      (P.clusterSize : ℝ) * (P.reducedWeights d).degree X := by
  have hhost := P.typical_vertex_degree_le hε δ X v hv
  have hsum := mul_le_mul_of_nonneg_left (P.sum_density_le_reduced_degree d hd X)
    (Nat.cast_nonneg P.clusterSize : (0 : ℝ) ≤ P.clusterSize)
  have hvolume : (P.clusterSize : ℝ) * P.clusters.card ≤ Fintype.card V := by
    exact_mod_cast P.cluster_volume_le
  have hloss := mul_le_mul_of_nonneg_left hvolume
    (show 0 ≤ 3 * ε + d + δ by positivity)
  nlinarith only [hhost, hsum, hloss]

theorem exists_reduced_high_degree (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (d : ℝ) (hd : 0 ≤ d) (δ : ℝ) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (D : ℝ) (H : Finset V) (hH : ∀ v ∈ H, D ≤ (G.degree v : ℝ))
    (hHcard : (ε + δ) * Fintype.card V < (H.card : ℝ)) :
    ∃ X : ↥P.clusters,
      D - ((4 * ε + d + δ) * Fintype.card V + 2 * P.clusterSize) ≤
        (P.clusterSize : ℝ) * (P.reducedWeights d).degree X := by
  obtain ⟨X, v, _hvX, hD, hv⟩ :=
    P.exists_high_upper_typical_vertex hε hεone δ hδ hεδ D H hH hHcard
  refine ⟨X, ?_⟩
  have hh := P.reduced_degree_lower_of_typical hε d hd δ hδ.le X v hv
  linarith only [hh, hD]

end Erdos547.EquitableRegularPartition

#print axioms Erdos547.EquitableRegularPartition.exists_reduced_high_degree
