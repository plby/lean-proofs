import ErdosProblems.Erdos547.ReducedGraph
import ErdosProblems.Erdos547.ClusterDegrees

/-!
# Minimum weighted degree inherited by the reduced graph
-/

namespace Erdos547.EquitableRegularPartition

open SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {ε : ℝ}
variable (P : EquitableRegularPartition G ε)

theorem reduced_min_degree_lower (hε : 0 ≤ ε) (d : ℝ) (hd : 0 ≤ d)
    (D : ℝ) (hD : ∀ v, D ≤ (G.degree v : ℝ)) (X : ↥P.clusters) :
    D - ((2 * ε + d) * Fintype.card V + P.clusterSize) ≤
      (P.clusterSize : ℝ) * (P.reducedWeights d).degree X := by
  have hlow := P.density_lower_of_min_degree D hD X
  have hsum := mul_le_mul_of_nonneg_left (P.sum_density_le_reduced_degree d hd X)
    (Nat.cast_nonneg P.clusterSize : (0 : ℝ) ≤ P.clusterSize)
  have hvolume : (P.clusterSize : ℝ) * P.clusters.card ≤ Fintype.card V := by
    exact_mod_cast P.cluster_volume_le
  have hloss := mul_le_mul_of_nonneg_left hvolume (add_nonneg hε hd)
  nlinarith only [hlow, hsum, hloss]

end Erdos547.EquitableRegularPartition

#print axioms Erdos547.EquitableRegularPartition.reduced_min_degree_lower
