import ErdosProblems.Erdos1105.CappedEdges
import ErdosProblems.Erdos1105.ConnectedPathBound

namespace Erdos1105

/-- Move the vertices between a distinguished connected component and
the remaining components. Convexity reduces the edge count to the two
endpoint allocations. -/
theorem path_component_endpoint_bound {n n₀ k a d : ℕ}
    (hk : 4 ≤ k) (ha : 2 * a ≤ k - 2) (hn₀ : k ≤ n₀) (hn : n₀ < n) :
    pathExtremalEdges n₀ (k - 1) a + cappedEdgeBound (n - n₀) d ≤
      max ((k - 1).choose 2 + cappedEdgeBound (n - k + 1) d)
        (pathExtremalEdges (n - 1) (k - 1) a) := by
  let M := n - k
  let m := n - n₀
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmM : m ≤ M := by dsimp [m, M]; omega
  have hmove : n₀ - k = M - m := by dsimp [M, m]; omega
  have hlast : M - 1 = n - 1 - k := by dsimp [M]; omega
  have hbase := pathExtremalEdges_at_path_order_le_clique hk ha
  have hmax := cappedEdgeBound_affine_max (d := d) (a := a) hm hmM
  calc
    _ = pathExtremalEdges k (k - 1) a +
        (cappedEdgeBound m d + a * (M - m)) := by
      rw [← pathExtremalEdges_affine (by omega : k - 1 ≤ k) hn₀, hmove]
      dsimp [m]
      omega
    _ ≤ pathExtremalEdges k (k - 1) a +
        max (a * (M - 1)) (cappedEdgeBound M d) := Nat.add_le_add_left hmax _
    _ = max (pathExtremalEdges k (k - 1) a + a * (M - 1))
        (pathExtremalEdges k (k - 1) a + cappedEdgeBound M d) := by omega
    _ ≤ _ := by
      apply max_le
      · rw [hlast, pathExtremalEdges_affine (by omega : k - 1 ≤ k) (by omega : k ≤ n - 1)]
        exact le_max_right _ _
      · apply le_trans ?_ (le_max_left _ _)
        exact Nat.add_le_add hbase (cappedEdgeBound_mono (by dsimp [M]; omega) d)

end Erdos1105

#print axioms Erdos1105.path_component_endpoint_bound
