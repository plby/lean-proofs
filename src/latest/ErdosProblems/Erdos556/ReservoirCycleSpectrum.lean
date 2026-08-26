import ErdosProblems.Erdos556.PathLengthWindow
import ErdosProblems.Erdos556.BipartitePaths

/-!
# An interval of cycle lengths from a complete bipartite reservoir

The proved shortening theorem places the exterior path at the required
distance below the target length. A prescribed even reservoir path then
closes a cycle of exactly that length.
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_cycle_of_length_of_bipartite_reservoir {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D d : ℕ) (hD : 0 < D)
    (hscale : Fintype.card V ≤ D * d) (hdegree : ∀ v, d ≤ G.degree v)
    (hN : 8 * (4 * D) ^ 2 ≤ Fintype.card V)
    (X Y : Finset V) (hXY : Disjoint X Y)
    (hcomplete : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y)
    (hX : 16 * D + 8 * (4 * D) ^ 2 + 1 ≤ X.card)
    (hY : 16 * D + 8 * (4 * D) ^ 2 ≤ Y.card)
    (hR : 2 * ((X ∪ Y).card + 16 * D + 1) ≤ d)
    (u v : V) (hu : u ∈ X) (hv : v ∈ X) (huv : u ≠ v)
    (p : G.Walk u v) (hp : p.IsPath)
    (hoff : ∀ z ∈ p.support, z ∈ X ∪ Y → z = u ∨ z = v)
    (n : ℕ) (hn : 32 * D + 8 * (4 * D) ^ 2 + 4 ≤ n)
    (hnp : n ≤ p.length + 2) (hpar : n % 2 = p.length % 2) :
    ∃ c : G.Walk u u, c.IsCycle ∧ c.length = n := by
  obtain ⟨q, hq, hqt, hwin, hqpar, hqoff⟩ := exists_path_in_length_window G D d hD
    hscale hdegree hN (X ∪ Y) hR (n - 2) (by omega) p hp (by omega) hoff
  let L := (n - q.length) / 2
  have hqparn : q.length % 2 = n % 2 := hqpar.trans hpar.symm
  have hqgt : 1 < q.length := by omega
  have hL : 0 < L := by dsimp [L]; omega
  have hLe : L ≤ 16 * D + 8 * (4 * D) ^ 2 := by dsimp [L]; omega
  have hlen : q.length + 2 * L = n := by dsimp [L]; omega
  obtain ⟨c, hc, hclen⟩ := exists_cycle_of_bipartite_reservoir G L hL X Y hXY hcomplete
    (by omega) (by omega) u v hu hv huv q hq hqgt hqoff
  exact ⟨c, hc, hclen.trans hlen⟩

#print axioms exists_cycle_of_length_of_bipartite_reservoir

end Erdos556
