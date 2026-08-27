import Arxiv.Arxiv2411_18291.EliminationPattern
import Arxiv.Arxiv2411_18291.AbsorberWorkingParameters

/-! # Exchange and elimination configurations with bounded vertex carriers -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem paper_exchange_vertex_bound {q r : ℕ} (hr : 1 ≤ r) (hqr : r < q) :
    6 * q ^ 2 * q.choose r ≤ (4 * q) ^ (2 * q) := by
  have hq : 2 ≤ q := by omega
  calc
    _ ≤ (4 * q) ^ 2 * (4 * q) ^ q :=
      Nat.mul_le_mul (by nlinarith) ((Nat.choose_le_two_pow q r).trans
        (Nat.pow_le_pow_left (by omega) q))
    _ = (4 * q) ^ (2 + q) := by rw [pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

/-- The actual exchange construction needs no additional assumption about
its carrier: both its edges and all its vertices satisfy explicit bounds. -/
theorem exists_small_carrier_clique_exchange (q r : ℕ) (hr : 1 ≤ r) (hqr : r < q) :
    ∃ T : FiniteExchangeSystem q r, ∃ A : Finset (Block T.Vertex q),
      T.system.graph.card ≤ 3 * (2 * q) ^ r * (q.choose r) ^ 2 ∧
      IsExchangeFamily T.system A ∧ IsCrossSimple r T.system.positive T.system.negative ∧
      IsPositiveFrameLocal T.system A ∧
      Fintype.card T.Vertex ≤ (4 * q) ^ (2 * q) := by
  obtain ⟨T, A, hc, hA, hs, hl, hv⟩ :=
    exists_local_crossSimple_clique_exchange_with_vertex_bound q r hr hqr
  exact ⟨T, A, hc, hA, hs, hl, hv.trans (paper_exchange_vertex_bound hr hqr)⟩

/-- A cancellation pattern, including its prescribed opposite-sign pair,
can be chosen with the same finite carrier bound. -/
theorem exists_small_carrier_elimination_pattern (q r : ℕ) (hqr : r + 1 < q) :
    ∃ T : FiniteExchangeSystem q (r + 1), ∃ N : Block T.Vertex q,
      ∃ e : Block T.Vertex (r + 1), IsEliminationPair T.system N e ∧
        T.system.graph.card ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2 ∧
        Fintype.card T.Vertex ≤ (4 * q) ^ (2 * q) := by
  obtain ⟨T, A, hc, hA, hs, _, hv⟩ :=
    exists_small_carrier_clique_exchange q (r + 1) (Nat.succ_pos r) hqr
  obtain ⟨e, he⟩ := cliqueEdges_nonempty hqr.le T.system.base
  obtain ⟨N, hN, hNe⟩ := hA.2.2.1 e he
  refine ⟨T, N, e, ⟨hA.1 hN, ?_, fun f hf => hA.pair_local hN hf, hs⟩, hc, hv⟩
  rw [inter_comm]
  exact vertices_inter_eq_of_cliqueEdges_singleton (Nat.succ_pos r) N T.system.base e hNe

end Arxiv2411_18291
