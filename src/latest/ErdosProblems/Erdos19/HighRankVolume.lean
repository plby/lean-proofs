import ErdosProblems.Erdos19.HighVolumeWindow
import ErdosProblems.Erdos19.EdgeIncidenceSums

/-! # A dense window of large edges leaves few incidences on small edges -/

namespace Erdos19.SetHypergraph

open Finset

theorem small_rank_incidence_of_dense_window (n R b C : ℕ) (hn : 0 < n)
    (hb : 10 ≤ b) (hC : 10 * C < b)
    (H : SetHypergraph (Fin n)) (hlinear : H.IsLinear)
    (hmin : ∀ e : H, 2 ≤ e.1.ncard) (W : Finset (H.rankAtLeast R))
    (hvolume : (b - 10) * n ^ 2 ≤ b * (∑ e ∈ W, e.1.ncard * (e.1.ncard - 1))) :
    C * (∑ e : H.rankBelow R, e.1.ncard) < n ^ 2 := by
  classical
  let L := H.rankAtLeast R
  let M := H.rankBelow R
  have hwindow : (b - 10) * n ^ 2 ≤
      b * (∑ e : L, e.1.ncard * (e.1.ncard - 1)) :=
    hvolume.trans (Nat.mul_le_mul_left b (sum_le_sum_of_subset (subset_univ W)))
  have htotal : (∑ e : L, e.1.ncard * (e.1.ncard - 1)) +
      (∑ e : M, e.1.ncard * (e.1.ncard - 1)) ≤ n ^ 2 := by
    rw [H.sum_rankAtLeast_add_rankBelow R (fun e ↦ e.ncard * (e.ncard - 1))]
    have h := H.sum_ncard_mul_sub_one_le hlinear
    simp only [Fintype.card_fin] at h
    exact h.trans (by
      have hsub := Nat.mul_le_mul_left n (Nat.sub_le n 1)
      simpa only [pow_two] using hsub)
  have hrest := small_complement_pair_volume n b C _ _ hn hb hC htotal hwindow
  have hincidence := M.incidence_le_pair_weight (fun e ↦ hmin ⟨e.1, e.2.1⟩)
  exact (Nat.mul_le_mul_left C hincidence).trans_lt hrest

#print axioms small_rank_incidence_of_dense_window

end Erdos19.SetHypergraph
