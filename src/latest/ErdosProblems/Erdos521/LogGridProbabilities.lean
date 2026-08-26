/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Endpoint-zero and multiple-root errors on fixed logarithmic grids.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LogGridScale
import ErdosProblems.Erdos521.TwoRootLimits
import ErdosProblems.Erdos521.AsymptoticBounds

namespace Erdos521

open MeasureTheory Filter
open scoped BigOperators Topology

theorem logGrid_zero_probability_sum_tendsto_zero (n : ℕ → ℕ) (s : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hs : Tendsto s atTop atTop) {a : ℝ} (ha : 0 < a) (δ : ℝ) (N : ℕ) :
    Tendsto (fun j ↦ ∑ i ∈ Finset.range (N + 1), sequenceLaw.real
      {ε | |powerSum ε (n j + 1) (logGrid (s j) a δ i)| ≤ 0}) atTop (𝓝 0) := by
  have hcell (i : ℕ) := polynomial_zero_probability_tendsto_zero n (fun j ↦ logGrid (s j) a δ i)
    hn (logGrid_point_tendsto s hs a δ i)
    ((eventually_logGrid_point_bounds s hs ha δ i).mono (fun _ hj ↦ hj.2.le))
  have h := tendsto_finsetSum (Finset.range (N + 1)) (fun i _ ↦ hcell i)
  simpa only [abs_nonpos_iff, Finset.sum_const_zero] using h

theorem eventually_logGrid_two_root_probability (n : ℕ → ℕ) (s : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (hs : Tendsto s atTop atTop)
    (hN : Tendsto (fun j ↦ ((n j + 1 : ℕ) : ℝ) / s j) atTop atTop)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (N : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ j : ℕ in atTop, (∑ i ∈ Finset.range N, sequenceLaw.real {ε |
      2 ≤ intervalRootCount ε (n j) (logGrid (s j) a δ i) (logGrid (s j) a δ (i + 1))}) ≤
      (N : ℝ) * ((normalizedSmallBallConstant + 96) * (Real.exp δ - 1) ^ (4 / 3 : ℝ)) + η := by
  have hd : 0 < Real.exp δ - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hδ)
  have hcell (i : ℕ) (e : ℝ) (he : 0 < e) : ∀ᶠ j : ℕ in atTop,
      sequenceLaw.real {ε | 2 ≤ intervalRootCount ε (n j)
        (logGrid (s j) a δ i) (logGrid (s j) a δ (i + 1))} ≤
          (normalizedSmallBallConstant + 96) * (Real.exp δ - 1) ^ (4 / 3 : ℝ) + e := by
    apply eventually_two_interval_roots_probability n _ _ hn (logGrid_point_tendsto s hs a δ (i + 1)) hd _ he
    filter_upwards [eventually_logGrid_point_bounds s hs ha δ i,
      eventually_logGrid_point_bounds s hs ha δ (i + 1), hs.eventually_gt_atTop 0,
      (logGrid_tail_tendsto_zero n s hs hN ha δ (i + 1)).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with j hja hjb hsj hjtail
    exact ⟨hja.1, logGrid_strictMono hsj ha hδ (Nat.lt_succ_self i), hjb.2,
      (logGrid_width (s j) a δ i).le, hjtail.le⟩
  have h := eventually_finset_sum_le_add (Finset.range N)
    (fun i j ↦ sequenceLaw.real {ε | 2 ≤ intervalRootCount ε (n j)
      (logGrid (s j) a δ i) (logGrid (s j) a δ (i + 1))})
    (fun _ ↦ (normalizedSmallBallConstant + 96) * (Real.exp δ - 1) ^ (4 / 3 : ℝ))
    (fun i _ ↦ hcell i) hη
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h

end Erdos521
