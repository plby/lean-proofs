/- Adapted from the checked repository proof in Erdos1148/RealDirichletValue.lean. -/
import ErdosProblems.Erdos941.DirichletWeightedSums

/-! # Ordered real Dirichlet-series values and quantitative truncation -/

namespace Erdos941.Analytic

open Filter Topology

noncomputable def realDirichletPartialSum {q : ℕ} (χ : DirichletCharacter ℝ q)
    (s : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) ^ (-s) * χ (k + 1)

noncomputable def realDirichletValue {q : ℕ} (χ : DirichletCharacter ℝ q) (s : ℝ) : ℝ :=
  limUnder atTop (realDirichletPartialSum χ s)

theorem realDirichletPartialSum_tendsto {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s) :
    Tendsto (realDirichletPartialSum χ s) atTop (𝓝 (realDirichletValue χ s)) :=
  tendsto_nhds_limUnder (dirichlet_real_series_converges χ hχ hs)

lemma realDirichletPartialSum_sub {q : ℕ} (χ : DirichletCharacter ℝ q) (s : ℝ)
    {a b : ℕ} (hab : a ≤ b) :
    realDirichletPartialSum χ s b - realDirichletPartialSum χ s a =
      ∑ k ∈ Finset.Ico (a + 1) (b + 1), (k : ℝ) ^ (-s) * χ k := by
  have h := eq_sub_of_add_eq' (Finset.sum_range_add_sum_Ico
    (fun k => ((k + 1 : ℕ) : ℝ) ^ (-s) * χ (k + 1)) hab)
  unfold realDirichletPartialSum
  rw [← h]
  simpa only [Nat.cast_add, Nat.cast_one] using
    Finset.sum_Ico_add' (fun k : ℕ => (k : ℝ) ^ (-s) * χ k) a b 1

theorem realDirichletValue_sub_partialSum_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ‖realDirichletValue χ s - realDirichletPartialSum χ s n‖ ≤
      2 * q * ((n + 1 : ℕ) : ℝ) ^ (-s) := by
  apply le_of_tendsto ((realDirichletPartialSum_tendsto χ hχ hs).sub_const
    (realDirichletPartialSum χ s n)).norm
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [realDirichletPartialSum_sub χ s hm]
  exact dirichlet_norm_sum_Ico_rpow_le χ hχ (Nat.succ_pos n) hs.le

theorem realDirichletValue_norm_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s) :
    ‖realDirichletValue χ s‖ ≤ 2 * q := by
  simpa only [realDirichletPartialSum, Finset.range_zero, Finset.sum_empty, sub_zero,
    zero_add, Nat.cast_one, Real.one_rpow, mul_one] using
    realDirichletValue_sub_partialSum_norm_le χ hχ hs 0

end Erdos941.Analytic
