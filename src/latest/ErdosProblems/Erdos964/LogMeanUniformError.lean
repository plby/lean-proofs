import ErdosProblems.Erdos964.ScalarMomentMean

/-!
# Uniform cumulative envelopes from logarithmic mean limits

A limit at infinity gives an arbitrarily small leading error plus a fixed
constant at every endpoint. This is the input for uniform weighted moments.
-/

namespace Erdos964

open BoundedGaps.Maynard Filter
open scoped Topology

theorem exists_log_mean_uniform_error (f : ArithmeticFunction ℝ) (c : ℝ) (k : ℕ)
    (hlimit : Tendsto (fun x : ℝ => abelCumulative f x / (Real.log x) ^ k) atTop (𝓝 c))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |abelCumulative f x - c * (Real.log x) ^ k| ≤ ε * (Real.log x) ^ k + C := by
  have hevent : ∀ᶠ x : ℝ in atTop, |abelCumulative f x / (Real.log x) ^ k - c| ≤ ε := by
    have h := Metric.tendsto_nhds.mp hlimit ε hε
    exact h.mono (fun x hx => by simpa only [Real.dist_eq] using hx.le)
  obtain ⟨X, hX⟩ := eventually_atTop.mp hevent
  let N := ⌈max X 2⌉₊
  have hN : max X 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hNX : X ≤ (N : ℝ) := (le_max_left X 2).trans hN
  have hN2 : (2 : ℝ) ≤ N := (le_max_right X 2).trans hN
  let C := (∑ n ∈ Finset.Icc 0 N, |f n|) + |c| * (Real.log N) ^ k
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact add_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      (mul_nonneg (abs_nonneg c) (pow_nonneg (Real.log_nonneg (by linarith)) k))
  refine ⟨C, hC, ?_⟩
  intro x hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  by_cases hlarge : (N : ℝ) ≤ x
  · have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
    have h := hX x (hNX.trans hlarge)
    have hid : abelCumulative f x / (Real.log x) ^ k - c =
        (abelCumulative f x - c * (Real.log x) ^ k) / (Real.log x) ^ k := by
      field_simp
    rw [hid, abs_div, abs_of_pos (pow_pos hlogpos k)] at h
    exact ((div_le_iff₀ (pow_pos hlogpos k)).mp h).trans (le_add_of_nonneg_right hC)
  · have hxN : x ≤ (N : ℝ) := le_of_lt (lt_of_not_ge hlarge)
    have hfloor : ⌊x⌋₊ ≤ N := by
      have h := Nat.floor_le_floor hxN
      simpa only [Nat.floor_natCast] using h
    have hsum : |abelCumulative f x| ≤ ∑ n ∈ Finset.Icc 0 N, |f n| := by
      unfold abelCumulative
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hfloor⟩
      · intro n hn hnot
        exact abs_nonneg _
    have hpow : (Real.log x) ^ k ≤ (Real.log N) ^ k :=
      pow_le_pow_left₀ hlog (Real.log_le_log (zero_lt_one.trans_le hx) hxN) k
    have hmain : |c * (Real.log x) ^ k| ≤ |c| * (Real.log N) ^ k := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hlog k)]
      exact mul_le_mul_of_nonneg_left hpow (abs_nonneg c)
    have h := (abs_sub (abelCumulative f x) (c * (Real.log x) ^ k)).trans (add_le_add hsum hmain)
    exact h.trans (le_add_of_nonneg_left (mul_nonneg hε.le (pow_nonneg hlog k)))

theorem exists_scalarMoment_two_uniform_error (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |abelCumulative (scalarMomentAF M 2) x -
        (scalarSieveEulerConstant M * (coprimeHarmonicDensity M ^ 2 / 2)) * (Real.log x) ^ 2| ≤
        ε * (Real.log x) ^ 2 + C :=
  exists_log_mean_uniform_error _ _ 2 (tendsto_scalarMomentAF_two_mean M hM h2M h3M) ε hε

theorem exists_scalarMoment_three_uniform_error (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |abelCumulative (scalarMomentAF M 3) x -
        (scalarSieveEulerConstant M * (coprimeHarmonicDensity M ^ 3 / 6)) * (Real.log x) ^ 3| ≤
        ε * (Real.log x) ^ 3 + C :=
  exists_log_mean_uniform_error _ _ 3 (tendsto_scalarMomentAF_three_mean M hM h2M h3M) ε hε

end Erdos964
