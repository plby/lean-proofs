import ErdosProblems.Erdos157.PrimeProgressions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Relative error bounds suitable for a growing polynomial modulus. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Filter
open scoped Topology

noncomputable def progressionRelativeError (q H n : ℝ) : ℝ :=
  H * Real.exp (H * Real.log q - n / (100 * H)) +
    2 * n * (n + 1) * Real.exp ((H - n / 2) * Real.log q)

theorem progressionRelativeError_nonneg (q H n : ℝ) (hH : 0 ≤ H) (hn : 0 ≤ n) :
    0 ≤ progressionRelativeError q H n := by
  unfold progressionRelativeError
  positivity

theorem normalize_progression_error (q : ℝ) (hq : 1 ≤ q) (H n : ℕ) :
    q ^ H * ((H : ℝ) * q ^ n * Real.exp (-(n : ℝ) / (100 * H)) +
      2 * (n : ℝ) * (n / 2 + 1 : ℕ) * q ^ (n / 2)) ≤
    q ^ n * progressionRelativeError q H n := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq
  have hpow (d : ℕ) : q ^ d = Real.exp ((d : ℝ) * Real.log q) := by
    rw [Real.exp_nat_mul, Real.exp_log hqpos]
  have hhalf : (n / 2 : ℕ) ≤ n := Nat.div_le_self _ _
  have hhalf' : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    have h := Nat.div_mul_le_self n 2
    have hc : ((n / 2 : ℕ) : ℝ) * 2 ≤ n := by exact_mod_cast h
    linarith
  have hfirst : q ^ H * ((H : ℝ) * q ^ n * Real.exp (-(n : ℝ) / (100 * H))) =
      q ^ n * ((H : ℝ) * Real.exp ((H : ℝ) * Real.log q - (n : ℝ) / (100 * H))) := by
    rw [Real.exp_sub, hpow H, neg_div, Real.exp_neg]
    ring
  have hsecond : q ^ H * q ^ (n / 2) ≤
      q ^ n * Real.exp (((H : ℝ) - (n : ℝ) / 2) * Real.log q) := by
    rw [hpow H, hpow (n / 2), hpow n, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ = q ^ H * ((H : ℝ) * q ^ n * Real.exp (-(n : ℝ) / (100 * H))) +
        2 * (n : ℝ) * (n / 2 + 1 : ℕ) * (q ^ H * q ^ (n / 2)) := by ring
    _ ≤ q ^ H * ((H : ℝ) * q ^ n * Real.exp (-(n : ℝ) / (100 * H))) +
        2 * (n : ℝ) * ((n : ℝ) + 1) *
          (q ^ n * Real.exp (((H : ℝ) - (n : ℝ) / 2) * Real.log q)) := by
      apply add_le_add le_rfl
      apply mul_le_mul _ hsecond (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast Nat.add_le_add_right hhalf 1
    _ = _ := by rw [hfirst]; unfold progressionRelativeError; ring

/-- The modulus may grow, provided its degree is small compared with the scale. -/
theorem progressionRelativeError_le (q H n k : ℝ) (hq : 1 ≤ q)
    (hH : 0 < H) (hn : 0 ≤ n) (hk : 0 ≤ k) (hHk : H ≤ k)
    (hlarge : 100 * (Real.log q + 1) * H * k ≤ n) (hquarter : H ≤ n / 4) :
    progressionRelativeError q H n ≤
      k * Real.exp (-k) + 2 * n * (n + 1) * Real.exp (-(Real.log q / 4) * n) := by
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq
  have hdiv : (Real.log q + 1) * k ≤ n / (100 * H) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [hlarge]
  have hexp : H * Real.log q - n / (100 * H) ≤ -k := by
    nlinarith
  have hpow : (H - n / 2) * Real.log q ≤ -(Real.log q / 4) * n := by
    nlinarith
  unfold progressionRelativeError
  apply add_le_add
  · exact mul_le_mul hHk (Real.exp_le_exp.mpr hexp) (Real.exp_nonneg _) hk
  · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpow) (by positivity)

theorem tendsto_primePowerRelativeMajorant (q : ℝ) (hq : 1 < q) :
    Tendsto (fun n : ℝ => 2 * n * (n + 1) * Real.exp (-(Real.log q / 4) * n))
      atTop (𝓝 0) := by
  have hb : 0 < Real.log q / 4 := div_pos (Real.log_pos hq) (by norm_num)
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (Real.log q / 4) hb
  have h2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (Real.log q / 4) hb
  have h := (h2.add h1).const_mul 2
  convert h using 1
  · ext n
    simp only [Real.rpow_one, Real.rpow_two]
    ring
  · norm_num

theorem tendsto_progressionRelativeError_of_bounds {ι : Type*} {l : Filter ι}
    (q : ℝ) (hq : 1 < q) (H n k : ι → ℝ)
    (hnlim : Tendsto n l atTop) (hklim : Tendsto k l atTop)
    (hbounds : ∀ᶠ i in l, 0 < H i ∧ 0 ≤ n i ∧ 0 ≤ k i ∧ H i ≤ k i ∧
      100 * (Real.log q + 1) * H i * k i ≤ n i ∧ H i ≤ n i / 4) :
    Tendsto (fun i => progressionRelativeError q (H i) (n i)) l (𝓝 0) := by
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hklim
  have h2 := (tendsto_primePowerRelativeMajorant q hq).comp hnlim
  have hsum : Tendsto (fun i => k i * Real.exp (-k i) +
      2 * n i * (n i + 1) * Real.exp (-(Real.log q / 4) * n i)) l (𝓝 0) := by
    simpa only [pow_one, zero_add, Function.comp_def] using h1.add h2
  apply squeeze_zero' _ _ hsum
  · filter_upwards [hbounds] with i hi
    exact progressionRelativeError_nonneg q _ _ hi.1.le hi.2.1
  · filter_upwards [hbounds] with i hi
    exact progressionRelativeError_le q _ _ _ hq.le hi.1 hi.2.1 hi.2.2.1
      hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2

/-- Sublinear modulus degree and quadratic prime degree force vanishing relative error. -/
theorem tendsto_progressionRelativeError_of_sublinear {ι : Type*} {l : Filter ι}
    (q : ℝ) (hq : 1 < q) (H n k : ι → ℝ) (c : ℝ) (hc : 0 < c)
    (hnlim : Tendsto n l atTop) (hklim : Tendsto k l atTop)
    (hsmall : Tendsto (fun i => H i / k i) l (𝓝 0))
    (hHpos : ∀ᶠ i in l, 0 < H i) (hlower : ∀ᶠ i in l, c * k i ^ 2 ≤ n i) :
    Tendsto (fun i => progressionRelativeError q (H i) (n i)) l (𝓝 0) := by
  apply tendsto_progressionRelativeError_of_bounds q hq H n k hnlim hklim
  let A : ℝ := 100 * (Real.log q + 1)
  have hA : 0 < A := by dsimp only [A]; have := Real.log_pos hq; positivity
  have hε : 0 < c / A := div_pos hc hA
  filter_upwards [hHpos, hlower, hklim.eventually_ge_atTop 1,
    hklim.eventually_ge_atTop (4 / c), hsmall.eventually (gt_mem_nhds zero_lt_one),
    hsmall.eventually (gt_mem_nhds hε)] with i hHi hni hki hklarge hHi1 hHic
  have hkpos : 0 < k i := lt_of_lt_of_le zero_lt_one hki
  have hHk : H i ≤ k i := by
    have h := (div_lt_iff₀ hkpos).mp hHi1
    simpa only [one_mul] using h.le
  have hHle : H i ≤ c / A * k i := (div_lt_iff₀ hkpos).mp hHic |>.le
  have hAH : A * H i ≤ c * k i := by
    calc
      _ ≤ A * (c / A * k i) := mul_le_mul_of_nonneg_left hHle hA.le
      _ = _ := by field_simp
  have hlarge : 100 * (Real.log q + 1) * H i * k i ≤ n i := by
    calc
      _ ≤ c * k i * k i := mul_le_mul_of_nonneg_right hAH hkpos.le
      _ = c * k i ^ 2 := by ring
      _ ≤ _ := hni
  have hck : 4 ≤ c * k i := by
    have h := (div_le_iff₀ hc).mp hklarge
    nlinarith
  have hquarter : H i ≤ n i / 4 := by
    have h4 : 4 * k i ≤ c * k i ^ 2 := by nlinarith
    linarith
  exact ⟨hHi, (by nlinarith [sq_nonneg (k i)]), hkpos.le, hHk, hlarge, hquarter⟩

end Erdos157.Elementary.PolynomialCharacters
