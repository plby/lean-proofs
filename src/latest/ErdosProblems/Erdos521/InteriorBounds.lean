/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform bounds for roots away from the endpoints in Erdős Problem 521.
For sign coefficients the compact-interior part of Do's argument follows
deterministically from Jensen's inequality and a geometric-series bound.
Formal proof: Codex.
https://arxiv.org/abs/2403.06353
-/
import ErdosProblems.Erdos521.Model
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib

namespace Erdos521

open Filter MeasureTheory Metric MeromorphicOn
open scoped BigOperators Topology

/-- Evaluation of the degree-`n` polynomial on the complex plane. -/
def complexPowerSum (a : ℕ → ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), (a k : ℂ) * z ^ k

theorem complexPowerSum_zero (a : ℕ → ℝ) (n : ℕ) :
    complexPowerSum a n 0 = (a 0 : ℂ) := by
  simp [complexPowerSum, Finset.sum_range_succ']

theorem complexPowerSum_ofReal (a : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    complexPowerSum a n (x : ℂ) = (powerSum a (n + 1) x : ℂ) := by
  simp [complexPowerSum, powerSum]

theorem analyticOnNhd_complexPowerSum (a : ℕ → ℝ) (n : ℕ) :
    AnalyticOnNhd ℂ (complexPowerSum a n) Set.univ := by
  intro z _
  unfold complexPowerSum
  fun_prop

theorem norm_complexPowerSum_le (a : ℕ → ℝ) (ha : ∀ k, |a k| ≤ 1)
    (n : ℕ) {R : ℝ} (hR₀ : 0 ≤ R) (hR₁ : R < 1) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖complexPowerSum a n z‖ ≤ (1 - R)⁻¹ := by
  calc
    ‖complexPowerSum a n z‖ ≤
        ∑ k ∈ Finset.range (n + 1), ‖(a k : ℂ) * z ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (n + 1), R ^ k := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul (ha k) (pow_le_pow_left₀ (norm_nonneg _) hz k)
        (pow_nonneg (norm_nonneg _) _) zero_le_one).trans_eq (one_mul _)
    _ ≤ (1 - R)⁻¹ := by
      simpa using geom_sum_Ico_le_of_lt_one (m := 0) (n := n + 1) hR₀ hR₁

/-- Each distinct zero contributes at least one to the divisor. -/
theorem card_le_sum_divisor_center {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (c : ℂ) (hfc : f c ≠ 0) (r : ℝ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ∈ closedBall c r ∧ f z = 0) :
    (S.card : ℤ) ≤ ∑ᶠ z, divisor f (closedBall c r) z := by
  classical
  have hball : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono (Set.subset_univ _)
  have hfinite := (divisor f (closedBall c r)).finiteSupport (isCompact_closedBall c r)
  have hpos (z : ℂ) (hz : z ∈ S) : 1 ≤ divisor f (closedBall c r) z := by
    have htop : analyticOrderAt f z ≠ ⊤ := by
      intro htop
      have hzero := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z
        (fun w ↦ hf w trivial)).mp htop
      exact hfc (congrFun hzero c)
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp htop
    have hkpos : k ≠ 0 := by
      intro hkzero
      have hnz := (hf z trivial).analyticOrderAt_ne_zero.mpr (hS z hz).2
      apply hnz
      rw [← hk, hkzero]
      rfl
    rw [hball.divisor_apply (hS z hz).1, ← hk]
    simpa using (show (1 : ℤ) ≤ k by omega)
  have hsub : S ⊆ hfinite.toFinset := by
    intro z hz
    simp only [Set.Finite.mem_toFinset, Function.mem_support]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one (hpos z hz))
  rw [finsum_eq_sum_of_support_subset _ (s := hfinite.toFinset) (by simp)]
  calc
    (S.card : ℤ) = ∑ _ ∈ S, (1 : ℤ) := by simp
    _ ≤ ∑ z ∈ S, divisor f (closedBall c r) z := Finset.sum_le_sum hpos
    _ ≤ ∑ z ∈ hfinite.toFinset, divisor f (closedBall c r) z :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ ↦ hball.divisor_nonneg z)

theorem card_le_sum_divisor {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hf₀ : f 0 ≠ 0) (r : ℝ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ∈ closedBall 0 r ∧ f z = 0) :
    (S.card : ℤ) ≤ ∑ᶠ z, divisor f (closedBall 0 r) z :=
  card_le_sum_divisor_center hf 0 hf₀ r S hS

/-- Number of distinct real roots in the fixed interval `[-r,r]`. -/
noncomputable def smallRootCount (a : ℕ → ℝ) (n : ℕ) (r : ℝ) : ℕ := by
  classical
  exact ((realRoots a n).filter fun x ↦ |x| ≤ r).card

/-- Jensen gives a bound independent of the degree on every smaller interval. -/
theorem smallRootCount_le (a : ℕ → ℝ) (ha : ∀ k, |a k| = 1)
    (n : ℕ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < 1) :
    (smallRootCount a n r : ℝ) ≤ Real.log ((1 - R)⁻¹) / Real.log (R / r) := by
  classical
  have hf := analyticOnNhd_complexPowerSum a n
  have ha₀ : a 0 ≠ 0 := by
    intro hzero
    have h := ha 0
    simp [hzero] at h
  have hf₀ : complexPowerSum a n 0 ≠ 0 := by
    rw [complexPowerSum_zero]
    exact_mod_cast ha₀
  have hnorm : ‖complexPowerSum a n 0‖ = 1 := by
    simpa [complexPowerSum_zero, Complex.norm_real, Real.norm_eq_abs] using ha 0
  let S := (realRoots a n).filter fun x ↦ |x| ≤ r
  have hS (z : ℂ) (hz : z ∈ S.image Complex.ofReal) :
      z ∈ closedBall 0 r ∧ complexPowerSum a n z = 0 := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hx' := Finset.mem_filter.mp hx
    constructor
    · simpa [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] using hx'.2
    · rw [complexPowerSum_ofReal, (mem_realRoots a n ha₀ x).mp hx'.1]
      simp
  have hcard : (smallRootCount a n r : ℤ) ≤
      ∑ᶠ z, divisor (complexPowerSum a n) (closedBall 0 r) z := by
    have h := card_le_sum_divisor hf hf₀ r (S.image Complex.ofReal) hS
    simpa only [Finset.card_image_of_injective _ Complex.ofReal_injective, smallRootCount,
      S] using h
  have hM : 1 ≤ (1 - R)⁻¹ := by
    rw [one_le_inv₀ (sub_pos.mpr hR)]
    linarith
  have hfbound (z : ℂ) (hz : z ∈ sphere 0 |R|) :
      ‖complexPowerSum a n z‖ ≤ (1 - R)⁻¹ := by
    have hz' : ‖z‖ = R := by
      simpa [Metric.mem_sphere, dist_zero_right, abs_of_pos (hr.trans hrR)] using hz
    exact norm_complexPowerSum_le a (fun k ↦ (ha k).le) n (hr.trans hrR).le hR hz'.le
  have hbound := (hf.mono (Set.subset_univ (closedBall 0 |R|))).sum_divisor_le
    (r := r) (by simpa [abs_of_pos hr] using hr)
    (by simpa [abs_of_pos hr, abs_of_pos (hr.trans hrR)] using hrR) hM hf₀
    hfbound
  rw [hnorm, div_one, abs_of_pos hr] at hbound
  have hcard' : (smallRootCount a n r : ℝ) ≤
      ((∑ᶠ z, divisor (complexPowerSum a n) (closedBall 0 r) z : ℤ) : ℝ) := by
    exact_mod_cast hcard
  exact hcard'.trans hbound

/-- For sign coefficients, compact-interior roots have vanishing logarithmic density
for every sample; no probabilistic exceptional set is needed. -/
theorem smallRootCount_div_log_tendsto_zero (a : ℕ → ℝ) (ha : ∀ k, |a k| = 1)
    {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    Tendsto (fun n : ℕ ↦ (smallRootCount a n r : ℝ) / Real.log n) atTop (𝓝 0) := by
  apply tendsto_bdd_div_atTop_nhds_zero
    (b := 0) (B := Real.log ((1 - (r + 1) / 2)⁻¹) / Real.log (((r + 1) / 2) / r))
  · exact Filter.Eventually.of_forall fun _ ↦ Nat.cast_nonneg _
  · exact Filter.Eventually.of_forall fun n ↦ smallRootCount_le a ha n hr
      (by linarith) (by linarith)
  · exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem ae_smallRootCount_div_log_tendsto_zero :
    ∀ᵐ ε ∂sequenceLaw, ∀ r : ℝ, 0 < r → r < 1 →
      Tendsto (fun n : ℕ ↦ (smallRootCount ε n r : ℝ) / Real.log n) atTop (𝓝 0) := by
  filter_upwards [ae_sequence_signs] with ε hsign
  intro r hr hr₁
  apply smallRootCount_div_log_tendsto_zero ε _ hr hr₁
  intro k
  rcases hsign k with h | h <;> simp [h]

end Erdos521
