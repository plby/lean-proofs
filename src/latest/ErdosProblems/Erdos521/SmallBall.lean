/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Quantitative small-ball bounds for the fair-sign polynomial in Erdős 521.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.Characteristic
import ErdosProblems.Erdos521.GaussianSmoothing

namespace Erdos521

open MeasureTheory ProbabilityTheory

/-- Gaussian smoothing turns a finite-frequency characteristic-function estimate
into a small-ball bound, retaining the explicit frequency truncation error. -/
theorem smallBall_of_charFun_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {c V T δ : ℝ} (hc : 0 < c) (hV : 0 < V) (hT : 0 ≤ T) (hδ : 0 < δ)
    (hchar : ∀ u : ℝ, |u| ≤ T →
      ‖charFun μ u‖ ≤ Real.exp (-c * min (u ^ 2) 1 * V)) :
    μ.real {x : ℝ | |x| ≤ δ} ≤ Real.exp (1 / 2) *
      (Real.sqrt (Real.pi / (c * V / δ ^ 2)) + Real.exp (-c * V) +
        2 * Real.exp (-(δ * T) ^ 2 / 2)) := by
  classical
  let γ := gaussianReal 0 1
  let E : Set ℝ := {u | δ * T < |u|}
  let a := c * V / δ ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have hE : MeasurableSet E := by measurability
  have hpoint (u : ℝ) : ‖charFun μ (u / δ)‖ ≤
      Real.exp (-a * u ^ 2) + Real.exp (-c * V) + E.indicator (fun _ ↦ (1 : ℝ)) u := by
    by_cases hu : u ∈ E
    · rw [Set.indicator_of_mem hu]
      have hnorm := norm_charFun_le_one (μ := μ) (u / δ)
      linarith [Real.exp_pos (-a * u ^ 2), Real.exp_pos (-c * V)]
    · rw [Set.indicator_of_notMem hu, add_zero]
      have harg : |u / δ| ≤ T := by
        rw [abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
        have hu' : |u| ≤ δ * T := le_of_not_gt hu
        simpa only [mul_comm] using hu'
      apply (hchar (u / δ) harg).trans
      by_cases hs : (u / δ) ^ 2 ≤ 1
      · rw [min_eq_left hs]
        have hexp : -c * (u / δ) ^ 2 * V = -a * u ^ 2 := by dsimp [a]; ring
        rw [hexp]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
      · rw [min_eq_right (le_of_not_ge hs), mul_one]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
  have hφ : Integrable (fun u : ℝ ↦ ‖charFun μ (u / δ)‖) γ := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    exact Filter.Eventually.of_forall fun u ↦ by
      simpa only [norm_norm] using norm_charFun_le_one (μ := μ) (u / δ)
  have hg : Integrable (fun u : ℝ ↦ Real.exp (-a * u ^ 2)) γ := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) (by fun_prop)
    exact Filter.Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le)
        (sq_nonneg u))
  have he := integrable_const (μ := γ) (Real.exp (-c * V))
  have hi := (integrable_const (μ := γ) (1 : ℝ)).indicator hE
  have hge : Integrable (fun u : ℝ ↦ Real.exp (-a * u ^ 2) + Real.exp (-c * V)) γ := hg.add he
  have hint := integral_mono hφ (hge.add hi) hpoint
  simp only [Pi.add_apply] at hint
  rw [integral_add hge hi, integral_add hg he, integral_const,
    integral_indicator_const _ hE] at hint
  simp [γ] at hint
  have htail : γ.real E ≤ 2 * Real.exp (-(δ * T) ^ 2 / 2) := by
    apply (measureReal_mono (μ := γ)
      (show E ⊆ {u : ℝ | δ * T ≤ |u|} from by
        intro u hu
        change δ * T < |u| at hu
        exact hu.le)).trans
    exact standardGaussian_abs_tail (mul_nonneg hδ.le hT)
  have hgint := integral_standardGaussian_exp_neg_sq_le ha
  apply (smallBall_le_charFun_gaussian μ hδ).trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact hint.trans (add_le_add (add_le_add (by simpa only [neg_mul] using hgint)
    (by simp only [neg_mul, le_refl])) htail)

theorem geometricVariance_succ_pos (x : ℝ) (n : ℕ) : 0 < geometricVariance x (n + 1) := by
  have h := geometricVariance_mono x (show 1 ≤ n + 1 by omega)
  have h₁ : (1 : ℝ) ≤ geometricVariance x (n + 1) := by
    simpa [geometricVariance] using h
  linarith

/-- An unconditional quantitative anti-concentration bound for the polynomial
at every point `x` between `1/2` and `1`. -/
theorem powerSum_smallBall (n L : ℕ) (hL : 2 * L ≤ n + 1)
    {x δ : ℝ} (hx₀ : 1 / 2 ≤ x) (hx₁ : x ≤ 1) (hδ : 0 < δ) :
    let c : ℝ := 1 / (4 * Real.pi ^ 2)
    sequenceLaw.real {ε | |powerSum ε (n + 1) x| ≤ δ} ≤ Real.exp (1 / 2) *
      (Real.sqrt (Real.pi / (c * geometricVariance x (n + 1) / δ ^ 2)) +
        Real.exp (-c * geometricVariance x (n + 1)) +
        2 * Real.exp (-(δ * (x ^ L)⁻¹) ^ 2 / 2)) := by
  dsimp only
  have hmeas : Measurable (fun ε : ℕ → ℝ ↦ powerSum ε (n + 1) x) := by
    exact Finset.measurable_sum _ fun k _ ↦ (measurable_pi_apply k).mul_const _
  let μ := sequenceLaw.map (fun ε ↦ powerSum ε (n + 1) x)
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have hxpos : 0 < x := by linarith
  have hchar (u : ℝ) (hu : |u| ≤ (x ^ L)⁻¹) :
      ‖charFun μ u‖ ≤ Real.exp (-(1 / (4 * Real.pi ^ 2)) * min (u ^ 2) 1 *
        geometricVariance x (n + 1)) := by
    apply norm_charFun_powerSum_gaussian_bound n L hL hx₀ hx₁
    exact (mul_le_mul_of_nonneg_right hu (pow_pos hxpos L).le).trans_eq
      (inv_mul_cancel₀ (pow_ne_zero L hxpos.ne'))
  have hbound := smallBall_of_charFun_bound μ (by positivity : 0 < 1 / (4 * Real.pi ^ 2))
    (geometricVariance_succ_pos x n) (by positivity : 0 ≤ (x ^ L)⁻¹) hδ hchar
  change (sequenceLaw.map (fun ε ↦ powerSum ε (n + 1) x)).real _ ≤ _ at hbound
  rw [map_measureReal_apply hmeas (by measurability)] at hbound
  exact hbound

end Erdos521
