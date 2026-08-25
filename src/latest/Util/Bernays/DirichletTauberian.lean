import Util.Bernays.HalfPowerTauberian
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Analysis.PSeries

/-!
# The half-power Tauberian theorem for arithmetic Dirichlet series

The logarithmic atomic measure has mass `a(n)/n` at `log n`. Its Laplace
transform is the real Dirichlet series at `1+s`; its cumulative mass is the
exact reciprocal partial sum, including all endpoint conventions.
-/

open MeasureTheory Filter Topology Real
open scoped NNReal ENNReal

namespace Bernays

noncomputable def realDirichlet (a : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑' n : ℕ, a (n + 1) / ((n + 1 : ℕ) : ℝ) ^ z

noncomputable def reciprocalSum (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, a (n + 1) / ((n + 1 : ℕ) : ℝ)

noncomputable def logAtom (n : ℕ) : ℝ≥0 :=
  ⟨log ((n + 1 : ℕ) : ℝ), log_natCast_nonneg _⟩

noncomputable def logarithmicMeasure (a : ℕ → ℝ) : Measure ℝ≥0 :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (a (n + 1) / ((n + 1 : ℕ) : ℝ)) • Measure.dirac (logAtom n)

theorem logarithmicMeasure_integral {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (f : ℝ≥0 → ℝ) :
    (∫ y, f y ∂logarithmicMeasure a) =
      ∑' n : ℕ, a (n + 1) / ((n + 1 : ℕ) : ℝ) * f (logAtom n) := by
  rw [logarithmicMeasure, integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro n
  rw [ENNReal.toReal_ofReal (div_nonneg (ha _) (by positivity)), smul_eq_mul]

theorem weighted_exponential_eq_dirichletTerm (b x s : ℝ) (hx : 0 < x) :
    b / x * exp (-s * log x) = b / x ^ (1 + s) := by
  rw [rpow_add hx, rpow_one, rpow_def_of_pos hx,
    show -s * log x = -(log x * s) by ring, exp_neg]
  ring

theorem logarithmicMeasure_laplace {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (s : ℝ) :
    laplace (logarithmicMeasure a) s = realDirichlet a (1 + s) := by
  rw [laplace, logarithmicMeasure_integral ha]
  apply tsum_congr
  intro n
  exact weighted_exponential_eq_dirichletTerm _ _ _ (by positivity)

theorem logarithmicMeasure_exp_integrable {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (s : ℝ)
    (h : Summable (fun n : ℕ => a (n + 1) / ((n + 1 : ℕ) : ℝ) ^ (1 + s))) :
    Integrable (fun y : ℝ≥0 => exp (-s * y)) (logarithmicMeasure a) := by
  apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
  convert h using 1
  ext n
  rw [ENNReal.toReal_ofReal (div_nonneg (ha _) (by positivity)),
    Real.norm_of_nonneg (exp_pos _).le]
  exact weighted_exponential_eq_dirichletTerm _ _ _ (by positivity)

theorem logAtom_mem_cutoff_iff (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (logAtom n : ℝ) ≤ log x ↔ n < ⌊x⌋₊ := by
  change log ((n + 1 : ℕ) : ℝ) ≤ log x ↔ _
  rw [log_le_log_iff (by positivity) hx, Nat.lt_iff_add_one_le, Nat.le_floor_iff hx.le]

theorem logarithmicMeasure_cutoff {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    {x : ℝ} (hx : 0 < x) :
    (logarithmicMeasure a).real {y : ℝ≥0 | (y : ℝ) ≤ log x} = reciprocalSum a ⌊x⌋₊ := by
  classical
  let S : Set ℝ≥0 := {y | (y : ℝ) ≤ log x}
  have hS : MeasurableSet S := measurableSet_le NNReal.continuous_coe.measurable measurable_const
  have hmem (n : ℕ) : logAtom n ∈ S ↔ n ∈ Finset.range ⌊x⌋₊ := by
    exact (logAtom_mem_cutoff_iff n hx).trans Finset.mem_range.symm
  change (logarithmicMeasure a).real S = _
  rw [← integral_indicator_one hS, logarithmicMeasure_integral ha]
  rw [tsum_eq_sum (s := Finset.range ⌊x⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Set.indicator_of_mem ((hmem n).mpr hn), Pi.one_apply, mul_one]
  · intro n hn
    rw [Set.indicator_of_notMem (fun h => hn ((hmem n).mp h)), mul_zero]

theorem summable_realDirichletTerm_of_bounded {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) {z : ℝ} (hz : 1 < z) :
    Summable (fun n : ℕ => a (n + 1) / ((n + 1 : ℕ) : ℝ) ^ z) := by
  have hp := (summable_one_div_nat_rpow.mpr hz).comp_injective
    (fun n m h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
  apply Summable.of_nonneg_of_le (fun n => div_nonneg (ha _) (by positivity)) _ hp
  intro n
  exact div_le_div_of_nonneg_right (ha₁ _) (by positivity)

theorem reciprocalSum_div_sqrt_log_tendsto {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (ha₁ : ∀ n, a n ≤ 1) {C : ℝ} (hC : 0 < C)
    (hD : Tendsto (fun s : ℝ => sqrt s * realDirichlet a (1 + s))
      (𝓝[Set.Ioi 0] 0) (𝓝 C)) :
    Tendsto (fun x : ℝ => reciprocalSum a ⌊x⌋₊ / sqrt (log x)) atTop
      (𝓝 (2 * C / sqrt π)) := by
  let s : ℝ → ℝ := fun x => (log (max 2 x))⁻¹
  have hs (x : ℝ) : 0 < s x :=
    inv_pos.mpr (log_pos (lt_of_lt_of_le (by norm_num) (le_max_left 2 x)))
  have hmax : Tendsto (fun x : ℝ => max 2 x) atTop atTop :=
    tendsto_atTop_mono (fun x => le_max_right 2 x) tendsto_id
  have hs₀ : Tendsto s atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_log_atTop.comp hmax)
  have hint (t : ℝ) (ht : 0 < t) :
      Integrable (fun y : ℝ≥0 => exp (-t * y)) (logarithmicMeasure a) :=
    logarithmicMeasure_exp_integrable ha t
      (summable_realDirichletTerm_of_bounded ha ha₁ (by linarith))
  have hL : Tendsto (fun t : ℝ => sqrt t * laplace (logarithmicMeasure a) t)
      (𝓝[Set.Ioi 0] 0) (𝓝 C) := by
    simpa only [logarithmicMeasure_laplace ha] using hD
  have ht := halfPowerTauberian (logarithmicMeasure a) hint hC hL s hs hs₀
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  dsimp only [s]
  rw [max_eq_right hx, inv_inv, logarithmicMeasure_cutoff ha (by linarith : 0 < x), sqrt_inv]
  ring

end Bernays
