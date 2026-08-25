import Util.Bernays.Moments
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Passing compact moment convergence through a cutoff

Continuous ramps above and below a cutoff allow its integral to pass to the
limit whenever the limiting measure has no atom at the cutoff.
-/

open MeasureTheory Filter Topology
open scoped unitInterval

namespace Bernays

theorem integral_tendsto_of_continuous_sandwich {ι : Type*} {l : Filter ι}
    {μ : ι → FiniteMeasure I} {ν : FiniteMeasure I}
    (hμ : ∀ g : C(I, ℝ), Tendsto (fun i => ∫ x, g x ∂(μ i : Measure I)) l
      (𝓝 (∫ x, g x ∂(ν : Measure I))))
    {f : I → ℝ} (hf : ∀ i, Integrable f (μ i : Measure I))
    (L U : ℕ → C(I, ℝ)) (hL : ∀ n x, L n x ≤ f x) (hU : ∀ n x, f x ≤ U n x)
    {c : ℝ}
    (hLc : Tendsto (fun n => ∫ x, L n x ∂(ν : Measure I)) atTop (𝓝 c))
    (hUc : Tendsto (fun n => ∫ x, U n x ∂(ν : Measure I)) atTop (𝓝 c)) :
    Tendsto (fun i => ∫ x, f x ∂(μ i : Measure I)) l (𝓝 c) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    obtain ⟨n, hn⟩ := (hLc.eventually (lt_mem_nhds hb)).exists
    filter_upwards [(hμ (L n)).eventually (lt_mem_nhds hn)] with i hi
    exact hi.trans_le (integral_mono
      ((L n).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) (hf i) (hL n))
  · intro b hb
    obtain ⟨n, hn⟩ := (hUc.eventually (gt_mem_nhds hb)).exists
    filter_upwards [(hμ (U n)).eventually (gt_mem_nhds hn)] with i hi
    exact (integral_mono (hf i)
      ((U n).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)) (hU n)).trans_lt hi

/-- A continuous approximation to the indicator of the positive half-line. -/
def ramp (n : ℕ) (t : ℝ) : ℝ := min 1 (max 0 ((n : ℝ) * t))

theorem ramp_nonneg (n : ℕ) (t : ℝ) : 0 ≤ ramp n t :=
  le_min zero_le_one (le_max_left _ _)

theorem ramp_le_one (n : ℕ) (t : ℝ) : ramp n t ≤ 1 := min_le_left _ _

theorem ramp_eq_zero_of_nonpos (n : ℕ) {t : ℝ} (ht : t ≤ 0) : ramp n t = 0 := by
  rw [ramp, max_eq_left (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) ht)]
  norm_num

theorem ramp_eq_one {n : ℕ} {t : ℝ} (ht : 1 ≤ (n : ℝ) * t) : ramp n t = 1 := by
  rw [ramp, max_eq_right (zero_le_one.trans ht), min_eq_left ht]

theorem continuous_ramp (n : ℕ) : Continuous (ramp n) := by
  unfold ramp
  fun_prop

theorem ramp_tendsto_of_pos {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => ramp n t) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop (1 / t))] with n hn
  exact (ramp_eq_one ((div_le_iff₀ ht).mp hn)).symm

def lowerCutoff (g : C(I, ℝ)) (a : ℝ) (n : ℕ) : C(I, ℝ) where
  toFun x := g x * ramp n ((x : ℝ) - a)
  continuous_toFun := g.continuous.mul
    ((continuous_ramp n).comp (continuous_subtype_val.sub continuous_const))

def upperCutoff (g : C(I, ℝ)) (a : ℝ) (n : ℕ) : C(I, ℝ) where
  toFun x := g x * (1 - ramp n (a - (x : ℝ)))
  continuous_toFun := g.continuous.mul
    (continuous_const.sub ((continuous_ramp n).comp (continuous_const.sub continuous_subtype_val)))

noncomputable def cutoff (g : C(I, ℝ)) (a : ℝ) (x : I) : ℝ :=
  if a ≤ (x : ℝ) then g x else 0

theorem lowerCutoff_le_cutoff {g : C(I, ℝ)} (hg : ∀ x, 0 ≤ g x) (a : ℝ) (n : ℕ) (x : I) :
    lowerCutoff g a n x ≤ cutoff g a x := by
  change g x * ramp n ((x : ℝ) - a) ≤ if a ≤ (x : ℝ) then g x else 0
  split_ifs with hx
  · exact (mul_le_mul_of_nonneg_left (ramp_le_one _ _) (hg x)).trans_eq (mul_one _)
  · rw [ramp_eq_zero_of_nonpos n (by linarith : (x : ℝ) - a ≤ 0), mul_zero]

theorem cutoff_le_upperCutoff {g : C(I, ℝ)} (hg : ∀ x, 0 ≤ g x) (a : ℝ) (n : ℕ) (x : I) :
    cutoff g a x ≤ upperCutoff g a n x := by
  change (if a ≤ (x : ℝ) then g x else 0) ≤ g x * (1 - ramp n (a - (x : ℝ)))
  split_ifs with hx
  · rw [ramp_eq_zero_of_nonpos n (sub_nonpos.mpr hx), sub_zero, mul_one]
  · exact mul_nonneg (hg x) (sub_nonneg.mpr (ramp_le_one _ _))

theorem lowerCutoff_tendsto {g : C(I, ℝ)} {a : ℝ} {x : I} (hx : (x : ℝ) ≠ a) :
    Tendsto (fun n => lowerCutoff g a n x) atTop (𝓝 (cutoff g a x)) := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · simp only [lowerCutoff, ContinuousMap.coe_mk,
      ramp_eq_zero_of_nonpos _ (sub_nonpos.mpr hx.le), mul_zero,
      cutoff, if_neg (not_le.mpr hx)]
    exact tendsto_const_nhds
  · have h := (ramp_tendsto_of_pos (sub_pos.mpr hx)).const_mul (g x)
    simpa only [mul_one, lowerCutoff, ContinuousMap.coe_mk, cutoff, if_pos hx.le] using h

theorem upperCutoff_tendsto {g : C(I, ℝ)} {a : ℝ} {x : I} (hx : (x : ℝ) ≠ a) :
    Tendsto (fun n => upperCutoff g a n x) atTop (𝓝 (cutoff g a x)) := by
  rcases lt_or_gt_of_ne hx with hx | hx
  · have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (ramp_tendsto_of_pos (sub_pos.mpr hx))).const_mul (g x)
    simpa only [sub_self, mul_zero, upperCutoff, ContinuousMap.coe_mk,
      cutoff, if_neg (not_le.mpr hx)] using h
  · simp only [upperCutoff, ContinuousMap.coe_mk,
      ramp_eq_zero_of_nonpos _ (sub_nonpos.mpr hx.le), sub_zero, mul_one,
      cutoff, if_pos hx.le]
    exact tendsto_const_nhds

theorem cutoff_integrable (μ : FiniteMeasure I) (g : C(I, ℝ)) (a : ℝ) :
    Integrable (cutoff g a) (μ : Measure I) := by
  have h := g.continuous.integrable_of_hasCompactSupport
    (μ := (μ : Measure I)) (HasCompactSupport.of_compactSpace g)
  exact h.indicator (measurableSet_le measurable_const continuous_subtype_val.measurable)

private theorem norm_mul_le_norm (g : C(I, ℝ)) (x : I) {r : ℝ}
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1) : ‖g x * r‖ ≤ ‖g‖ := by
  rw [norm_mul, Real.norm_of_nonneg hr₀]
  exact (mul_le_mul (g.norm_coe_le_norm x) hr₁ hr₀ (norm_nonneg g)).trans_eq (mul_one _)

theorem norm_lowerCutoff_le (g : C(I, ℝ)) (a : ℝ) (n : ℕ) (x : I) :
    ‖lowerCutoff g a n x‖ ≤ ‖g‖ :=
  norm_mul_le_norm g x (ramp_nonneg _ _) (ramp_le_one _ _)

theorem norm_upperCutoff_le (g : C(I, ℝ)) (a : ℝ) (n : ℕ) (x : I) :
    ‖upperCutoff g a n x‖ ≤ ‖g‖ :=
  norm_mul_le_norm g x (sub_nonneg.mpr (ramp_le_one _ _))
    (by linarith [ramp_nonneg n (a - (x : ℝ))])

theorem cutoff_integral_tendsto_of_moments {ι : Type*} {l : Filter ι}
    {μ : ι → FiniteMeasure I} {ν : FiniteMeasure I}
    (h : ∀ k : ℕ, Tendsto (fun i => ∫ x : I, (x : ℝ) ^ k ∂(μ i : Measure I)) l
      (𝓝 (∫ x : I, (x : ℝ) ^ k ∂(ν : Measure I))))
    (g : C(I, ℝ)) (hg : ∀ x, 0 ≤ g x) (a : ℝ)
    (hν : (ν : Measure I) {x : I | (x : ℝ) = a} = 0) :
    Tendsto (fun i => ∫ x, cutoff g a x ∂(μ i : Measure I)) l
      (𝓝 (∫ x, cutoff g a x ∂(ν : Measure I))) := by
  have hne : ∀ᵐ (x : I) ∂(ν : Measure I), (x : ℝ) ≠ a := by
    simpa only [ae_iff, not_not] using hν
  apply integral_tendsto_of_continuous_sandwich
    (continuous_integral_tendsto_of_moments h)
    (fun i => cutoff_integrable (μ i) g a)
    (lowerCutoff g a) (upperCutoff g a)
    (lowerCutoff_le_cutoff hg a) (cutoff_le_upperCutoff hg a)
  · apply tendsto_integral_of_dominated_convergence (fun _ : I => ‖g‖)
    · intro n
      exact (lowerCutoff g a n).continuous.aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Filter.Eventually.of_forall (norm_lowerCutoff_le g a n)
    · exact hne.mono fun _ hx => lowerCutoff_tendsto hx
  · apply tendsto_integral_of_dominated_convergence (fun _ : I => ‖g‖)
    · intro n
      exact (upperCutoff g a n).continuous.aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Filter.Eventually.of_forall (norm_upperCutoff_le g a n)
    · exact hne.mono fun _ hx => upperCutoff_tendsto hx

end Bernays
