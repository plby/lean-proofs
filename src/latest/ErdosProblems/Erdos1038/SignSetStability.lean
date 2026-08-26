import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite



/-!
# Stability of strict sign sets under convergence in measure

If real-valued measurable functions converge in measure and the limiting
function is nonzero almost everywhere, then their strict negative sets
converge in symmetric-difference measure.  Equivalently, the corresponding
`{0, 1}`-valued indicators converge in measure and in `L¹`.
-/

open scoped ENNReal symmDiff
open Filter MeasureTheory Set Topology

namespace Erdos1038

noncomputable section

variable {α : Type*}

/-- The strict negative set of a real-valued function. -/
def negativeSet (f : α → ℝ) : Set α := {x | f x < 0}

/-- The real-valued indicator of the strict negative set. -/
def negativeIndicator (f : α → ℝ) : α → ℝ :=
  (negativeSet f).indicator fun _ ↦ 1

theorem measurableSet_negativeSet [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f) :
    MeasurableSet (negativeSet f) := by
  exact measurableSet_lt hf measurable_const

theorem stronglyMeasurable_negativeIndicator [MeasurableSpace α] {f : α → ℝ}
    (hf : Measurable f) :
    StronglyMeasurable (negativeIndicator f) := by
  exact stronglyMeasurable_const.indicator (measurableSet_negativeSet hf)

/-- If two functions have different strict signs, the value of the second
function is no larger in absolute value than their difference. -/
theorem negativeSet_symmDiff_subset_error {f g : α → ℝ} :
    negativeSet f ∆ negativeSet g ⊆ {x | |g x| ≤ |f x - g x|} := by
  intro x hx
  rw [symmDiff_def] at hx
  rcases hx with hx | hx
  · have hf_neg : f x < 0 := hx.1
    have hg_nonneg : 0 ≤ g x := le_of_not_gt hx.2
    change |g x| ≤ |f x - g x|
    rw [abs_of_nonneg hg_nonneg,
      abs_of_nonpos (sub_nonpos.mpr (hf_neg.le.trans hg_nonneg))]
    linarith
  · have hg_neg : g x < 0 := hx.1
    have hf_nonneg : 0 ≤ f x := le_of_not_gt hx.2
    change |g x| ≤ |f x - g x|
    rw [abs_of_nonpos hg_neg.le,
      abs_of_nonneg (sub_nonneg.mpr (hg_neg.le.trans hf_nonneg))]
    linarith

/-- Quantitative form of sign stability: a sign discrepancy can occur only
where the limit is small or the approximation error is large. -/
theorem negativeSet_symmDiff_subset_small_union_error {f g : α → ℝ} (δ : ℝ) :
    negativeSet f ∆ negativeSet g ⊆
      {x | |g x| ≤ δ} ∪ {x | δ ≤ |f x - g x|} := by
  intro x hx
  have hcross := negativeSet_symmDiff_subset_error hx
  rcases le_total |g x| δ with hsmall | hlarge
  · exact Or.inl hsmall
  · exact Or.inr (hlarge.trans hcross)

/-- The corresponding quantitative measure bound. -/
theorem measure_negativeSet_symmDiff_le [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (δ : ℝ) :
    μ (negativeSet f ∆ negativeSet g) ≤
      μ {x | |g x| ≤ δ} + μ {x | δ ≤ |f x - g x|} := by
  exact (measure_mono (negativeSet_symmDiff_subset_small_union_error δ)).trans
    (measure_union_le _ _)

/-- The negative-set indicator is continuous along a convergent scalar
sequence whenever the limit is nonzero. -/
theorem tendsto_negativeIndicator_apply_of_ne_zero {v : ℕ → ℝ} {a : ℝ}
    (hv : Tendsto v atTop (𝓝 a)) (ha : a ≠ 0) :
    Tendsto (fun n ↦ if v n < 0 then (1 : ℝ) else 0) atTop
      (𝓝 (if a < 0 then (1 : ℝ) else 0)) := by
  rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
  · have hev : ∀ᶠ n in atTop, v n < 0 :=
      hv.eventually (isOpen_Iio.mem_nhds ha_neg)
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [hev] with n hn
    simp [hn, ha_neg]
  · have hev : ∀ᶠ n in atTop, 0 < v n :=
      hv.eventually (isOpen_Ioi.mem_nhds ha_pos)
    refine (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [hev] with n hn
    simp [not_lt_of_ge hn.le, not_lt_of_ge ha_pos.le]

/-- Convergence in measure is stable under taking strict-negative-set
indicators, provided the limiting function vanishes only on a null set. -/
theorem tendstoInMeasure_negativeIndicator [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ]
    {u : ℕ → α → ℝ} {v : α → ℝ}
    (hu : ∀ n, Measurable (u n))
    (huv : TendstoInMeasure μ u atTop v)
    (hv_zero : μ {x | v x = 0} = 0) :
    TendstoInMeasure μ (fun n ↦ negativeIndicator (u n)) atTop
      (negativeIndicator v) := by
  rw [exists_seq_tendstoInMeasure_atTop_iff
    (fun n ↦ (stronglyMeasurable_negativeIndicator (hu n)).aestronglyMeasurable)]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := (huv.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ns', hns', ?_⟩
  have hv_ne : ∀ᵐ x ∂μ, v x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_ne_iff] using! hv_zero
  filter_upwards [hae, hv_ne] with x hx hx0
  simpa only [negativeIndicator, negativeSet, Set.indicator_apply,
    Set.mem_ofPred_eq, Pi.one_apply, Function.comp_def] using!
    tendsto_negativeIndicator_apply_of_ne_zero hx hx0

/-- For negative-set indicators, the distance threshold `1` detects exactly
the symmetric difference of the underlying sets. -/
theorem one_le_edist_negativeIndicator_iff {f g : α → ℝ} {x : α} :
    (1 : ℝ≥0∞) ≤ edist (negativeIndicator f x) (negativeIndicator g x) ↔
      x ∈ negativeSet f ∆ negativeSet g := by
  by_cases hf : x ∈ negativeSet f <;> by_cases hg : x ∈ negativeSet g <;>
    simp [negativeIndicator, hf, hg, symmDiff_def]

/-- The strict negative sets converge in symmetric-difference measure. -/
theorem tendsto_measure_negativeSet_symmDiff [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ]
    {u : ℕ → α → ℝ} {v : α → ℝ}
    (hu : ∀ n, Measurable (u n))
    (huv : TendstoInMeasure μ u atTop v)
    (hv_zero : μ {x | v x = 0} = 0) :
    Tendsto (fun n ↦ μ (negativeSet (u n) ∆ negativeSet v)) atTop (𝓝 0) := by
  have hind := tendstoInMeasure_negativeIndicator hu huv hv_zero
  simpa only [one_le_edist_negativeIndicator_iff, Set.ofPred_mem_eq] using!
    hind (1 : ℝ≥0∞) (by simp)

/-- The `L¹` seminorm distance between two negative-set indicators is
exactly the measure of the symmetric difference. -/
theorem eLpNorm_one_negativeIndicator_sub_eq [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    eLpNorm (negativeIndicator f - negativeIndicator g) 1 μ =
      μ (negativeSet f ∆ negativeSet g) := by
  simp only [negativeIndicator]
  rw [eLpNorm_indicator_sub_indicator]
  rw [eLpNorm_indicator_const
    ((measurableSet_negativeSet hf).symmDiff (measurableSet_negativeSet hg))
    (by simp) (by simp)]
  simp

/-- The negative-set indicators converge in the `L¹` seminorm. -/
theorem tendsto_eLpNorm_one_negativeIndicator_sub [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ]
    {u : ℕ → α → ℝ} {v : α → ℝ}
    (hu : ∀ n, Measurable (u n)) (hv : Measurable v)
    (huv : TendstoInMeasure μ u atTop v)
    (hv_zero : μ {x | v x = 0} = 0) :
    Tendsto
      (fun n ↦ eLpNorm (negativeIndicator (u n) - negativeIndicator v) 1 μ)
      atTop (𝓝 0) := by
  have hsymm := tendsto_measure_negativeSet_symmDiff hu huv hv_zero
  have heq :
      (fun n ↦ eLpNorm (negativeIndicator (u n) - negativeIndicator v) 1 μ) =
        fun n ↦ μ (negativeSet (u n) ∆ negativeSet v) := by
    funext n
    exact eLpNorm_one_negativeIndicator_sub_eq (hu n) hv
  rw [heq]
  exact hsymm

/-- In particular, the real-valued measures of the negative sets converge. -/
theorem tendsto_measureReal_negativeSet [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ]
    {u : ℕ → α → ℝ} {v : α → ℝ}
    (hu : ∀ n, Measurable (u n)) (hv : Measurable v)
    (huv : TendstoInMeasure μ u atTop v)
    (hv_zero : μ {x | v x = 0} = 0) :
    Tendsto (fun n ↦ μ.real (negativeSet (u n))) atTop
      (𝓝 (μ.real (negativeSet v))) := by
  have hsymm := tendsto_measure_negativeSet_symmDiff hu huv hv_zero
  have hsymm_real :
      Tendsto (fun n ↦ μ.real (negativeSet (u n) ∆ negativeSet v)) atTop (𝓝 0) := by
    simpa only [measureReal_def, Function.comp_def, ENNReal.toReal_zero] using!
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsymm
  rw [← tendsto_sub_nhds_zero_iff, tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
    (Eventually.of_forall fun n ↦ ?_) hsymm_real
  simpa only [Real.norm_eq_abs] using!
    abs_measureReal_sub_le_measureReal_symmDiff
      (measurableSet_negativeSet (hu n)).nullMeasurableSet
      (measurableSet_negativeSet hv).nullMeasurableSet

/-- The same convergence expressed in Mathlib's native `ℝ≥0∞`-valued
measure. -/
theorem tendsto_measure_negativeSet [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ]
    {u : ℕ → α → ℝ} {v : α → ℝ}
    (hu : ∀ n, Measurable (u n)) (hv : Measurable v)
    (huv : TendstoInMeasure μ u atTop v)
    (hv_zero : μ {x | v x = 0} = 0) :
    Tendsto (fun n ↦ μ (negativeSet (u n))) atTop
      (𝓝 (μ (negativeSet v))) := by
  apply (ENNReal.tendsto_toReal_iff (fun n ↦ measure_ne_top μ _) (measure_ne_top μ _)).mp
  simpa only [measureReal_def] using!
    tendsto_measureReal_negativeSet hu hv huv hv_zero

end

end Erdos1038
