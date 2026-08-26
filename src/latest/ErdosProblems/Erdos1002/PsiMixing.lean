import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# From event ψ-mixing to covariance bounds

This file isolates the measure-theoretic bridge used after the continued-fraction
mixing estimate.  `EventRelativeMixing` is the event form of ψ-mixing for two
sub-σ-algebras.  The proof first treats nonnegative simple functions by expanding
over their measurable fibres.  General nonnegative functions are obtained from
the monotone `SimpleFunc.eapprox` approximation, including the limiting and
product-integrability arguments.  Signed real and complex functions then follow
by positive/negative and real/imaginary decompositions.
-/

open Filter MeasureTheory Set
open scoped ENNReal Topology ComplexConjugate

namespace Erdos1002

noncomputable section

variable {Ω : Type*}

/-- Event-level relative mixing for two sub-σ-algebras.  The ambient measurable
space is the typeclass argument `m₀`; `m₁` and `m₂` are kept explicit so that
measurability hypotheses cannot silently use the wrong σ-algebra. -/
def EventRelativeMixing (m₁ m₂ : MeasurableSpace Ω) [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) (ε : ℝ) : Prop :=
  ∀ A B, @MeasurableSet Ω m₁ A → @MeasurableSet Ω m₂ B →
    |μ.real (A ∩ B) - μ.real A * μ.real B| ≤
      ε * μ.real A * μ.real B

private theorem integral_simpleFunc_mul_eq_double_sum
    [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f g : SimpleFunc Ω ℝ) :
    (∫ ω, f ω * g ω ∂μ) =
      ∑ x ∈ f.range, ∑ y ∈ g.range,
        x * y * μ.real (f ⁻¹' {x} ∩ g ⁻¹' {y}) := by
  classical
  have hp (ω : Ω) :
      f ω * g ω =
        ∑ x ∈ f.range, ∑ y ∈ g.range,
          (f ⁻¹' {x} ∩ g ⁻¹' {y}).indicator (fun _ => x * y) ω := by
    rw [Finset.sum_eq_single (f ω)]
    · rw [Finset.sum_eq_single (g ω)]
      · rw [indicator_of_mem]
        exact ⟨rfl, rfl⟩
      · intro y hy hyne
        rw [indicator_of_notMem]
        exact fun h => hyne h.2.symm
      · exact fun h => (h (SimpleFunc.mem_range_self g ω)).elim
    · intro x hx hxne
      apply Finset.sum_eq_zero
      intro y hy
      rw [indicator_of_notMem]
      exact fun h => hxne h.1.symm
    · exact fun h => (h (SimpleFunc.mem_range_self f ω)).elim
  rw [integral_congr_ae (ae_of_all _ hp)]
  have hInt (x y : ℝ) : Integrable
      ((f ⁻¹' {x} ∩ g ⁻¹' {y}).indicator (fun _ : Ω => x * y)) μ :=
    (integrable_const (x * y)).indicator
      ((f.measurableSet_preimage {x}).inter (g.measurableSet_preimage {y}))
  rw [integral_finset_sum f.range (fun x hx =>
    integrable_finset_sum g.range (fun y hy => hInt x y))]
  congr 1
  ext x
  rw [integral_finset_sum g.range (fun y hy => hInt x y)]
  congr 1
  ext y
  rw [integral_indicator]
  · simp [measureReal_def]
    ring
  · exact (f.measurableSet_preimage {x}).inter (g.measurableSet_preimage {y})

/-- The event estimate expanded over the fibres of two nonnegative simple
functions.  This is the finite combinatorial core of the bridge. -/
theorem EventRelativeMixing.covariance_simple_nonneg
    (m₁ m₂ : MeasurableSpace Ω) [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ε : ℝ)
    (hmix : EventRelativeMixing m₁ m₂ μ ε)
    (f g : SimpleFunc Ω ℝ) (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hfM : ∀ x, @MeasurableSet Ω m₁ (f ⁻¹' {x}))
    (hgM : ∀ y, @MeasurableSet Ω m₂ (g ⁻¹' {y})) :
    |(∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ| ≤
      ε * (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ := by
  classical
  rw [integral_simpleFunc_mul_eq_double_sum μ f g,
    SimpleFunc.integral_eq_sum f hfi, SimpleFunc.integral_eq_sum g hgi]
  simp only [smul_eq_mul]
  have hrewrite :
      (∑ x ∈ f.range, ∑ y ∈ g.range,
          x * y * μ.real (f ⁻¹' {x} ∩ g ⁻¹' {y})) -
        (∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * x) *
          ∑ y ∈ g.range, μ.real (g ⁻¹' {y}) * y =
      ∑ x ∈ f.range, ∑ y ∈ g.range, x * y *
        (μ.real (f ⁻¹' {x} ∩ g ⁻¹' {y}) -
          μ.real (f ⁻¹' {x}) * μ.real (g ⁻¹' {y})) := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext x
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext y
    ring
  rw [hrewrite]
  calc
    |∑ x ∈ f.range, ∑ y ∈ g.range, x * y *
        (μ.real (f ⁻¹' {x} ∩ g ⁻¹' {y}) -
          μ.real (f ⁻¹' {x}) * μ.real (g ⁻¹' {y}))| ≤
        ∑ x ∈ f.range, ∑ y ∈ g.range,
          |x * y * (μ.real (f ⁻¹' {x} ∩ g ⁻¹' {y}) -
            μ.real (f ⁻¹' {x}) * μ.real (g ⁻¹' {y}))| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans <|
        Finset.sum_le_sum fun x hx => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ f.range, ∑ y ∈ g.range,
        ε * (μ.real (f ⁻¹' {x}) * x) * (μ.real (g ⁻¹' {y}) * y) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro y hy
      have hx0 : 0 ≤ x := by
        rw [SimpleFunc.mem_range] at hx
        rcases hx with ⟨ω, rfl⟩
        exact hf0 ω
      have hy0 : 0 ≤ y := by
        rw [SimpleFunc.mem_range] at hy
        rcases hy with ⟨ω, rfl⟩
        exact hg0 ω
      rw [abs_mul, abs_of_nonneg (mul_nonneg hx0 hy0)]
      calc
        x * y * |μ.real (f ⁻¹' {x} ∩ g ⁻¹' {y}) -
            μ.real (f ⁻¹' {x}) * μ.real (g ⁻¹' {y})| ≤
            x * y * (ε * μ.real (f ⁻¹' {x}) * μ.real (g ⁻¹' {y})) := by
          gcongr
          exact hmix _ _ (hfM x) (hgM y)
        _ = ε * (μ.real (f ⁻¹' {x}) * x) *
            (μ.real (g ⁻¹' {y}) * y) := by ring
    _ = ε * (∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * x) *
        ∑ y ∈ g.range, μ.real (g ⁻¹' {y}) * y := by
      calc
        (∑ x ∈ f.range, ∑ y ∈ g.range,
            ε * (μ.real (f ⁻¹' {x}) * x) * (μ.real (g ⁻¹' {y}) * y)) =
            ∑ x ∈ f.range, (ε * (μ.real (f ⁻¹' {x}) * x)) *
              ∑ y ∈ g.range, μ.real (g ⁻¹' {y}) * y := by
          congr 1
          ext x
          rw [Finset.mul_sum]
        _ = (∑ x ∈ f.range, ε * (μ.real (f ⁻¹' {x}) * x)) *
              ∑ y ∈ g.range, μ.real (g ⁻¹' {y}) * y := by
          rw [Finset.sum_mul]
        _ = ε * (∑ x ∈ f.range, μ.real (f ⁻¹' {x}) * x) *
              ∑ y ∈ g.range, μ.real (g ⁻¹' {y}) * y := by
          congr 1
          rw [Finset.mul_sum]


private noncomputable def eapproxReal [m : MeasurableSpace Ω]
    (f : Ω → ℝ) (n : ℕ) : SimpleFunc Ω ℝ :=
  (SimpleFunc.eapprox (fun ω => ENNReal.ofReal (f ω)) n).map ENNReal.toReal

private lemma eapproxReal_apply [m : MeasurableSpace Ω]
    (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    eapproxReal f n ω =
      ENNReal.toReal (SimpleFunc.eapprox (fun z => ENNReal.ofReal (f z)) n ω) := rfl

private lemma eapproxReal_nonneg [m : MeasurableSpace Ω]
    (f : Ω → ℝ) (n : ℕ) : 0 ≤ eapproxReal f n := by
  intro ω
  rw [eapproxReal_apply]
  exact ENNReal.toReal_nonneg

private lemma eapproxReal_mono [m : MeasurableSpace Ω]
    (f : Ω → ℝ) : Monotone (fun n => (eapproxReal f n : Ω → ℝ)) := by
  intro n k hnk ω
  simp only [eapproxReal_apply]
  apply ENNReal.toReal_mono
  · exact ne_of_lt (SimpleFunc.eapprox_lt_top _ _ _)
  · exact SimpleFunc.monotone_eapprox _ hnk ω

private lemma eapproxReal_le [m : MeasurableSpace Ω]
    {f : Ω → ℝ} (hfM : Measurable f) (hf0 : 0 ≤ f) (n : ℕ) :
    (eapproxReal f n : Ω → ℝ) ≤ f := by
  intro ω
  rw [eapproxReal_apply, ← ENNReal.toReal_ofReal (hf0 ω)]
  apply ENNReal.toReal_mono
  · simp
  · calc
      _ ≤ ⨆ k, SimpleFunc.eapprox (fun z => ENNReal.ofReal (f z)) k ω :=
        le_iSup (fun k => SimpleFunc.eapprox (fun z => ENNReal.ofReal (f z)) k ω) n
      _ = _ := SimpleFunc.iSup_eapprox_apply (ENNReal.measurable_ofReal.comp hfM) ω

private lemma eapproxReal_tendsto [m : MeasurableSpace Ω]
    {f : Ω → ℝ} (hfM : Measurable f) (hf0 : 0 ≤ f) (ω : Ω) :
    Tendsto (fun n => eapproxReal f n ω) atTop (𝓝 (f ω)) := by
  simp only [eapproxReal_apply]
  convert! (ENNReal.continuousAt_toReal (by simp)).tendsto.comp
    (SimpleFunc.tendsto_eapprox (ENNReal.measurable_ofReal.comp hfM) ω) using 1
  all_goals simp [ENNReal.toReal_ofReal (hf0 ω)]

theorem EventRelativeMixing.covariance_nonneg
    (m₁ m₂ : MeasurableSpace Ω) [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ε : ℝ) (hε : 0 ≤ ε)
    (hm₁ : m₁ ≤ m₀) (hm₂ : m₂ ≤ m₀)
    (hmix : EventRelativeMixing m₁ m₂ μ ε)
    {f g : Ω → ℝ}
    (hfM : @Measurable Ω ℝ m₁ (borel ℝ) f)
    (hgM : @Measurable Ω ℝ m₂ (borel ℝ) g)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hf0 : 0 ≤ f) (hg0 : 0 ≤ g) :
    Integrable (fun ω => f ω * g ω) μ ∧
      |(∫ ω, f ω * g ω ∂μ) -
          (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ| ≤
        ε * (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ := by
  let fs (n : ℕ) : @SimpleFunc Ω m₁ ℝ := @eapproxReal Ω m₁ f n
  let gs (n : ℕ) : @SimpleFunc Ω m₂ ℝ := @eapproxReal Ω m₂ g n
  let F (n : ℕ) : @SimpleFunc Ω m₀ ℝ := (fs n).toLargerSpace hm₁
  let G (n : ℕ) : @SimpleFunc Ω m₀ ℝ := (gs n).toLargerSpace hm₂
  have hFM0 : @Measurable Ω ℝ m₀ (borel ℝ) f := hfM.mono hm₁ le_rfl
  have hGM0 : @Measurable Ω ℝ m₀ (borel ℝ) g := hgM.mono hm₂ le_rfl
  have hF0 (n : ℕ) : 0 ≤ F n := by
    simpa [F, fs, SimpleFunc.coe_toLargerSpace_eq] using!
      (@eapproxReal_nonneg Ω m₁ f n)
  have hG0 (n : ℕ) : 0 ≤ G n := by
    simpa [G, gs, SimpleFunc.coe_toLargerSpace_eq] using!
      (@eapproxReal_nonneg Ω m₂ g n)
  have hFle (n : ℕ) : (F n : Ω → ℝ) ≤ f := by
    simpa [F, fs, SimpleFunc.coe_toLargerSpace_eq] using!
      (@eapproxReal_le Ω m₁ f hfM hf0 n)
  have hGle (n : ℕ) : (G n : Ω → ℝ) ≤ g := by
    simpa [G, gs, SimpleFunc.coe_toLargerSpace_eq] using!
      (@eapproxReal_le Ω m₂ g hgM hg0 n)
  have hFmono : Monotone (fun n => (F n : Ω → ℝ)) := by
    simpa [F, fs, SimpleFunc.coe_toLargerSpace_eq] using!
      (@eapproxReal_mono Ω m₁ f)
  have hGmono : Monotone (fun n => (G n : Ω → ℝ)) := by
    simpa [G, gs, SimpleFunc.coe_toLargerSpace_eq] using!
      (@eapproxReal_mono Ω m₂ g)
  have hFtend (ω : Ω) : Tendsto (fun n => F n ω) atTop (𝓝 (f ω)) := by
    simpa [F, fs, SimpleFunc.coe_toLargerSpace_eq] using!
      (@eapproxReal_tendsto Ω m₁ f hfM hf0 ω)
  have hGtend (ω : Ω) : Tendsto (fun n => G n ω) atTop (𝓝 (g ω)) := by
    simpa [G, gs, SimpleFunc.coe_toLargerSpace_eq] using!
      (@eapproxReal_tendsto Ω m₂ g hgM hg0 ω)
  have hFint (n : ℕ) : Integrable (F n : Ω → ℝ) μ := by
    apply hfi.mono' (F n).measurable.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 n ω)]
    exact hFle n ω
  have hGint (n : ℕ) : Integrable (G n : Ω → ℝ) μ := by
    apply hgi.mono' (G n).measurable.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 n ω)]
    exact hGle n ω
  have hsimple (n : ℕ) :
      |(∫ ω, F n ω * G n ω ∂μ) -
          (∫ ω, F n ω ∂μ) * ∫ ω, G n ω ∂μ| ≤
        ε * (∫ ω, F n ω ∂μ) * ∫ ω, G n ω ∂μ := by
    apply hmix.covariance_simple_nonneg m₁ m₂ μ ε (F n) (G n)
      (hFint n) (hGint n) (hF0 n) (hG0 n)
    · intro x
      simpa [F, fs, SimpleFunc.coe_toLargerSpace_eq] using!
        (@SimpleFunc.measurableSet_preimage Ω ℝ m₁ (fs n) {x})
    · intro y
      simpa [G, gs, SimpleFunc.coe_toLargerSpace_eq] using!
        (@SimpleFunc.measurableSet_preimage Ω ℝ m₂ (gs n) {y})
  have hFGint (n : ℕ) : Integrable (fun ω => F n ω * G n ω) μ := by
    let H : SimpleFunc Ω ℝ := F n * G n
    have hi := (integrable_const (μ := μ) (1 : ℝ)).bdd_mul
      H.measurable.aestronglyMeasurable
      (c := ∑ x ∈ H.range, ‖x‖)
    have hb : ∀ᵐ ω ∂μ, ‖H ω‖ ≤ ∑ x ∈ H.range, ‖x‖ := by
      filter_upwards [] with ω
      exact Finset.single_le_sum (fun x hx => norm_nonneg x) (H.mem_range_self ω)
    have := hi hb
    simpa [H] using! this
  have hFint_nonneg (n : ℕ) : 0 ≤ ∫ ω, F n ω ∂μ :=
    integral_nonneg (hF0 n)
  have hGint_nonneg (n : ℕ) : 0 ≤ ∫ ω, G n ω ∂μ :=
    integral_nonneg (hG0 n)
  have hFint_le (n : ℕ) : (∫ ω, F n ω ∂μ) ≤ ∫ ω, f ω ∂μ :=
    integral_mono (hFint n) hfi (hFle n)
  have hGint_le (n : ℕ) : (∫ ω, G n ω ∂μ) ≤ ∫ ω, g ω ∂μ :=
    integral_mono (hGint n) hgi (hGle n)
  have hprod_int_bound (n : ℕ) :
      (∫ ω, F n ω * G n ω ∂μ) ≤
        (1 + ε) * (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ := by
    have habs := hsimple n
    have hone :
        (∫ ω, F n ω * G n ω ∂μ) -
            (∫ ω, F n ω ∂μ) * ∫ ω, G n ω ∂μ ≤
          ε * (∫ ω, F n ω ∂μ) * ∫ ω, G n ω ∂μ :=
      (le_abs_self _).trans habs
    calc
      (∫ ω, F n ω * G n ω ∂μ) ≤
          (1 + ε) * (∫ ω, F n ω ∂μ) * ∫ ω, G n ω ∂μ := by
        linarith
      _ ≤ (1 + ε) * (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ := by
        have h1e : 0 ≤ 1 + ε := by linarith
        have hfI0 : 0 ≤ ∫ ω, f ω ∂μ := integral_nonneg hf0
        have hgI0 : 0 ≤ ∫ ω, g ω ∂μ := integral_nonneg hg0
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hFint_le n) h1e)
          (hGint_le n) (hGint_nonneg n) (mul_nonneg h1e hfI0)
  have hprod0 (n : ℕ) : 0 ≤ fun ω => F n ω * G n ω := fun ω =>
    mul_nonneg (hF0 n ω) (hG0 n ω)
  have hprod_mono : Monotone (fun n ω => F n ω * G n ω) := by
    intro n k hnk ω
    exact mul_le_mul (hFmono hnk ω) (hGmono hnk ω) (hG0 n ω) (hF0 k ω)
  have hprod_tend (ω : Ω) :
      Tendsto (fun n => F n ω * G n ω) atTop (𝓝 (f ω * g ω)) :=
    (hFtend ω).mul (hGtend ω)
  have hfgM0 : Measurable (fun ω => f ω * g ω) := hFM0.mul hGM0
  have hfg0 : 0 ≤ fun ω => f ω * g ω := fun ω => mul_nonneg (hf0 ω) (hg0 ω)
  have hsup (ω : Ω) :
      (⨆ n, ENNReal.ofReal (F n ω * G n ω)) = ENNReal.ofReal (f ω * g ω) := by
    apply iSup_eq_of_tendsto
    · intro n k hnk
      exact ENNReal.ofReal_le_ofReal (hprod_mono hnk ω)
    · exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hprod_tend ω)
  have hlintegral_bound :
      (∫⁻ ω, ENNReal.ofReal (f ω * g ω) ∂μ) ≤
        ENNReal.ofReal ((1 + ε) * (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ) := by
    calc
      (∫⁻ ω, ENNReal.ofReal (f ω * g ω) ∂μ) =
          ∫⁻ ω, ⨆ n, ENNReal.ofReal (F n ω * G n ω) ∂μ := by
        apply lintegral_congr
        intro ω
        exact (hsup ω).symm
      _ = ⨆ n, ∫⁻ ω, ENNReal.ofReal (F n ω * G n ω) ∂μ := by
        apply lintegral_iSup
        · intro n
          exact ((F n).measurable.mul (G n).measurable).ennreal_ofReal
        · intro n k hnk ω
          exact ENNReal.ofReal_le_ofReal (hprod_mono hnk ω)
      _ ≤ ENNReal.ofReal ((1 + ε) * (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ) := by
        apply iSup_le
        intro n
        rw [← ofReal_integral_eq_lintegral_ofReal (hFGint n)
          (Eventually.of_forall (hprod0 n))]
        exact ENNReal.ofReal_le_ofReal (hprod_int_bound n)
  have hfgInt : Integrable (fun ω => f ω * g ω) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      hfgM0.aestronglyMeasurable (Eventually.of_forall hfg0)).mp
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlintegral_bound
  have hFtend_int : Tendsto (fun n => ∫ ω, F n ω ∂μ) atTop (𝓝 (∫ ω, f ω ∂μ)) :=
    integral_tendsto_of_tendsto_of_monotone hFint hfi
      (Eventually.of_forall fun ω => fun n k hnk => hFmono hnk ω)
      (Eventually.of_forall hFtend)
  have hGtend_int : Tendsto (fun n => ∫ ω, G n ω ∂μ) atTop (𝓝 (∫ ω, g ω ∂μ)) :=
    integral_tendsto_of_tendsto_of_monotone hGint hgi
      (Eventually.of_forall fun ω => fun n k hnk => hGmono hnk ω)
      (Eventually.of_forall hGtend)
  have hprodtend_int :
      Tendsto (fun n => ∫ ω, F n ω * G n ω ∂μ) atTop
        (𝓝 (∫ ω, f ω * g ω ∂μ)) :=
    integral_tendsto_of_tendsto_of_monotone hFGint hfgInt
      (Eventually.of_forall fun ω => fun n k hnk => hprod_mono hnk ω)
      (Eventually.of_forall hprod_tend)
  have hlhs : Tendsto (fun n =>
      |(∫ ω, F n ω * G n ω ∂μ) -
        (∫ ω, F n ω ∂μ) * ∫ ω, G n ω ∂μ|) atTop
      (𝓝 |(∫ ω, f ω * g ω ∂μ) -
        (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ|) :=
    (hprodtend_int.sub (hFtend_int.mul hGtend_int)).abs
  have hrhs : Tendsto (fun n =>
      ε * (∫ ω, F n ω ∂μ) * ∫ ω, G n ω ∂μ) atTop
      (𝓝 (ε * (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ)) :=
    (tendsto_const_nhds.mul hFtend_int).mul hGtend_int
  have hlimit :
      |(∫ ω, f ω * g ω ∂μ) -
        (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ| ≤
      ε * (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ :=
    le_of_tendsto_of_tendsto' hlhs hrhs hsimple
  exact ⟨hfgInt, hlimit⟩

private lemma measurable_posPart {m : MeasurableSpace Ω} {f : Ω → ℝ}
    (hf : Measurable f) : Measurable (fun ω => (f ω)⁺) := by
  simpa only [posPart] using! hf.max measurable_const

private lemma measurable_negPart {m : MeasurableSpace Ω} {f : Ω → ℝ}
    (hf : Measurable f) : Measurable (fun ω => (f ω)⁻) := by
  simpa only [negPart] using! hf.neg.max measurable_const

private lemma integrable_posPart [m : MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfM : Measurable f) (hfi : Integrable f μ) :
    Integrable (fun ω => (f ω)⁺) μ := by
  apply hfi.norm.mono' (measurable_posPart hfM).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (posPart_nonneg _)]
  change max (f ω) 0 ≤ ‖f ω‖
  rw [Real.norm_eq_abs]
  exact max_le (le_abs_self _) (abs_nonneg _)

private lemma integrable_negPart [m : MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hfM : Measurable f) (hfi : Integrable f μ) :
    Integrable (fun ω => (f ω)⁻) μ := by
  apply hfi.norm.mono' (measurable_negPart hfM).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (negPart_nonneg _)]
  change max (-f ω) 0 ≤ ‖f ω‖
  rw [Real.norm_eq_abs]
  exact max_le (neg_le_abs _) (abs_nonneg _)

theorem EventRelativeMixing.covariance_real
    (m₁ m₂ : MeasurableSpace Ω) [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ε : ℝ) (hε : 0 ≤ ε)
    (hm₁ : m₁ ≤ m₀) (hm₂ : m₂ ≤ m₀)
    (hmix : EventRelativeMixing m₁ m₂ μ ε)
    {f g : Ω → ℝ}
    (hfM : @Measurable Ω ℝ m₁ (borel ℝ) f)
    (hgM : @Measurable Ω ℝ m₂ (borel ℝ) g)
    (hfi : Integrable f μ) (hgi : Integrable g μ) :
    Integrable (fun ω => f ω * g ω) μ ∧
      |(∫ ω, f ω * g ω ∂μ) -
          (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ| ≤
        ε * (∫ ω, |f ω| ∂μ) * ∫ ω, |g ω| ∂μ := by
  let fp : Ω → ℝ := fun ω => (f ω)⁺
  let fm : Ω → ℝ := fun ω => (f ω)⁻
  let gp : Ω → ℝ := fun ω => (g ω)⁺
  let gm : Ω → ℝ := fun ω => (g ω)⁻
  have hfpM : @Measurable Ω ℝ m₁ (borel ℝ) fp := measurable_posPart hfM
  have hfmM : @Measurable Ω ℝ m₁ (borel ℝ) fm := measurable_negPart hfM
  have hgpM : @Measurable Ω ℝ m₂ (borel ℝ) gp := measurable_posPart hgM
  have hgmM : @Measurable Ω ℝ m₂ (borel ℝ) gm := measurable_negPart hgM
  have hfM0 : @Measurable Ω ℝ m₀ (borel ℝ) f := hfM.mono hm₁ le_rfl
  have hgM0 : @Measurable Ω ℝ m₀ (borel ℝ) g := hgM.mono hm₂ le_rfl
  have hfpI : Integrable fp μ := integrable_posPart hfM0 hfi
  have hfmI : Integrable fm μ := integrable_negPart hfM0 hfi
  have hgpI : Integrable gp μ := integrable_posPart hgM0 hgi
  have hgmI : Integrable gm μ := integrable_negPart hgM0 hgi
  have hpp := hmix.covariance_nonneg m₁ m₂ μ ε hε hm₁ hm₂
    hfpM hgpM hfpI hgpI (fun ω => posPart_nonneg _) (fun ω => posPart_nonneg _)
  have hpm := hmix.covariance_nonneg m₁ m₂ μ ε hε hm₁ hm₂
    hfpM hgmM hfpI hgmI (fun ω => posPart_nonneg _) (fun ω => negPart_nonneg _)
  have hmp := hmix.covariance_nonneg m₁ m₂ μ ε hε hm₁ hm₂
    hfmM hgpM hfmI hgpI (fun ω => negPart_nonneg _) (fun ω => posPart_nonneg _)
  have hmm := hmix.covariance_nonneg m₁ m₂ μ ε hε hm₁ hm₂
    hfmM hgmM hfmI hgmI (fun ω => negPart_nonneg _) (fun ω => negPart_nonneg _)
  have hfgI : Integrable (fun ω => f ω * g ω) μ := by
    have hcomb := ((hpp.1.sub hpm.1).sub hmp.1).add hmm.1
    apply hcomb.congr
    filter_upwards [] with ω
    dsimp [fp, fm, gp, gm]
    calc
      (f ω)⁺ * (g ω)⁺ - (f ω)⁺ * (g ω)⁻ -
          (f ω)⁻ * (g ω)⁺ + (f ω)⁻ * (g ω)⁻ =
          ((f ω)⁺ - (f ω)⁻) * ((g ω)⁺ - (g ω)⁻) := by ring
      _ = f ω * g ω := by rw [posPart_sub_negPart, posPart_sub_negPart]
  have hIf : (∫ ω, f ω ∂μ) = (∫ ω, fp ω ∂μ) - ∫ ω, fm ω ∂μ := by
    rw [← integral_sub hfpI hfmI]
    apply integral_congr_ae
    filter_upwards [] with ω
    exact (posPart_sub_negPart (f ω)).symm
  have hIg : (∫ ω, g ω ∂μ) = (∫ ω, gp ω ∂μ) - ∫ ω, gm ω ∂μ := by
    rw [← integral_sub hgpI hgmI]
    apply integral_congr_ae
    filter_upwards [] with ω
    exact (posPart_sub_negPart (g ω)).symm
  have hIfg : (∫ ω, f ω * g ω ∂μ) =
      ((∫ ω, fp ω * gp ω ∂μ) - ∫ ω, fp ω * gm ω ∂μ) -
        (∫ ω, fm ω * gp ω ∂μ) + ∫ ω, fm ω * gm ω ∂μ := by
    calc
      (∫ ω, f ω * g ω ∂μ) = ∫ ω,
          (fp ω * gp ω - fp ω * gm ω) - fm ω * gp ω + fm ω * gm ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        dsimp [fp, fm, gp, gm]
        calc
          f ω * g ω = ((f ω)⁺ - (f ω)⁻) * ((g ω)⁺ - (g ω)⁻) := by
            rw [posPart_sub_negPart, posPart_sub_negPart]
          _ = ((f ω)⁺ * (g ω)⁺ - (f ω)⁺ * (g ω)⁻) -
              (f ω)⁻ * (g ω)⁺ + (f ω)⁻ * (g ω)⁻ := by ring
      _ = _ := by
        calc
          (∫ ω, (fp ω * gp ω - fp ω * gm ω) - fm ω * gp ω +
              fm ω * gm ω ∂μ) =
              (∫ ω, (fp ω * gp ω - fp ω * gm ω) - fm ω * gp ω ∂μ) +
                ∫ ω, fm ω * gm ω ∂μ := by
            simpa only [Pi.add_apply, Pi.sub_apply] using!
              integral_add ((hpp.1.sub hpm.1).sub hmp.1) hmm.1
          _ = ((∫ ω, fp ω * gp ω - fp ω * gm ω ∂μ) -
                ∫ ω, fm ω * gp ω ∂μ) + ∫ ω, fm ω * gm ω ∂μ := by
            congr 1
            simpa only [Pi.sub_apply] using!
              integral_sub (hpp.1.sub hpm.1) hmp.1
          _ = _ := by
            congr 2
            simpa only [Pi.sub_apply] using! integral_sub hpp.1 hpm.1
  have hfabs : (∫ ω, |f ω| ∂μ) =
      (∫ ω, fp ω ∂μ) + ∫ ω, fm ω ∂μ := by
    rw [← integral_add hfpI hfmI]
    apply integral_congr_ae
    filter_upwards [] with ω
    exact (posPart_add_negPart (f ω)).symm
  have hgabs : (∫ ω, |g ω| ∂μ) =
      (∫ ω, gp ω ∂μ) + ∫ ω, gm ω ∂μ := by
    rw [← integral_add hgpI hgmI]
    apply integral_congr_ae
    filter_upwards [] with ω
    exact (posPart_add_negPart (g ω)).symm
  let Cpp : ℝ := (∫ ω, fp ω * gp ω ∂μ) -
    (∫ ω, fp ω ∂μ) * ∫ ω, gp ω ∂μ
  let Cpm : ℝ := (∫ ω, fp ω * gm ω ∂μ) -
    (∫ ω, fp ω ∂μ) * ∫ ω, gm ω ∂μ
  let Cmp : ℝ := (∫ ω, fm ω * gp ω ∂μ) -
    (∫ ω, fm ω ∂μ) * ∫ ω, gp ω ∂μ
  let Cmm : ℝ := (∫ ω, fm ω * gm ω ∂μ) -
    (∫ ω, fm ω ∂μ) * ∫ ω, gm ω ∂μ
  have hcov : (∫ ω, f ω * g ω ∂μ) -
      (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ = Cpp - Cpm - Cmp + Cmm := by
    rw [hIfg, hIf, hIg]
    simp only [Cpp, Cpm, Cmp, Cmm]
    ring
  refine ⟨hfgI, ?_⟩
  rw [hcov, hfabs, hgabs]
  calc
    |Cpp - Cpm - Cmp + Cmm| ≤ |Cpp| + |Cpm| + |Cmp| + |Cmm| := by
      calc
        _ ≤ |Cpp - Cpm - Cmp| + |Cmm| := abs_add_le _ _
        _ ≤ (|Cpp - Cpm| + |Cmp|) + |Cmm| := by gcongr; exact abs_sub _ _
        _ ≤ (|Cpp| + |Cpm| + |Cmp|) + |Cmm| := by gcongr; exact abs_sub _ _
    _ ≤ (ε * (∫ ω, fp ω ∂μ) * ∫ ω, gp ω ∂μ) +
          (ε * (∫ ω, fp ω ∂μ) * ∫ ω, gm ω ∂μ) +
          (ε * (∫ ω, fm ω ∂μ) * ∫ ω, gp ω ∂μ) +
          (ε * (∫ ω, fm ω ∂μ) * ∫ ω, gm ω ∂μ) := by
      exact add_le_add (add_le_add (add_le_add hpp.2 hpm.2) hmp.2) hmm.2
    _ = ε * ((∫ ω, fp ω ∂μ) + ∫ ω, fm ω ∂μ) *
          ((∫ ω, gp ω ∂μ) + ∫ ω, gm ω ∂μ) := by ring

theorem EventRelativeMixing.covariance_complex
    (m₁ m₂ : MeasurableSpace Ω) [m₀ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ε : ℝ) (hε : 0 ≤ ε)
    (hm₁ : m₁ ≤ m₀) (hm₂ : m₂ ≤ m₀)
    (hmix : EventRelativeMixing m₁ m₂ μ ε)
    {f g : Ω → ℂ}
    (hfM : @Measurable Ω ℂ m₁ (borel ℂ) f)
    (hgM : @Measurable Ω ℂ m₂ (borel ℂ) g)
    (hfi : Integrable f μ) (hgi : Integrable g μ) :
    Integrable (fun ω => f ω * g ω) μ ∧
      ‖(∫ ω, f ω * g ω ∂μ) -
          (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ‖ ≤
        4 * ε * (∫ ω, ‖f ω‖ ∂μ) * ∫ ω, ‖g ω‖ ∂μ := by
  let fr : Ω → ℝ := fun ω => (f ω).re
  let fi : Ω → ℝ := fun ω => (f ω).im
  let gr : Ω → ℝ := fun ω => (g ω).re
  let gi : Ω → ℝ := fun ω => (g ω).im
  have hfrM : @Measurable Ω ℝ m₁ (borel ℝ) fr :=
    Complex.continuous_re.measurable.comp hfM
  have hfiM : @Measurable Ω ℝ m₁ (borel ℝ) fi :=
    Complex.continuous_im.measurable.comp hfM
  have hgrM : @Measurable Ω ℝ m₂ (borel ℝ) gr :=
    Complex.continuous_re.measurable.comp hgM
  have hgiM : @Measurable Ω ℝ m₂ (borel ℝ) gi :=
    Complex.continuous_im.measurable.comp hgM
  have hfrI : Integrable fr μ := hfi.re
  have hfiI : Integrable fi μ := hfi.im
  have hgrI : Integrable gr μ := hgi.re
  have hgiI : Integrable gi μ := hgi.im
  have hrr := hmix.covariance_real m₁ m₂ μ ε hε hm₁ hm₂ hfrM hgrM hfrI hgrI
  have hri := hmix.covariance_real m₁ m₂ μ ε hε hm₁ hm₂ hfrM hgiM hfrI hgiI
  have hir := hmix.covariance_real m₁ m₂ μ ε hε hm₁ hm₂ hfiM hgrM hfiI hgrI
  have hii := hmix.covariance_real m₁ m₂ μ ε hε hm₁ hm₂ hfiM hgiM hfiI hgiI
  have hfgI : Integrable (fun ω => f ω * g ω) μ := by
    apply Integrable.re_im_iff.mp
    constructor
    · simpa only [Complex.mul_re, fr, fi, gr, gi] using! hrr.1.sub hii.1
    · simpa only [Complex.mul_im, fr, fi, gr, gi] using! hri.1.add hir.1
  let Crr : ℝ := (∫ ω, fr ω * gr ω ∂μ) -
    (∫ ω, fr ω ∂μ) * ∫ ω, gr ω ∂μ
  let Cri : ℝ := (∫ ω, fr ω * gi ω ∂μ) -
    (∫ ω, fr ω ∂μ) * ∫ ω, gi ω ∂μ
  let Cir : ℝ := (∫ ω, fi ω * gr ω ∂μ) -
    (∫ ω, fi ω ∂μ) * ∫ ω, gr ω ∂μ
  let Cii : ℝ := (∫ ω, fi ω * gi ω ∂μ) -
    (∫ ω, fi ω ∂μ) * ∫ ω, gi ω ∂μ
  let Z : ℂ := (∫ ω, f ω * g ω ∂μ) -
    (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ
  have hfg_re : (∫ ω, f ω * g ω ∂μ).re =
      ∫ ω, fr ω * gr ω - fi ω * gi ω ∂μ := by
    simpa only [Complex.mul_re, fr, fi, gr, gi] using! (integral_re hfgI).symm
  have hfg_im : (∫ ω, f ω * g ω ∂μ).im =
      ∫ ω, fr ω * gi ω + fi ω * gr ω ∂μ := by
    simpa only [Complex.mul_im, fr, fi, gr, gi] using! (integral_im hfgI).symm
  have hf_re : (∫ ω, f ω ∂μ).re = ∫ ω, fr ω ∂μ := by
    simpa only [fr] using! (integral_re hfi).symm
  have hf_im : (∫ ω, f ω ∂μ).im = ∫ ω, fi ω ∂μ := by
    simpa only [fi] using! (integral_im hfi).symm
  have hg_re : (∫ ω, g ω ∂μ).re = ∫ ω, gr ω ∂μ := by
    simpa only [gr] using! (integral_re hgi).symm
  have hg_im : (∫ ω, g ω ∂μ).im = ∫ ω, gi ω ∂μ := by
    simpa only [gi] using! (integral_im hgi).symm
  have hZre : Z.re = Crr - Cii := by
    dsimp only [Z, Crr, Cii]
    rw [Complex.sub_re, Complex.mul_re, hfg_re, hf_re, hf_im, hg_re, hg_im]
    rw [integral_sub hrr.1 hii.1]
    ring
  have hZim : Z.im = Cri + Cir := by
    dsimp only [Z, Cri, Cir]
    rw [Complex.sub_im, Complex.mul_im, hfg_im, hf_re, hf_im, hg_re, hg_im]
    rw [integral_add hri.1 hir.1]
    ring
  have hfr_abs : (∫ ω, |fr ω| ∂μ) ≤ ∫ ω, ‖f ω‖ ∂μ := by
    apply integral_mono hfrI.norm hfi.norm
    intro ω
    exact Complex.abs_re_le_norm (f ω)
  have hfi_abs : (∫ ω, |fi ω| ∂μ) ≤ ∫ ω, ‖f ω‖ ∂μ := by
    apply integral_mono hfiI.norm hfi.norm
    intro ω
    exact Complex.abs_im_le_norm (f ω)
  have hgr_abs : (∫ ω, |gr ω| ∂μ) ≤ ∫ ω, ‖g ω‖ ∂μ := by
    apply integral_mono hgrI.norm hgi.norm
    intro ω
    exact Complex.abs_re_le_norm (g ω)
  have hgi_abs : (∫ ω, |gi ω| ∂μ) ≤ ∫ ω, ‖g ω‖ ∂μ := by
    apply integral_mono hgiI.norm hgi.norm
    intro ω
    exact Complex.abs_im_le_norm (g ω)
  have hf_norm0 : 0 ≤ ∫ ω, ‖f ω‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  have hg_norm0 : 0 ≤ ∫ ω, ‖g ω‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  have hcommon {a b : Ω → ℝ}
      (ha0 : 0 ≤ ∫ ω, |a ω| ∂μ) (hb0 : 0 ≤ ∫ ω, |b ω| ∂μ)
      (ha : (∫ ω, |a ω| ∂μ) ≤ ∫ ω, ‖f ω‖ ∂μ)
      (hb : (∫ ω, |b ω| ∂μ) ≤ ∫ ω, ‖g ω‖ ∂μ) :
      ε * (∫ ω, |a ω| ∂μ) * ∫ ω, |b ω| ∂μ ≤
        ε * (∫ ω, ‖f ω‖ ∂μ) * ∫ ω, ‖g ω‖ ∂μ := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left ha hε) hb hb0
      (mul_nonneg hε hf_norm0)
  have hrr' : |Crr| ≤ ε * (∫ ω, ‖f ω‖ ∂μ) * ∫ ω, ‖g ω‖ ∂μ :=
    hrr.2.trans (hcommon (integral_nonneg fun _ => abs_nonneg _)
      (integral_nonneg fun _ => abs_nonneg _) hfr_abs hgr_abs)
  have hri' : |Cri| ≤ ε * (∫ ω, ‖f ω‖ ∂μ) * ∫ ω, ‖g ω‖ ∂μ :=
    hri.2.trans (hcommon (integral_nonneg fun _ => abs_nonneg _)
      (integral_nonneg fun _ => abs_nonneg _) hfr_abs hgi_abs)
  have hir' : |Cir| ≤ ε * (∫ ω, ‖f ω‖ ∂μ) * ∫ ω, ‖g ω‖ ∂μ :=
    hir.2.trans (hcommon (integral_nonneg fun _ => abs_nonneg _)
      (integral_nonneg fun _ => abs_nonneg _) hfi_abs hgr_abs)
  have hii' : |Cii| ≤ ε * (∫ ω, ‖f ω‖ ∂μ) * ∫ ω, ‖g ω‖ ∂μ :=
    hii.2.trans (hcommon (integral_nonneg fun _ => abs_nonneg _)
      (integral_nonneg fun _ => abs_nonneg _) hfi_abs hgi_abs)
  refine ⟨hfgI, ?_⟩
  change ‖Z‖ ≤ _
  calc
    ‖Z‖ ≤ |Z.re| + |Z.im| := Complex.norm_le_abs_re_add_abs_im Z
    _ = |Crr - Cii| + |Cri + Cir| := by rw [hZre, hZim]
    _ ≤ (|Crr| + |Cii|) + (|Cri| + |Cir|) :=
      add_le_add (abs_sub _ _) (abs_add_le _ _)
    _ ≤ 4 * ε * (∫ ω, ‖f ω‖ ∂μ) * ∫ ω, ‖g ω‖ ∂μ := by
      linarith

/-- A fixed polynomial number of tuples is dominated by any genuine
geometric mixing rate.  This is the quantitative summation used after the
function-level covariance estimate. -/
theorem tendsto_natPower_mul_inverse_geometric
    (r c : ℕ) (hc : 0 < c) {θ : ℝ} (hθ : 1 < θ) :
    Tendsto
      (fun L : ℕ ↦ (L : ℝ) ^ r * (θ ^ (c * L))⁻¹)
      atTop (nhds 0) := by
  have hbase : 1 < θ ^ c := one_lt_pow₀ hθ (Nat.ne_of_gt hc)
  have h := tendsto_pow_const_div_const_pow_of_one_lt r hbase
  simpa only [div_eq_mul_inv, pow_mul] using! h

/-- The same decay remains after multiplication by a fixed constant. -/
theorem tendsto_const_mul_natPower_mul_inverse_geometric
    (C : ℝ) (r c : ℕ) (hc : 0 < c) {θ : ℝ} (hθ : 1 < θ) :
    Tendsto
      (fun L : ℕ ↦ C * ((L : ℝ) ^ r * (θ ^ (c * L))⁻¹))
      atTop (nhds 0) := by
  simpa only [mul_zero] using!
    (tendsto_natPower_mul_inverse_geometric r c hc hθ).const_mul C



end

end Erdos1002
