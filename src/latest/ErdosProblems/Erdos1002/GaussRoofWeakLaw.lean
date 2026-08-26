import ErdosProblems.Erdos1002.GaussBoundedWeakLaw
import ErdosProblems.Erdos1002.GaussRoofMean
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Weak law for the unbounded Gauss roof

The logarithmic roof is truncated by replacing `x` with
`max (exp (-B)) x`.  This convention is continuous at zero and therefore
gives a genuinely bounded Lipschitz observable on the closed state interval.
After applying the bounded weak law, dominated convergence removes the
truncation.
-/

open Filter MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos1002

noncomputable section

/-- Continuous truncation of the Gauss roof at height `B`. -/
def gaussRoofTruncation (B x : ℝ) : ℝ :=
  -Real.log (max (Real.exp (-B)) x)

theorem continuous_gaussRoofTruncation (B : ℝ) :
    Continuous (gaussRoofTruncation B) := by
  unfold gaussRoofTruncation
  exact ((continuous_const.max continuous_id).log
    (fun x => ne_of_gt ((Real.exp_pos (-B)).trans_le
      (le_max_left _ _)))).neg

theorem measurable_gaussRoofTruncation (B : ℝ) :
    Measurable (gaussRoofTruncation B) :=
  (continuous_gaussRoofTruncation B).measurable

theorem gaussRoofTruncation_nonnegative
    {B x : ℝ} (hB : 0 ≤ B) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ gaussRoofTruncation B x := by
  have hc1 : Real.exp (-B) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr hB)
  have hm0 : 0 < max (Real.exp (-B)) x :=
    (Real.exp_pos _).trans_le (le_max_left _ _)
  have hm1 : max (Real.exp (-B)) x ≤ 1 := max_le hc1 hx.2
  unfold gaussRoofTruncation
  exact neg_nonneg.mpr (Real.log_nonpos hm0.le hm1)

theorem gaussRoofTruncation_le
    {B x : ℝ} :
    gaussRoofTruncation B x ≤ B := by
  have hcpos : 0 < Real.exp (-B) := Real.exp_pos _
  have hmpos : 0 < max (Real.exp (-B)) x :=
    hcpos.trans_le (le_max_left _ _)
  have hlog := Real.strictMonoOn_log.monotoneOn
    (show Real.exp (-B) ∈ Ioi (0 : ℝ) from hcpos)
    (show max (Real.exp (-B)) x ∈ Ioi (0 : ℝ) from hmpos)
    (le_max_left _ _)
  unfold gaussRoofTruncation
  rw [Real.log_exp] at hlog
  linarith

/-- The truncation has the explicit Lipschitz constant `exp B` on `[0,1]`. -/
theorem gaussRoofTruncation_lipschitz
    {B : ℝ} (hB : 0 ≤ B) :
    GaussUnitLipschitzBound (Real.exp B) (gaussRoofTruncation B) := by
  let c : ℝ := Real.exp (-B)
  have hcpos : 0 < c := Real.exp_pos _
  have hc1 : c ≤ 1 := by
    dsimp only [c]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr hB)
  have hderiv : ∀ x ∈ Icc c (1 : ℝ),
      DifferentiableAt ℝ Real.log x := by
    intro x hx
    exact (Real.hasDerivAt_log (ne_of_gt (hcpos.trans_le hx.1))).differentiableAt
  have hbound : ∀ x ∈ Icc c (1 : ℝ),
      ‖deriv Real.log x‖₊ ≤ (Real.exp B).toNNReal := by
    intro x hx
    have hxpos : 0 < x := hcpos.trans_le hx.1
    rw [(Real.hasDerivAt_log (ne_of_gt hxpos)).deriv]
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hxpos),
      Real.coe_toNNReal (Real.exp B) (Real.exp_pos B).le]
    have hinv : x⁻¹ ≤ c⁻¹ := by
      simpa only [one_div] using! one_div_le_one_div_of_le hcpos hx.1
    calc
      x⁻¹ ≤ c⁻¹ := hinv
      _ = Real.exp B := by
        dsimp only [c]
        rw [Real.exp_neg]
        exact inv_inv _
  have hlogLip := Convex.lipschitzOnWith_of_nnnorm_deriv_le
    hderiv hbound (convex_Icc c (1 : ℝ))
  intro y hy z hz
  have hmy : max c y ∈ Icc c (1 : ℝ) :=
    ⟨le_max_left _ _, max_le hc1 hy.2⟩
  have hmz : max c z ∈ Icc c (1 : ℝ) :=
    ⟨le_max_left _ _, max_le hc1 hz.2⟩
  have hlog := hlogLip.norm_sub_le hmy hmz
  have hmax : |max c y - max c z| ≤ |y - z| := by
    simpa only [max_comm] using! abs_max_sub_max_le_abs y z c
  unfold gaussRoofTruncation
  rw [show -Real.log (max c y) - -Real.log (max c z) =
      -(Real.log (max c y) - Real.log (max c z)) by ring,
    abs_neg]
  calc
    |Real.log (max c y) - Real.log (max c z)| ≤
        Real.exp B * |max c y - max c z| := by
      simpa only [Real.norm_eq_abs,
        Real.coe_toNNReal (Real.exp B) (Real.exp_pos B).le] using! hlog
    _ ≤ Real.exp B * |y - z| :=
      mul_le_mul_of_nonneg_left hmax (Real.exp_pos B).le

theorem gaussRoofTruncation_unit_bounds
    {B : ℝ} (hB : 0 ≤ B) :
    GaussUnitNonnegative (gaussRoofTruncation B) ∧
      GaussUnitUpperBound B (gaussRoofTruncation B) := by
  exact ⟨fun _ hx => gaussRoofTruncation_nonnegative hB hx,
    fun _ _hx => gaussRoofTruncation_le⟩

theorem gaussRoofTruncation_le_roof
    {B x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    gaussRoofTruncation B x ≤ -Real.log x := by
  have hmpos : 0 < max (Real.exp (-B)) x :=
    hx.1.trans_le (le_max_right _ _)
  have hlog := Real.strictMonoOn_log.monotoneOn
    (show x ∈ Ioi (0 : ℝ) from hx.1)
    (show max (Real.exp (-B)) x ∈ Ioi (0 : ℝ) from hmpos)
    (le_max_right _ _)
  unfold gaussRoofTruncation
  linarith

/-- Pointwise removal of the natural-height truncation at every positive
state point. -/
theorem tendsto_gaussRoofTruncation_nat {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => gaussRoofTruncation (n : ℝ) x)
      atTop (𝓝 (-Real.log x)) := by
  have hexp : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ)))
      atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  have hmax : Tendsto
      (fun n : ℕ => max (Real.exp (-(n : ℝ))) x)
      atTop (𝓝 x) := by
    convert! hexp.max tendsto_const_nhds using 1
    rw [max_eq_right hx.le]
  have hlog := (Real.continuousAt_log hx.ne').tendsto.comp hmax
  simpa only [gaussRoofTruncation] using! hlog.neg

/-- Dominated convergence removes the roof truncation in expectation. -/
theorem tendsto_integral_gaussRoofTruncation_nat :
    Tendsto
      (fun n : ℕ => ∫ x, gaussRoofTruncation (n : ℝ) x ∂gaussMeasure)
      atTop (𝓝 gaussRoofMean) := by
  unfold gaussRoofMean
  apply tendsto_integral_of_dominated_convergence
    (fun x : ℝ => -Real.log x)
  · intro n
    exact (measurable_gaussRoofTruncation (n : ℝ)).aestronglyMeasurable
  · exact integrable_neg_log_gaussMeasure
  · intro n
    filter_upwards [gaussMeasure_unit_ae] with x hx
    have hxcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    rw [Real.norm_eq_abs,
      abs_of_nonneg (gaussRoofTruncation_nonnegative
        (by positivity : (0 : ℝ) ≤ n) hxcc)]
    exact gaussRoofTruncation_le_roof hx
  · filter_upwards [gaussMeasure_unit_ae] with x hx
    exact tendsto_gaussRoofTruncation_nat hx.1

/-- The nonnegative part of the roof discarded at height `B`. -/
def gaussRoofTail (B x : ℝ) : ℝ :=
  -Real.log x - gaussRoofTruncation B x

theorem measurable_gaussRoofTail (B : ℝ) :
    Measurable (gaussRoofTail B) := by
  unfold gaussRoofTail
  exact Real.measurable_log.neg.sub (measurable_gaussRoofTruncation B)

theorem gaussRoofTail_nonnegative
    {B x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    0 ≤ gaussRoofTail B x := by
  unfold gaussRoofTail
  linarith [gaussRoofTruncation_le_roof (B := B) hx]

theorem integrable_gaussRoofTruncation_nat (B : ℕ) :
    Integrable (gaussRoofTruncation (B : ℝ)) gaussMeasure := by
  have hb := gaussRoofTruncation_unit_bounds
    (show (0 : ℝ) ≤ B by positivity)
  have hmem := memLp_two_comp_gaussOrbit_of_unit_bounds
    (measurable_gaussRoofTruncation (B : ℝ)) hb.1 hb.2 0
  simpa only [gaussOrbit, Function.iterate_zero, id_eq] using!
    hmem.integrable (by norm_num)

theorem integrable_gaussRoofTail_nat (B : ℕ) :
    Integrable (gaussRoofTail (B : ℝ)) gaussMeasure := by
  unfold gaussRoofTail
  exact integrable_neg_log_gaussMeasure.sub
    (integrable_gaussRoofTruncation_nat B)

theorem integral_gaussRoofTail_nat (B : ℕ) :
    (∫ x, gaussRoofTail (B : ℝ) x ∂gaussMeasure) =
      gaussRoofMean -
        ∫ x, gaussRoofTruncation (B : ℝ) x ∂gaussMeasure := by
  unfold gaussRoofTail gaussRoofMean
  rw [integral_sub integrable_neg_log_gaussMeasure
    (integrable_gaussRoofTruncation_nat B)]

theorem tendsto_integral_gaussRoofTail_nat :
    Tendsto
      (fun B : ℕ => ∫ x, gaussRoofTail (B : ℝ) x ∂gaussMeasure)
      atTop (𝓝 0) := by
  have h := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => gaussRoofMean) atTop (𝓝 gaussRoofMean)).sub
    tendsto_integral_gaussRoofTruncation_nat
  simpa only [integral_gaussRoofTail_nat, sub_self] using! h

/-! ## Stationary averages of integrable observables -/

/-- Every finite iterate of the Gauss map preserves the Gauss probability
measure.  We expose the bundled form because it permits integrability and
almost-everywhere statements to be pulled back without boundedness. -/
theorem measurePreserving_gaussOrbit (i : ℕ) :
    MeasurePreserving (gaussOrbit i) gaussMeasure gaussMeasure := by
  refine ⟨measurable_gaussOrbit i, ?_⟩
  simpa only [gaussOrbit] using! map_gaussMap_iterate_gaussMeasure i

theorem gaussOrbit_unit_ae (i : ℕ) :
    ∀ᵐ x ∂gaussMeasure, gaussOrbit i x ∈ Ioc (0 : ℝ) 1 := by
  exact (measurePreserving_gaussOrbit i).quasiMeasurePreserving.tendsto_ae
    gaussMeasure_unit_ae

theorem integrable_comp_gaussOrbit_of_integrable
    {f : ℝ → ℝ} (hf : Integrable f gaussMeasure) (i : ℕ) :
    Integrable (fun x => f (gaussOrbit i x)) gaussMeasure := by
  simpa only [Function.comp_apply] using!
    (measurePreserving_gaussOrbit i).integrable_comp_of_integrable hf

theorem integrable_gaussBirkhoffAverage_of_integrable
    {f : ℝ → ℝ} (hf : Integrable f gaussMeasure) (n : ℕ) :
    Integrable (gaussBirkhoffAverage f n) gaussMeasure := by
  have hsum : Integrable
      (fun x => ∑ i ∈ Finset.range n, f (gaussOrbit i x))
      gaussMeasure := by
    have hraw := integrable_finset_sum' (Finset.range n) fun i _hi =>
      integrable_comp_gaussOrbit_of_integrable hf i
    convert! hraw using 1
    funext x
    rw [Finset.sum_apply]
  simpa only [gaussBirkhoffAverage, div_eq_mul_inv] using!
    hsum.mul_const ((n : ℝ)⁻¹)

/-- Stationarity identifies the expectation of every nonempty finite
Birkhoff average, with no boundedness assumption. -/
theorem integral_gaussBirkhoffAverage_of_integrable
    {f : ℝ → ℝ} (hfM : Measurable f)
    (hf : Integrable f gaussMeasure) {n : ℕ} (hn : 0 < n) :
    (∫ x, gaussBirkhoffAverage f n x ∂gaussMeasure) =
      ∫ x, f x ∂gaussMeasure := by
  have hint (i : ℕ) :
      Integrable (fun x => f (gaussOrbit i x)) gaussMeasure :=
    integrable_comp_gaussOrbit_of_integrable hf i
  unfold gaussBirkhoffAverage
  rw [integral_div]
  rw [integral_finset_sum _ fun i _hi => hint i]
  simp_rw [integral_comp_gaussOrbit f hfM]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp [hnR]

theorem gaussBirkhoffAverage_sub (f g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    gaussBirkhoffAverage (fun y => f y - g y) n x =
      gaussBirkhoffAverage f n x - gaussBirkhoffAverage g n x := by
  simp only [gaussBirkhoffAverage, Finset.sum_sub_distrib]
  ring

theorem gaussBirkhoffAverage_nonnegative_ae
    {f : ℝ → ℝ} (hf0 : ∀ᵐ x ∂gaussMeasure, 0 ≤ f x) (n : ℕ) :
    ∀ᵐ x ∂gaussMeasure, 0 ≤ gaussBirkhoffAverage f n x := by
  have hi (i : ℕ) : ∀ᵐ x ∂gaussMeasure, 0 ≤ f (gaussOrbit i x) :=
    (measurePreserving_gaussOrbit i).quasiMeasurePreserving.tendsto_ae hf0
  have hall : ∀ᵐ x ∂gaussMeasure, ∀ i : ℕ,
      0 ≤ f (gaussOrbit i x) := ae_all_iff.mpr hi
  filter_upwards [hall] with x hx
  unfold gaussBirkhoffAverage
  exact div_nonneg (Finset.sum_nonneg fun i _hi => hx i) (Nat.cast_nonneg n)

/-! ## The logarithmic roof average and its tail -/

/-- Average of the actual, unbounded logarithmic roof. -/
def gaussRoofAverage (n : ℕ) : ℝ → ℝ :=
  gaussBirkhoffAverage (fun x : ℝ => -Real.log x) n

theorem gaussRoofAverage_sub_truncation
    (B n : ℕ) (x : ℝ) :
    gaussRoofAverage n x -
        gaussBirkhoffAverage (gaussRoofTruncation (B : ℝ)) n x =
      gaussBirkhoffAverage (gaussRoofTail (B : ℝ)) n x := by
  rw [show gaussRoofAverage n x =
      gaussBirkhoffAverage (fun y : ℝ => -Real.log y) n x by rfl]
  rw [← gaussBirkhoffAverage_sub]
  rfl

theorem gaussRoofTailAverage_nonnegative_ae (B n : ℕ) :
    ∀ᵐ x ∂gaussMeasure,
      0 ≤ gaussBirkhoffAverage (gaussRoofTail (B : ℝ)) n x := by
  apply gaussBirkhoffAverage_nonnegative_ae
  filter_upwards [gaussMeasure_unit_ae] with x hx
  exact gaussRoofTail_nonnegative hx

theorem integrable_gaussRoofTailAverage (B n : ℕ) :
    Integrable
      (gaussBirkhoffAverage (gaussRoofTail (B : ℝ)) n)
      gaussMeasure :=
  integrable_gaussBirkhoffAverage_of_integrable
    (integrable_gaussRoofTail_nat B) n

theorem integral_gaussRoofTailAverage
    (B : ℕ) {n : ℕ} (hn : 0 < n) :
    (∫ x, gaussBirkhoffAverage (gaussRoofTail (B : ℝ)) n x
        ∂gaussMeasure) =
      ∫ x, gaussRoofTail (B : ℝ) x ∂gaussMeasure :=
  integral_gaussBirkhoffAverage_of_integrable
    (measurable_gaussRoofTail (B : ℝ))
    (integrable_gaussRoofTail_nat B) hn

/-- Real-valued Markov inequality in the precise form used below.  The
nonnegativity hypothesis is only almost everywhere; no pointwise repair of
the observable is needed. -/
theorem gaussMeasureReal_ge_le_integral_div
    {f : ℝ → ℝ} (hfM : Measurable f)
    (hf : Integrable f gaussMeasure)
    (hf0 : ∀ᵐ x ∂gaussMeasure, 0 ≤ f x)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    gaussMeasure.real {x | epsilon ≤ f x} ≤
      (∫ x, f x ∂gaussMeasure) / epsilon := by
  have hmarkov := meas_ge_le_lintegral_div (μ := gaussMeasure)
    hfM.ennreal_ofReal.aemeasurable
    (ε := ENNReal.ofReal epsilon)
    (ENNReal.ofReal_ne_zero_iff.mpr hepsilon)
    ENNReal.ofReal_ne_top
  have hset :
      {x | ENNReal.ofReal epsilon ≤ ENNReal.ofReal (f x)} =
        {x | epsilon ≤ f x} := by
    ext x
    simp only [mem_setOf_eq, ENNReal.ofReal_le_ofReal_iff']
    exact or_iff_left (not_le.mpr hepsilon)
  rw [hset, ← ofReal_integral_eq_lintegral_ofReal hf hf0] at hmarkov
  have hreal := ENNReal.toReal_mono (by finiteness) hmarkov
  have hint0 : 0 ≤ ∫ x, f x ∂gaussMeasure :=
    integral_nonneg_of_ae hf0
  simpa only [measureReal_def, ENNReal.toReal_div,
    ENNReal.toReal_ofReal hint0,
    ENNReal.toReal_ofReal hepsilon.le] using! hreal

theorem gaussRoofTailAverage_markov
    (B : ℕ) {n : ℕ} (hn : 0 < n)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    gaussMeasure.real
        {x | epsilon ≤
          gaussBirkhoffAverage (gaussRoofTail (B : ℝ)) n x} ≤
      (∫ x, gaussRoofTail (B : ℝ) x ∂gaussMeasure) / epsilon := by
  rw [← integral_gaussRoofTailAverage B hn]
  exact gaussMeasureReal_ge_le_integral_div
    ((Finset.measurable_fun_sum (Finset.range n) fun i _hi =>
      (measurable_gaussRoofTail (B : ℝ)).comp
        (measurable_gaussOrbit i)).div_const (n : ℝ))
    (integrable_gaussRoofTailAverage B n)
    (gaussRoofTailAverage_nonnegative_ae B n) hepsilon

/-! ## Removal of the truncation in probability -/

/-- Weak law for the actual unbounded logarithmic roof.  The proof first
chooses one truncation height from the `L¹` tail, applies the already-proved
bounded Lipschitz weak law at that fixed height, and then uses Markov's
inequality uniformly in the averaging time. -/
theorem tendstoInMeasure_gaussRoofAverage :
    TendstoInMeasure gaussMeasure
      (fun n => gaussRoofAverage n) atTop
      (fun _ => gaussRoofMean) := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro epsilon hepsilon
  rw [Metric.tendsto_atTop]
  intro eta heta
  let delta : ℝ := min (epsilon / 3) (eta * epsilon / 6)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min (by positivity) (by positivity)
  obtain ⟨B, hBsmall⟩ :=
    (((tendsto_order.1 tendsto_integral_gaussRoofTail_nat).2
      delta hdelta).exists)
  let tailMean : ℝ :=
    ∫ x, gaussRoofTail (B : ℝ) x ∂gaussMeasure
  let truncMean : ℝ :=
    ∫ x, gaussRoofTruncation (B : ℝ) x ∂gaussMeasure
  have htailSmall : tailMean < epsilon / 3 := by
    exact (lt_min_iff.mp hBsmall).1
  have htailEta : tailMean < eta * epsilon / 6 := by
    exact (lt_min_iff.mp hBsmall).2
  have htail0 : 0 ≤ tailMean := by
    dsimp only [tailMean]
    apply integral_nonneg_of_ae
    filter_upwards [gaussMeasure_unit_ae] with x hx
    exact gaussRoofTail_nonnegative hx
  have hmean : gaussRoofMean = truncMean + tailMean := by
    have h := integral_gaussRoofTail_nat B
    dsimp only [tailMean, truncMean]
    linarith
  have hB0 : (0 : ℝ) ≤ B := by positivity
  obtain ⟨htrunc0, htruncB⟩ :=
    gaussRoofTruncation_unit_bounds hB0
  have htruncConv :
      TendstoInMeasure gaussMeasure
        (fun n => gaussBirkhoffAverage
          (gaussRoofTruncation (B : ℝ)) n) atTop
        (fun _ => truncMean) := by
    dsimp only [truncMean]
    exact tendstoInMeasure_gaussBirkhoffAverage
      (Real.exp_pos (B : ℝ)).le
      (measurable_gaussRoofTruncation (B : ℝ))
      htrunc0 htruncB (gaussRoofTruncation_lipschitz hB0)
  have htruncMeasure :
      Tendsto
        (fun n => gaussMeasure.real
          {x | epsilon / 3 ≤
            dist
              (gaussBirkhoffAverage
                (gaussRoofTruncation (B : ℝ)) n x)
              truncMean})
        atTop (𝓝 0) := by
    exact (tendstoInMeasure_iff_measureReal_dist.mp htruncConv)
      (epsilon / 3) (by positivity)
  have htruncEventually : ∀ᶠ n : ℕ in atTop,
      gaussMeasure.real
          {x | epsilon / 3 ≤
            dist
              (gaussBirkhoffAverage
                (gaussRoofTruncation (B : ℝ)) n x)
              truncMean} < eta / 2 :=
    (tendsto_order.1 htruncMeasure).2 (eta / 2) (by positivity)
  have htailProbability : tailMean / (epsilon / 3) < eta / 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < epsilon / 3)).2
    nlinarith [htailEta]
  obtain ⟨N, hN⟩ := htruncEventually.exists_forall_of_atTop
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one
    (le_trans (le_max_right _ _) hn)
  let E : Set ℝ :=
    {x | epsilon ≤ dist (gaussRoofAverage n x) gaussRoofMean}
  let T : Set ℝ :=
    {x | epsilon / 3 ≤
      gaussBirkhoffAverage (gaussRoofTail (B : ℝ)) n x}
  let U : Set ℝ :=
    {x | epsilon / 3 ≤
      dist
        (gaussBirkhoffAverage
          (gaussRoofTruncation (B : ℝ)) n x)
        truncMean}
  have hsubsetAE : E ≤ᵐ[gaussMeasure] (T ∪ U : Set ℝ) := by
    filter_upwards [gaussRoofTailAverage_nonnegative_ae B n] with x hTx
    intro hxE
    by_contra hxUnion
    have hxT :
        gaussBirkhoffAverage (gaussRoofTail (B : ℝ)) n x <
          epsilon / 3 := by
      have : x ∉ T := fun hx => hxUnion (mem_union_left U hx)
      simpa only [T, mem_setOf_eq, not_le] using! this
    have hxU :
        dist
          (gaussBirkhoffAverage
            (gaussRoofTruncation (B : ℝ)) n x)
          truncMean < epsilon / 3 := by
      have : x ∉ U := fun hx => hxUnion (mem_union_right T hx)
      simpa only [U, mem_setOf_eq, not_le] using! this
    have htriangle :
        dist (gaussRoofAverage n x) gaussRoofMean ≤
          gaussBirkhoffAverage (gaussRoofTail (B : ℝ)) n x +
            dist
              (gaussBirkhoffAverage
                (gaussRoofTruncation (B : ℝ)) n x)
              truncMean + tailMean := by
      rw [Real.dist_eq, Real.dist_eq]
      calc
        |gaussRoofAverage n x - gaussRoofMean| ≤
            |gaussRoofAverage n x -
                gaussBirkhoffAverage
                  (gaussRoofTruncation (B : ℝ)) n x| +
              |gaussBirkhoffAverage
                  (gaussRoofTruncation (B : ℝ)) n x -
                gaussRoofMean| :=
          abs_sub_le _ _ _
        _ ≤ |gaussRoofAverage n x -
                gaussBirkhoffAverage
                  (gaussRoofTruncation (B : ℝ)) n x| +
              (|gaussBirkhoffAverage
                  (gaussRoofTruncation (B : ℝ)) n x -
                truncMean| + |truncMean - gaussRoofMean|) := by
          gcongr
          exact abs_sub_le _ _ _
        _ = gaussBirkhoffAverage
                (gaussRoofTail (B : ℝ)) n x +
              |gaussBirkhoffAverage
                  (gaussRoofTruncation (B : ℝ)) n x -
                truncMean| + tailMean := by
          rw [gaussRoofAverage_sub_truncation B n x,
            abs_of_nonneg hTx, hmean]
          rw [show truncMean - (truncMean + tailMean) = -tailMean by ring,
            abs_neg, abs_of_nonneg htail0]
          ring
    have hxDist : dist (gaussRoofAverage n x) gaussRoofMean < epsilon := by
      linarith
    exact (not_lt_of_ge hxE) hxDist
  have hmonoENN : gaussMeasure E ≤ gaussMeasure (T ∪ U) :=
    measure_mono_ae hsubsetAE
  have hmonoReal : gaussMeasure.real E ≤ gaussMeasure.real (T ∪ U) := by
    exact ENNReal.toReal_mono (by finiteness) hmonoENN
  have hmarkov : gaussMeasure.real T ≤
      tailMean / (epsilon / 3) := by
    dsimp only [T, tailMean]
    exact gaussRoofTailAverage_markov B hnpos (by positivity)
  have hU : gaussMeasure.real U < eta / 2 := by
    exact hN n hnN
  have hEsmall : gaussMeasure.real E < eta := by
    calc
      gaussMeasure.real E ≤ gaussMeasure.real (T ∪ U) := hmonoReal
      _ ≤ gaussMeasure.real T + gaussMeasure.real U :=
        measureReal_union_le T U
      _ ≤ tailMean / (epsilon / 3) + gaussMeasure.real U := by
        gcongr
      _ < eta / 2 + eta / 2 := add_lt_add htailProbability hU
      _ = eta := by ring
  simpa only [E, Real.dist_eq, sub_zero,
    abs_of_nonneg measureReal_nonneg] using! hEsmall

end

end Erdos1002
