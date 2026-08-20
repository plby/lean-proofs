/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
import ErdosProblems.Erdos783.External.Erdos390.PoissonDickmanTotalDensity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Erdos390

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- Real-valued representative of the explicit total-mass density. -/
def poissonDickmanTotalDensityReal (u : ℝ) : ℝ :=
  (poissonDickmanTotalDensityFormula u).toReal

/-- Real normalization constant for the total-mass density. -/
def poissonDickmanDensityNormalizerReal : ℝ :=
  poissonDickmanDensityNormalizer.toReal

theorem poissonDickmanTotalDensityReal_nonneg
    (u : ℝ) :
    0 ≤ poissonDickmanTotalDensityReal u := by
  unfold poissonDickmanTotalDensityReal
  exact ENNReal.toReal_nonneg

theorem poissonDickmanTotalDensityReal_of_nonpos
    {u : ℝ} (hu : u ≤ 0) :
    poissonDickmanTotalDensityReal u = 0 := by
  rw [poissonDickmanTotalDensityReal,
    poissonDickmanTotalDensityFormula_of_nonpos hu]
  simp

theorem poissonDickmanDensityNormalizerReal_pos :
    0 < poissonDickmanDensityNormalizerReal := by
  unfold poissonDickmanDensityNormalizerReal
  exact ENNReal.toReal_pos
    poissonDickmanDensityNormalizer_pos.ne'
    poissonDickmanDensityNormalizer_lt_top.ne

theorem poissonDickmanTotalDensityReal_of_mem_unit
    {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    poissonDickmanTotalDensityReal u =
      poissonDickmanDensityNormalizerReal := by
  unfold poissonDickmanTotalDensityReal
  unfold poissonDickmanDensityNormalizerReal
  rw [poissonDickmanTotalDensityFormula_of_mem_unit
    hu0 hu1]

theorem integrable_poissonDickmanTotalDensityReal :
    Integrable poissonDickmanTotalDensityReal volume := by
  unfold poissonDickmanTotalDensityReal
  apply
    (integrable_toReal_iff
      measurable_poissonDickmanTotalDensityFormula.aemeasurable
      (ae_poissonDickmanTotalDensityFormula_lt_top.mono
        fun _ h ↦ h.ne)).2
  rw [lintegral_poissonDickmanTotalDensityFormula]
  simp

theorem integral_poissonDickmanTotalDensityReal :
    ∫ u : ℝ,
      poissonDickmanTotalDensityReal u ∂volume =
      1 := by
  unfold poissonDickmanTotalDensityReal
  rw [integral_toReal
    measurable_poissonDickmanTotalDensityFormula.aemeasurable
    ae_poissonDickmanTotalDensityFormula_lt_top]
  rw [lintegral_poissonDickmanTotalDensityFormula]
  simp

/-- The integrable kernel appearing in the density tail equation. -/
def poissonDickmanDensityTailKernel (t : ℝ) : ℝ :=
  poissonDickmanTotalDensityReal t / (1 + t)

theorem measurable_poissonDickmanDensityTailKernel :
    Measurable poissonDickmanDensityTailKernel := by
  unfold poissonDickmanDensityTailKernel
  unfold poissonDickmanTotalDensityReal
  exact
    (Measurable.ennreal_toReal
      measurable_poissonDickmanTotalDensityFormula).div
        (measurable_const.add measurable_id)

theorem abs_poissonDickmanDensityTailKernel_le
    (t : ℝ) :
    |poissonDickmanDensityTailKernel t| ≤
      poissonDickmanTotalDensityReal t := by
  by_cases ht : t ≤ 0
  · rw [poissonDickmanDensityTailKernel,
      poissonDickmanTotalDensityReal_of_nonpos ht]
    simp
  · have ht0 : 0 < t := lt_of_not_ge ht
    have hden : 1 ≤ 1 + t := by linarith
    have hdenPos : 0 < 1 + t := by linarith
    rw [poissonDickmanDensityTailKernel,
      abs_of_nonneg
        (div_nonneg
          (poissonDickmanTotalDensityReal_nonneg t)
          hdenPos.le)]
    exact div_le_self
      (poissonDickmanTotalDensityReal_nonneg t)
      hden

theorem integrable_poissonDickmanDensityTailKernel :
    Integrable poissonDickmanDensityTailKernel volume := by
  apply
    integrable_poissonDickmanTotalDensityReal.mono'
      measurable_poissonDickmanDensityTailKernel.aestronglyMeasurable
  exact ae_of_all _ fun t ↦ by
    rw [Real.norm_eq_abs]
    exact abs_poissonDickmanDensityTailKernel_le t

/--
Real form of the density tail equation.
-/
theorem poissonDickmanTotalDensityReal_eq_integral_tail
    {u : ℝ} (hu : 0 < u) :
    poissonDickmanTotalDensityReal u =
      ∫ t : ℝ in Ici (u - 1),
        poissonDickmanDensityTailKernel t
        ∂volume := by
  rw [poissonDickmanTotalDensityReal,
    poissonDickmanTotalDensityFormula_eq_densityTail hu]
  let H : ℝ → ℝ≥0∞ :=
    fun t ↦
      poissonDickmanTotalDensityFormula t *
        ENNReal.ofReal (1 + t)⁻¹
  have hHMeas : AEMeasurable H
      (volume.restrict (Ici (u - 1))) := by
    apply Measurable.aemeasurable
    unfold H
    exact measurable_poissonDickmanTotalDensityFormula.mul
      ((measurable_const.add measurable_id).inv.ennreal_ofReal)
  have hHFinite :
      ∀ᵐ t : ℝ ∂volume.restrict (Ici (u - 1)),
        H t < ∞ := by
    filter_upwards
      [ae_restrict_mem measurableSet_Ici,
        ae_restrict_of_ae
          ae_poissonDickmanTotalDensityFormula_lt_top] with t ht hft
    apply ENNReal.mul_lt_top hft
    exact ENNReal.ofReal_lt_top
  rw [← integral_toReal hHMeas hHFinite]
  apply integral_congr_ae
  filter_upwards
    [ae_restrict_mem measurableSet_Ici,
      ae_restrict_of_ae
        ae_poissonDickmanTotalDensityFormula_lt_top] with t ht hft
  unfold H
  unfold poissonDickmanDensityTailKernel
  unfold poissonDickmanTotalDensityReal
  have hden : 0 ≤ (1 + t)⁻¹ := by
    apply inv_nonneg.mpr
    linarith [mem_Ici.mp ht]
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hden]
  rw [div_eq_mul_inv]

/--
The tail integral regarded as a function of its moving lower
endpoint.
-/
def poissonDickmanDensityTailRepresentation (u : ℝ) : ℝ :=
  ∫ t : ℝ in Ici (u - 1),
    poissonDickmanDensityTailKernel t ∂volume

theorem poissonDickmanDensityTailRepresentation_eq
    (u : ℝ) :
    poissonDickmanDensityTailRepresentation u =
      (∫ t : ℝ in Ici (0 : ℝ),
          poissonDickmanDensityTailKernel t ∂volume) -
        ∫ t : ℝ in (0 : ℝ)..(u - 1),
          poissonDickmanDensityTailKernel t := by
  have hdiff :=
    intervalIntegral.integral_Ici_sub_Ici'
      (μ := volume)
      (a := (0 : ℝ))
      (b := u - 1)
      integrable_poissonDickmanDensityTailKernel.integrableOn
      integrable_poissonDickmanDensityTailKernel.integrableOn
  unfold poissonDickmanDensityTailRepresentation
  linarith

theorem continuous_poissonDickmanDensityTailRepresentation :
    Continuous poissonDickmanDensityTailRepresentation := by
  have hprimitive :
      Continuous
        (fun v : ℝ ↦
          ∫ t : ℝ in (0 : ℝ)..v,
            poissonDickmanDensityTailKernel t) :=
    integrable_poissonDickmanDensityTailKernel.continuous_primitive 0
  have heq :
      poissonDickmanDensityTailRepresentation =
        fun u : ℝ ↦
          (∫ t : ℝ in Ici (0 : ℝ),
              poissonDickmanDensityTailKernel t ∂volume) -
            ∫ t : ℝ in (0 : ℝ)..(u - 1),
              poissonDickmanDensityTailKernel t := by
    funext u
    exact poissonDickmanDensityTailRepresentation_eq u
  rw [heq]
  exact continuous_const.sub
    (hprimitive.comp (continuous_id.sub continuous_const))

theorem poissonDickmanTotalDensityReal_eq_tailRepresentation
    {u : ℝ} (hu : 0 < u) :
    poissonDickmanTotalDensityReal u =
      poissonDickmanDensityTailRepresentation u := by
  exact poissonDickmanTotalDensityReal_eq_integral_tail hu

/--
Although the formula was initially obtained as an `ℝ≥0∞` density,
its real representative is continuous at every positive point.
-/
theorem continuousAt_poissonDickmanTotalDensityReal
    {u : ℝ} (hu : 0 < u) :
    ContinuousAt poissonDickmanTotalDensityReal u := by
  apply
    continuous_poissonDickmanDensityTailRepresentation.continuousAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact poissonDickmanTotalDensityReal_eq_tailRepresentation hv

theorem continuousOn_poissonDickmanTotalDensityReal :
    ContinuousOn poissonDickmanTotalDensityReal (Ioi 0) := by
  intro u hu
  exact
    (continuousAt_poissonDickmanTotalDensityReal hu).continuousWithinAt

theorem continuousAt_poissonDickmanDensityTailKernel
    {t : ℝ} (ht : 0 < t) :
    ContinuousAt poissonDickmanDensityTailKernel t := by
  unfold poissonDickmanDensityTailKernel
  apply ContinuousAt.div
  · exact continuousAt_poissonDickmanTotalDensityReal ht
  · fun_prop
  · linarith

/--
Differential form of the density renewal equation:
`u f'(u) = -f(u-1)` for `u > 1`.
-/
theorem hasDerivAt_poissonDickmanTotalDensityReal
    {u : ℝ} (hu : 1 < u) :
    HasDerivAt poissonDickmanTotalDensityReal
      (-poissonDickmanTotalDensityReal (u - 1) / u) u := by
  have hshift : 0 < u - 1 := by linarith
  have hkernel :=
    continuousAt_poissonDickmanDensityTailKernel hshift
  have hprimitive :
      HasDerivAt
        (fun v : ℝ ↦
          ∫ t : ℝ in (0 : ℝ)..v,
            poissonDickmanDensityTailKernel t)
        (poissonDickmanDensityTailKernel (u - 1))
        (u - 1) :=
    intervalIntegral.integral_hasDerivAt_right
      integrable_poissonDickmanDensityTailKernel.intervalIntegrable
      (ContinuousAt.stronglyMeasurableAtFilter
        isOpen_Ioi
        (fun t ht ↦
          continuousAt_poissonDickmanDensityTailKernel ht)
        (u - 1) hshift)
      hkernel
  have htail :
      HasDerivAt poissonDickmanDensityTailRepresentation
        (-poissonDickmanDensityTailKernel (u - 1)) u := by
    have hraw :=
      (hasDerivAt_const u
        (∫ t : ℝ in Ici (0 : ℝ),
          poissonDickmanDensityTailKernel t ∂volume)).sub
        (hprimitive.comp u
          ((hasDerivAt_id' u).sub_const 1))
    have hevent :
        poissonDickmanDensityTailRepresentation =ᶠ[nhds u]
          ((fun _ : ℝ ↦
              ∫ t : ℝ in Ici (0 : ℝ),
                poissonDickmanDensityTailKernel t ∂volume) -
            (fun v : ℝ ↦
              ∫ t : ℝ in (0 : ℝ)..v,
                poissonDickmanDensityTailKernel t) ∘
              fun v : ℝ ↦ v - 1) := by
      filter_upwards with v
      rw [poissonDickmanDensityTailRepresentation_eq]
      rfl
    have hconverted := hraw.congr_of_eventuallyEq hevent
    exact hconverted.congr_deriv (by ring)
  have heq :
      poissonDickmanTotalDensityReal =ᶠ[nhds u]
        poissonDickmanDensityTailRepresentation := by
    filter_upwards [Ioi_mem_nhds (lt_trans zero_lt_one hu)] with v hv
    exact poissonDickmanTotalDensityReal_eq_tailRepresentation hv
  have hfinal := htail.congr_of_eventuallyEq heq
  exact hfinal.congr_deriv (by
    unfold poissonDickmanDensityTailKernel
    ring)

theorem deriv_poissonDickmanTotalDensityReal
    {u : ℝ} (hu : 1 < u) :
    deriv poissonDickmanTotalDensityReal u =
      -poissonDickmanTotalDensityReal (u - 1) / u :=
  (hasDerivAt_poissonDickmanTotalDensityReal hu).deriv

theorem poissonDickmanDensityTailKernel_nonneg
    (t : ℝ) :
    0 ≤ poissonDickmanDensityTailKernel t := by
  by_cases ht : t ≤ 0
  · rw [poissonDickmanDensityTailKernel,
      poissonDickmanTotalDensityReal_of_nonpos ht]
    simp
  · exact div_nonneg
      (poissonDickmanTotalDensityReal_nonneg t)
      (by linarith)

/--
The renewal equation propagates strict positivity from the unit
interval to every bounded positive interval.
-/
theorem poissonDickmanTotalDensityReal_pos_nat
    (n : ℕ) {u : ℝ} (hu : 0 < u)
    (hun : u < (n : ℝ) + 1) :
    0 < poissonDickmanTotalDensityReal u := by
  induction n generalizing u with
  | zero =>
      rw [Nat.cast_zero, zero_add] at hun
      rw [poissonDickmanTotalDensityReal_of_mem_unit hu hun.le]
      exact poissonDickmanDensityNormalizerReal_pos
  | succ n ih =>
      by_cases hu1 : u ≤ 1
      · rw [poissonDickmanTotalDensityReal_of_mem_unit hu hu1]
        exact poissonDickmanDensityNormalizerReal_pos
      · rw [poissonDickmanTotalDensityReal_eq_integral_tail hu]
        let a : ℝ := max 0 (u - 1)
        let b : ℝ := (a + ((n : ℝ) + 1)) / 2
        have hun' : u < (n : ℝ) + 2 := by
          norm_num [Nat.cast_succ] at hun
          linarith
        have haTop : a < (n : ℝ) + 1 := by
          dsimp only [a]
          rw [max_lt_iff]
          constructor
          · positivity
          · linarith
        have hab : a < b := by
          dsimp only [b]
          linarith
        have hbTop : b < (n : ℝ) + 1 := by
          dsimp only [b]
          linarith
        have hsubset :
            Ioo a b ⊆
              Function.support poissonDickmanDensityTailKernel ∩
                Ici (u - 1) := by
          intro t ht
          have ht0 : 0 < t := by
            have ha0 : 0 ≤ a := by
              dsimp only [a]
              exact le_max_left _ _
            linarith [ht.1]
          have htTop : t < (n : ℝ) + 1 := by
            linarith [ht.2, hbTop]
          have hft :
              0 < poissonDickmanTotalDensityReal t :=
            ih ht0 htTop
          constructor
          · change poissonDickmanDensityTailKernel t ≠ 0
            exact (div_pos hft (by linarith)).ne'
          · exact mem_Ici.mpr <| by
              have haLower : u - 1 ≤ a := by
                dsimp only [a]
                exact le_max_right _ _
              linarith [ht.1]
        apply
          (setIntegral_pos_iff_support_of_nonneg_ae
            (s := Ici (u - 1))
            (ae_restrict_of_ae <|
              ae_of_all _ fun t ↦
                poissonDickmanDensityTailKernel_nonneg t)
            integrable_poissonDickmanDensityTailKernel.integrableOn).2
        exact lt_of_lt_of_le
          (by
            rw [Real.volume_Ioo]
            exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
          (measure_mono hsubset)

/-- The explicit real density is strictly positive at every positive point. -/
theorem poissonDickmanTotalDensityReal_pos
    {u : ℝ} (hu : 0 < u) :
    0 < poissonDickmanTotalDensityReal u := by
  obtain ⟨n : ℕ, hn : u < n⟩ := exists_nat_gt u
  exact poissonDickmanTotalDensityReal_pos_nat n hu
    (hn.trans_le (by exact_mod_cast Nat.le_add_right n 1))

/--
The canonical zero-extended Dickman profile obtained by normalizing
the explicit density.  The density itself vanishes at the single
endpoint `0`; the Dickman profile takes its standard right-continuous
value `1` there.
-/
def poissonDickmanProfile (u : ℝ) : ℝ :=
  if u = 0 then 1
  else
    poissonDickmanTotalDensityReal u /
      poissonDickmanDensityNormalizerReal

theorem poissonDickmanProfile_of_ne_zero
    {u : ℝ} (hu : u ≠ 0) :
    poissonDickmanProfile u =
      poissonDickmanTotalDensityReal u /
        poissonDickmanDensityNormalizerReal := by
  simp [poissonDickmanProfile, hu]

theorem poissonDickmanProfile_of_neg
    {u : ℝ} (hu : u < 0) :
    poissonDickmanProfile u = 0 := by
  rw [poissonDickmanProfile_of_ne_zero hu.ne]
  rw [poissonDickmanTotalDensityReal_of_nonpos hu.le]
  simp

theorem poissonDickmanProfile_of_mem_unit
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    poissonDickmanProfile u = 1 := by
  by_cases hu : u = 0
  · simp [poissonDickmanProfile, hu]
  · rw [poissonDickmanProfile_of_ne_zero hu,
      poissonDickmanTotalDensityReal_of_mem_unit
        (lt_of_le_of_ne hu0 (Ne.symm hu)) hu1]
    exact div_self poissonDickmanDensityNormalizerReal_pos.ne'

theorem poissonDickmanTotalDensityReal_le_normalizer
    {u : ℝ} (hu : 0 < u) :
    poissonDickmanTotalDensityReal u ≤
      poissonDickmanDensityNormalizerReal := by
  unfold poissonDickmanTotalDensityReal
  unfold poissonDickmanDensityNormalizerReal
  exact
    (ENNReal.toReal_le_toReal
      (poissonDickmanTotalDensityFormula_lt_top hu).ne
      poissonDickmanDensityNormalizer_lt_top.ne).2
        (poissonDickmanTotalDensityFormula_le_normalizer hu)

theorem poissonDickmanProfile_nonneg
    {u : ℝ} (_hu : 0 ≤ u) :
    0 ≤ poissonDickmanProfile u := by
  by_cases hu0 : u = 0
  · simp [poissonDickmanProfile, hu0]
  · rw [poissonDickmanProfile_of_ne_zero hu0]
    exact div_nonneg
      (poissonDickmanTotalDensityReal_nonneg u)
      poissonDickmanDensityNormalizerReal_pos.le

theorem poissonDickmanProfile_pos
    {u : ℝ} (hu : 0 ≤ u) :
    0 < poissonDickmanProfile u := by
  by_cases hu0 : u = 0
  · simp [poissonDickmanProfile, hu0]
  · rw [poissonDickmanProfile_of_ne_zero hu0]
    exact div_pos
      (poissonDickmanTotalDensityReal_pos
        (lt_of_le_of_ne hu (Ne.symm hu0)))
      poissonDickmanDensityNormalizerReal_pos

theorem poissonDickmanProfile_le_one
    {u : ℝ} (hu : 0 ≤ u) :
    poissonDickmanProfile u ≤ 1 := by
  by_cases hu0 : u = 0
  · simp [poissonDickmanProfile, hu0]
  · rw [poissonDickmanProfile_of_ne_zero hu0]
    apply (div_le_one poissonDickmanDensityNormalizerReal_pos).2
    exact poissonDickmanTotalDensityReal_le_normalizer
      (lt_of_le_of_ne hu (Ne.symm hu0))

theorem poissonDickmanDensityTailKernel_le_normalizer
    (t : ℝ) :
    poissonDickmanDensityTailKernel t ≤
      poissonDickmanDensityNormalizerReal := by
  by_cases ht : t ≤ 0
  · rw [poissonDickmanDensityTailKernel,
      poissonDickmanTotalDensityReal_of_nonpos ht]
    simpa using poissonDickmanDensityNormalizerReal_pos.le
  · have ht0 : 0 < t := lt_of_not_ge ht
    calc
      poissonDickmanDensityTailKernel t ≤
          poissonDickmanTotalDensityReal t := by
        unfold poissonDickmanDensityTailKernel
        exact div_le_self
          (poissonDickmanTotalDensityReal_nonneg t)
          (by linarith)
      _ ≤ poissonDickmanDensityNormalizerReal :=
        poissonDickmanTotalDensityReal_le_normalizer ht0

theorem abs_poissonDickmanTotalDensityReal_sub_le
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    |poissonDickmanTotalDensityReal u -
        poissonDickmanTotalDensityReal v| ≤
      poissonDickmanDensityNormalizerReal * |u - v| := by
  have hdiff :
      poissonDickmanTotalDensityReal u -
          poissonDickmanTotalDensityReal v =
        ∫ t : ℝ in (u - 1)..(v - 1),
          poissonDickmanDensityTailKernel t := by
    rw [poissonDickmanTotalDensityReal_eq_tailRepresentation hu,
      poissonDickmanTotalDensityReal_eq_tailRepresentation hv,
      poissonDickmanDensityTailRepresentation_eq,
      poissonDickmanDensityTailRepresentation_eq]
    calc
      ((∫ t : ℝ in Ici (0 : ℝ),
              poissonDickmanDensityTailKernel t ∂volume) -
            ∫ t : ℝ in (0 : ℝ)..(u - 1),
              poissonDickmanDensityTailKernel t) -
          ((∫ t : ℝ in Ici (0 : ℝ),
                poissonDickmanDensityTailKernel t ∂volume) -
            ∫ t : ℝ in (0 : ℝ)..(v - 1),
              poissonDickmanDensityTailKernel t) =
        (∫ t : ℝ in (0 : ℝ)..(v - 1),
            poissonDickmanDensityTailKernel t) -
          ∫ t : ℝ in (0 : ℝ)..(u - 1),
            poissonDickmanDensityTailKernel t := by ring
      _ = ∫ t : ℝ in (u - 1)..(v - 1),
          poissonDickmanDensityTailKernel t :=
        intervalIntegral.integral_interval_sub_left
          (integrable_poissonDickmanDensityTailKernel.intervalIntegrable)
          (integrable_poissonDickmanDensityTailKernel.intervalIntegrable)
  rw [hdiff, ← Real.norm_eq_abs]
  have hbound :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (a := u - 1) (b := v - 1)
      (C := poissonDickmanDensityNormalizerReal)
      (f := poissonDickmanDensityTailKernel)
      (fun t _ ↦ by
        rw [Real.norm_eq_abs,
          abs_of_nonneg
            (poissonDickmanDensityTailKernel_nonneg t)]
        exact poissonDickmanDensityTailKernel_le_normalizer t)
  simpa only [sub_sub_sub_cancel_right, abs_sub_comm] using hbound

theorem abs_poissonDickmanProfile_sub_le_of_pos
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    |poissonDickmanProfile u - poissonDickmanProfile v| ≤
      |u - v| := by
  rw [poissonDickmanProfile_of_ne_zero hu.ne',
    poissonDickmanProfile_of_ne_zero hv.ne']
  rw [div_sub_div_same]
  rw [abs_div, abs_of_pos poissonDickmanDensityNormalizerReal_pos]
  apply (div_le_iff₀ poissonDickmanDensityNormalizerReal_pos).2
  simpa [mul_comm] using
    abs_poissonDickmanTotalDensityReal_sub_le hu hv

theorem abs_poissonDickmanProfile_zero_sub_le
    {v : ℝ} (hv : 0 ≤ v) :
    |poissonDickmanProfile 0 - poissonDickmanProfile v| ≤
      |(0 : ℝ) - v| := by
  by_cases hv1 : v ≤ 1
  · rw [poissonDickmanProfile_of_mem_unit (by norm_num) (by norm_num),
      poissonDickmanProfile_of_mem_unit hv hv1]
    simp
  · have hvPos : 0 < v :=
      lt_trans zero_lt_one (lt_of_not_ge hv1)
    have hone :
        |poissonDickmanProfile (1 : ℝ) -
            poissonDickmanProfile v| ≤ |(1 : ℝ) - v| :=
      abs_poissonDickmanProfile_sub_le_of_pos
        zero_lt_one hvPos
    rw [poissonDickmanProfile_of_mem_unit
      (u := (0 : ℝ)) (by norm_num) (by norm_num)]
    rw [poissonDickmanProfile_of_mem_unit
      (u := (1 : ℝ)) (by norm_num) (by norm_num)] at hone
    calc
      |1 - poissonDickmanProfile v| ≤ |1 - v| := hone
      _ ≤ |0 - v| := by
        rw [abs_of_nonpos (by linarith),
          abs_of_nonpos (by linarith)]
        linarith

/-- The normalized probabilistic profile is globally one-Lipschitz on `[0,∞)`. -/
theorem abs_poissonDickmanProfile_sub_le
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |poissonDickmanProfile u - poissonDickmanProfile v| ≤
      |u - v| := by
  by_cases hu0 : u = 0
  · subst u
    exact abs_poissonDickmanProfile_zero_sub_le hv
  · by_cases hv0 : v = 0
    · subst v
      simpa only [abs_sub_comm] using
        abs_poissonDickmanProfile_zero_sub_le hu
    · exact abs_poissonDickmanProfile_sub_le_of_pos
        (lt_of_le_of_ne hu (Ne.symm hu0))
        (lt_of_le_of_ne hv (Ne.symm hv0))

/-- A fixed primitive of the explicit real density. -/
def poissonDickmanTotalDensityPrimitive (u : ℝ) : ℝ :=
  ∫ t : ℝ in (0 : ℝ)..u,
    poissonDickmanTotalDensityReal t

theorem hasDerivAt_poissonDickmanTotalDensityPrimitive
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt poissonDickmanTotalDensityPrimitive
      (poissonDickmanTotalDensityReal u) u := by
  exact
    (intervalIntegral.integral_hasStrictDerivAt_right
      integrable_poissonDickmanTotalDensityReal.intervalIntegrable
      (measurable_poissonDickmanTotalDensityFormula.ennreal_toReal
        ).stronglyMeasurable.stronglyMeasurableAtFilter
      (continuousAt_poissonDickmanTotalDensityReal hu)).hasDerivAt

theorem poissonDickmanTotalDensityPrimitive_sub
    (u : ℝ) :
    poissonDickmanTotalDensityPrimitive u -
        poissonDickmanTotalDensityPrimitive (u - 1) =
      ∫ t : ℝ in (u - 1)..u,
        poissonDickmanTotalDensityReal t := by
  unfold poissonDickmanTotalDensityPrimitive
  exact
    intervalIntegral.integral_interval_sub_left
      integrable_poissonDickmanTotalDensityReal.intervalIntegrable
      integrable_poissonDickmanTotalDensityReal.intervalIntegrable

/-- The difference between the two sides of the density delay identity. -/
def poissonDickmanTotalDensityDelayDefect (u : ℝ) : ℝ :=
  poissonDickmanTotalDensityPrimitive u -
      poissonDickmanTotalDensityPrimitive (u - 1) -
    u * poissonDickmanTotalDensityReal u

theorem hasDerivAt_poissonDickmanTotalDensityDelayDefect
    {u : ℝ} (hu : 1 < u) :
    HasDerivAt poissonDickmanTotalDensityDelayDefect 0 u := by
  have hprim :=
    (hasDerivAt_poissonDickmanTotalDensityPrimitive
      (lt_trans zero_lt_one hu)).sub
      ((hasDerivAt_poissonDickmanTotalDensityPrimitive
        (by linarith)).comp u
        ((hasDerivAt_id' u).sub_const 1))
  have hprod :=
    (hasDerivAt_id' u).mul
      (hasDerivAt_poissonDickmanTotalDensityReal hu)
  unfold poissonDickmanTotalDensityDelayDefect
  convert hprim.sub hprod using 1 <;>
    first
    | rfl
    | (field_simp [ne_of_gt (lt_trans zero_lt_one hu)]; ring)

theorem continuous_poissonDickmanTotalDensityPrimitive :
    Continuous poissonDickmanTotalDensityPrimitive := by
  exact
    integrable_poissonDickmanTotalDensityReal.continuous_primitive 0

theorem continuousOn_poissonDickmanTotalDensityDelayDefect
    {u : ℝ} (_hu : 1 ≤ u) :
    ContinuousOn poissonDickmanTotalDensityDelayDefect
      (Icc (1 : ℝ) u) := by
  unfold poissonDickmanTotalDensityDelayDefect
  apply ContinuousOn.sub
  · exact continuous_poissonDickmanTotalDensityPrimitive.continuousOn.sub
      (continuous_poissonDickmanTotalDensityPrimitive.comp
        (continuous_id.sub continuous_const)).continuousOn
  · exact continuous_id.continuousOn.mul
      (continuousOn_poissonDickmanTotalDensityReal.mono
        (fun t ht ↦ by
          exact mem_Ioi.mpr (zero_lt_one.trans_le ht.1)))

theorem poissonDickmanTotalDensityDelayDefect_one :
    poissonDickmanTotalDensityDelayDefect 1 = 0 := by
  have hint :
      (∫ t : ℝ in (0 : ℝ)..1,
          poissonDickmanTotalDensityReal t) =
        poissonDickmanDensityNormalizerReal := by
    calc
      (∫ t : ℝ in (0 : ℝ)..1,
          poissonDickmanTotalDensityReal t) =
          ∫ _t : ℝ in (0 : ℝ)..1,
            poissonDickmanDensityNormalizerReal := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t ht
        rw [uIoc_of_le (by norm_num)] at ht
        exact poissonDickmanTotalDensityReal_of_mem_unit
          ht.1 ht.2
      _ = poissonDickmanDensityNormalizerReal := by simp
  unfold poissonDickmanTotalDensityDelayDefect
  rw [show
      poissonDickmanTotalDensityPrimitive 1 -
          poissonDickmanTotalDensityPrimitive (1 - 1) =
        ∫ t : ℝ in (0 : ℝ)..1,
          poissonDickmanTotalDensityReal t by
        simpa using poissonDickmanTotalDensityPrimitive_sub 1]
  rw [hint,
    poissonDickmanTotalDensityReal_of_mem_unit
      zero_lt_one le_rfl]
  ring

/--
Integral form of the delay equation for the explicit real density.
-/
theorem poissonDickmanTotalDensityReal_integral_delay
    {u : ℝ} (hu : 1 ≤ u) :
    (∫ t : ℝ in (u - 1)..u,
        poissonDickmanTotalDensityReal t) =
      u * poissonDickmanTotalDensityReal u := by
  by_cases hu1 : u = 1
  · subst u
    have h := poissonDickmanTotalDensityDelayDefect_one
    unfold poissonDickmanTotalDensityDelayDefect at h
    rw [poissonDickmanTotalDensityPrimitive_sub] at h
    norm_num at h ⊢
    linarith
  · have h1u : 1 < u := lt_of_le_of_ne hu (Ne.symm hu1)
    have hderiv :
        ∀ v ∈ Ioo (1 : ℝ) u,
          HasDerivAt poissonDickmanTotalDensityDelayDefect 0 v := by
      intro v hv
      exact
        hasDerivAt_poissonDickmanTotalDensityDelayDefect hv.1
    obtain ⟨v, hv, hslope⟩ :=
      exists_hasDerivAt_eq_slope
        poissonDickmanTotalDensityDelayDefect
        (fun _ ↦ (0 : ℝ)) h1u
        (continuousOn_poissonDickmanTotalDensityDelayDefect hu)
        hderiv
    rw [poissonDickmanTotalDensityDelayDefect_one] at hslope
    have hden : u - 1 ≠ 0 := sub_ne_zero.mpr h1u.ne'
    have hzero :
        poissonDickmanTotalDensityDelayDefect u = 0 :=
      by
        simpa using
          (div_eq_zero_iff.mp hslope.symm).resolve_right hden
    unfold poissonDickmanTotalDensityDelayDefect at hzero
    rw [poissonDickmanTotalDensityPrimitive_sub] at hzero
    linarith

/-- Integral form of the delay equation for the normalized profile. -/
theorem poissonDickmanProfile_integral_delay
    {u : ℝ} (hu : 1 ≤ u) :
    (∫ t : ℝ in (u - 1)..u,
        poissonDickmanProfile t) =
      u * poissonDickmanProfile u := by
  by_cases hu1 : u = 1
  · subst u
    rw [poissonDickmanProfile_of_mem_unit
      (u := (1 : ℝ)) (by norm_num) (by norm_num)]
    have hint :
        (∫ t : ℝ in (0 : ℝ)..1,
            poissonDickmanProfile t) =
          ∫ _t : ℝ in (0 : ℝ)..1, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      exact poissonDickmanProfile_of_mem_unit ht.1 ht.2
    norm_num
    rw [hint]
    simp
  · have hu1' : 1 < u := lt_of_le_of_ne hu (Ne.symm hu1)
    have hprofile :
        (∫ t : ℝ in (u - 1)..u,
            poissonDickmanProfile t) =
          (∫ t : ℝ in (u - 1)..u,
              poissonDickmanTotalDensityReal t) /
            poissonDickmanDensityNormalizerReal := by
      rw [← intervalIntegral.integral_div]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      rw [poissonDickmanProfile_of_ne_zero]
      linarith [hu1', ht.1]
    rw [hprofile,
      poissonDickmanTotalDensityReal_integral_delay hu]
    rw [poissonDickmanProfile_of_ne_zero]
    · ring
    · linarith

end

end Erdos390
