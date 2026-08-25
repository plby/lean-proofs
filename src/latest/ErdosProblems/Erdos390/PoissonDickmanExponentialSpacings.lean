/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
import ErdosProblems.Erdos390.PoissonDickmanConfiguration
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace Erdos390

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance poissonDickmanExpMeasureProbability :
    IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/--
Independent exponential gaps used to realize the scale-invariant
Poisson process.  If `E₀,E₁,…` have this product law, its decreasing
atoms are `exp (-(E₀+⋯+Eₙ))`.
-/
abbrev PoissonDickmanGapSequence := ℕ → ℝ

/-- The product law of independent rate-one exponential gaps. -/
def poissonDickmanGapLaw : Measure PoissonDickmanGapSequence :=
  Measure.infinitePi fun _ : ℕ ↦ expMeasure 1

instance : IsProbabilityMeasure poissonDickmanGapLaw := by
  unfold poissonDickmanGapLaw
  infer_instance

/--
The `n`th logarithmic arrival time.  Truncating a gap below by zero
makes the construction land in `(0,1]` for every input sequence; the
truncation is invisible under the exponential product law.
-/
def poissonDickmanArrival
    (e : PoissonDickmanGapSequence) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), max (e k) 0

/-- The decreasing exponential-spacing configuration. -/
def poissonDickmanSpacingConfiguration
    (e : PoissonDickmanGapSequence) :
    PoissonDickmanConfiguration :=
  fun n ↦ Real.exp (-poissonDickmanArrival e n)

theorem measurable_poissonDickmanArrival
    (n : ℕ) :
    Measurable (fun e ↦ poissonDickmanArrival e n) := by
  apply Finset.measurable_sum
  intro k hk
  exact (measurable_pi_apply k).max measurable_const

theorem measurable_poissonDickmanSpacingConfiguration :
    Measurable poissonDickmanSpacingConfiguration := by
  rw [measurable_pi_iff]
  intro n
  exact
    (measurable_poissonDickmanArrival n).neg.exp

/-- The unconditioned labelled scale-invariant Poisson law. -/
def poissonDickmanUnconditionedLaw :
    Measure PoissonDickmanConfiguration :=
  poissonDickmanGapLaw.map
    poissonDickmanSpacingConfiguration

instance : IsProbabilityMeasure poissonDickmanUnconditionedLaw := by
  unfold poissonDickmanUnconditionedLaw
  exact Measure.isProbabilityMeasure_map
    measurable_poissonDickmanSpacingConfiguration.aemeasurable

theorem poissonDickmanSpacingConfiguration_mem_Ioc
    (e : PoissonDickmanGapSequence) (n : ℕ) :
    poissonDickmanSpacingConfiguration e n ∈ Ioc (0 : ℝ) 1 := by
  constructor
  · exact Real.exp_pos _
  · unfold poissonDickmanSpacingConfiguration
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr <|
      Finset.sum_nonneg fun _ _ ↦
        le_max_right _ _

theorem poissonDickmanSpacingConfiguration_antitone
    (e : PoissonDickmanGapSequence) :
    Antitone (poissonDickmanSpacingConfiguration e) := by
  intro m n hmn
  rw [poissonDickmanSpacingConfiguration,
    poissonDickmanSpacingConfiguration]
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_subset_range.mpr <|
      Nat.add_le_add_right hmn 1
  · intro i hi _
    exact le_max_right _ _

/--
The elementary Laplace-transform value for a rate-one exponential
gap.  This is the numerical input behind the geometric mean
`E exp (-(E₀+⋯+Eₙ)) = 2⁻⁽ⁿ⁺¹⁾`.
-/
theorem integral_exp_neg_expMeasure_one :
    ∫ x : ℝ, Real.exp (-x) ∂expMeasure 1 = (2 : ℝ)⁻¹ := by
  change
    ∫ x : ℝ, Real.exp (-x)
        ∂volume.withDensity (exponentialPDF 1) =
      (2 : ℝ)⁻¹
  have hfun :
      (fun x : ℝ ↦
        (exponentialPDF 1 x).toReal • Real.exp (-x)) =
      (Ici (0 : ℝ)).indicator
        (fun x : ℝ ↦ Real.exp (-(2 * x))) := by
    funext x
    by_cases hx : 0 ≤ x
    · simp only [exponentialPDF_eq,
        one_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
        smul_eq_mul, indicator, mem_Ici, hx, ↓reduceIte]
      rw [← Real.exp_add]
      congr 1
      ring
    · have hx' : x ∉ Ici (0 : ℝ) := hx
      simp [exponentialPDF_eq, hx, hx']
  calc
    _ = ∫ x : ℝ,
          (exponentialPDF 1 x).toReal •
            Real.exp (-x) ∂volume :=
      integral_withDensity_eq_integral_toReal_smul
        (μ := volume) (by fun_prop)
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) _
    _ = ∫ x : ℝ in Ioi 0,
          Real.exp (-(2 * x)) := by
      rw [hfun, integral_indicator measurableSet_Ici,
        integral_Ici_eq_integral_Ioi]
    _ = (2 : ℝ)⁻¹ := by
      convert
        integral_comp_mul_left_Ioi
          (fun x : ℝ ↦ Real.exp (-x)) 0
          (show (0 : ℝ) < 2 by norm_num) using 1
      all_goals simp [integral_exp_Iic_zero]

/-- A rate-one exponential gap is nonnegative almost surely. -/
theorem ae_nonneg_expMeasure_one :
    ∀ᵐ x : ℝ ∂expMeasure 1, 0 ≤ x := by
  have hzero :
      expMeasure 1 (Iic (0 : ℝ)) = 0 := by
    rw [← ofReal_cdf]
    simp [cdf_expMeasure_eq one_pos]
  have hneg :
      expMeasure 1 (Iio (0 : ℝ)) = 0 :=
    measure_mono_null Iio_subset_Iic_self hzero
  exact
    (measure_eq_zero_iff_ae_notMem.mp hneg).mono
      fun x hx ↦ not_lt.mp hx

theorem integral_exp_neg_max_expMeasure_one :
    ∫ x : ℝ, Real.exp (-max x 0) ∂expMeasure 1 =
      (2 : ℝ)⁻¹ := by
  rw [← integral_exp_neg_expMeasure_one]
  apply integral_congr_ae
  filter_upwards [ae_nonneg_expMeasure_one] with x hx
  rw [max_eq_left hx]

theorem poissonDickmanSpacingConfiguration_eq_prod
    (e : PoissonDickmanGapSequence) (n : ℕ) :
    poissonDickmanSpacingConfiguration e n =
      ∏ k ∈ Finset.range (n + 1),
        Real.exp (-max (e k) 0) := by
  unfold poissonDickmanSpacingConfiguration
  rw [← Real.exp_sum]
  congr 1
  rw [poissonDickmanArrival, Finset.sum_neg_distrib]

theorem integral_poissonDickmanGapCoordinate
    (i : ℕ) :
    ∫ e : PoissonDickmanGapSequence,
        Real.exp (-max (e i) 0)
      ∂poissonDickmanGapLaw =
      (2 : ℝ)⁻¹ := by
  calc
    _ = ∫ x : ℝ, Real.exp (-max x 0)
          ∂poissonDickmanGapLaw.map
            (fun e : PoissonDickmanGapSequence ↦ e i) :=
      (integral_map
        (μ := poissonDickmanGapLaw)
        (φ := fun e : PoissonDickmanGapSequence ↦ e i)
        (measurable_pi_apply i).aemeasurable
        (by fun_prop)).symm
    _ = ∫ x : ℝ, Real.exp (-max x 0)
          ∂expMeasure 1 := by
      rw [poissonDickmanGapLaw,
        Measure.infinitePi_map_eval]
    _ = (2 : ℝ)⁻¹ :=
      integral_exp_neg_max_expMeasure_one

/--
The mean of the `n`th atom is geometric.  In particular the expected
total mass of the exponential-spacing configuration is finite.
-/
theorem integral_poissonDickmanSpacingConfiguration
    (n : ℕ) :
    ∫ e : PoissonDickmanGapSequence,
        poissonDickmanSpacingConfiguration e n
      ∂poissonDickmanGapLaw =
      ((2 : ℝ)⁻¹) ^ (n + 1) := by
  simp_rw [poissonDickmanSpacingConfiguration_eq_prod]
  let s := Finset.range (n + 1)
  have hIndepNat :
      iIndepFun
        (fun i : ℕ ↦
          fun e : PoissonDickmanGapSequence ↦ e i)
        poissonDickmanGapLaw := by
    unfold poissonDickmanGapLaw
    exact iIndepFun_infinitePi
      (X := fun _ : ℕ ↦ id) fun _ ↦
        measurable_id
  have hIndep :
      iIndepFun
        (fun i : {i // i ∈ s} ↦
          fun e : PoissonDickmanGapSequence ↦ e i.1)
        poissonDickmanGapLaw :=
    hIndepNat.precomp Subtype.val_injective
  have hprod :=
    hIndep.integral_fun_prod_comp
      (f := fun _ : {i // i ∈ s} ↦
        fun x : ℝ ↦ Real.exp (-max x 0))
      (fun i ↦ (measurable_pi_apply i.1).aemeasurable)
      (fun _ ↦ (by fun_prop))
  calc
    (∫ e : PoissonDickmanGapSequence,
        ∏ k ∈ Finset.range (n + 1),
          Real.exp (-max (e k) 0)
        ∂poissonDickmanGapLaw) =
        ∫ e : PoissonDickmanGapSequence,
          ∏ i : {i // i ∈ s},
            Real.exp (-max (e i.1) 0)
          ∂poissonDickmanGapLaw := by
      apply integral_congr_ae
      exact ae_of_all _ fun e ↦ by
        simpa [s] using
          (Finset.prod_attach
            (Finset.range (n + 1))
            (fun k ↦ Real.exp (-max (e k) 0))).symm
    _ =
        ∏ i : {i // i ∈ s},
          ∫ e : PoissonDickmanGapSequence,
            Real.exp (-max (e i.1) 0)
            ∂poissonDickmanGapLaw :=
      hprod
    _ = ((2 : ℝ)⁻¹) ^ (n + 1) := by
      simp [integral_poissonDickmanGapCoordinate, s]

theorem measurable_poissonDickmanSpacingCoordinate
    (n : ℕ) :
    Measurable
      (fun e : PoissonDickmanGapSequence ↦
        poissonDickmanSpacingConfiguration e n) :=
  (measurable_pi_apply n).comp
    measurable_poissonDickmanSpacingConfiguration

theorem integrable_poissonDickmanSpacingCoordinate
    (n : ℕ) :
    Integrable
      (fun e : PoissonDickmanGapSequence ↦
        poissonDickmanSpacingConfiguration e n)
      poissonDickmanGapLaw := by
  apply Integrable.of_bound
    (measurable_poissonDickmanSpacingCoordinate n).aestronglyMeasurable
    1
  exact ae_of_all _ fun e ↦ by
    rw [Real.norm_eq_abs,
      abs_of_pos
        (poissonDickmanSpacingConfiguration_mem_Ioc e n).1]
    exact
      (poissonDickmanSpacingConfiguration_mem_Ioc e n).2

theorem lintegral_poissonDickmanSpacingConfiguration
    (n : ℕ) :
    ∫⁻ e : PoissonDickmanGapSequence,
        ENNReal.ofReal
          (poissonDickmanSpacingConfiguration e n)
      ∂poissonDickmanGapLaw =
      ((2 : ℝ≥0∞)⁻¹) ^ (n + 1) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_poissonDickmanSpacingCoordinate n)
    (ae_of_all _ fun e ↦
      (poissonDickmanSpacingConfiguration_mem_Ioc e n).1.le)]
  rw [integral_poissonDickmanSpacingConfiguration]
  rw [ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by ring,
    ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 2 by norm_num)]
  norm_num

/--
Tonelli turns the geometric coordinate means into a finite mean for
the whole configuration.  In fact that mean is exactly one.
-/
theorem lintegral_poissonDickmanSpacingTotal :
    ∫⁻ e : PoissonDickmanGapSequence,
        ∑' n : ℕ,
          ENNReal.ofReal
            (poissonDickmanSpacingConfiguration e n)
      ∂poissonDickmanGapLaw = 1 := by
  rw [lintegral_tsum fun n ↦
    (measurable_poissonDickmanSpacingCoordinate n).ennreal_ofReal.aemeasurable]
  simp_rw [lintegral_poissonDickmanSpacingConfiguration]
  rw [ENNReal.tsum_geometric_add_one]
  rw [ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel
    (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)

theorem ae_poissonDickmanSpacingTotal_lt_top :
    ∀ᵐ e : PoissonDickmanGapSequence
      ∂poissonDickmanGapLaw,
      (∑' n : ℕ,
        ENNReal.ofReal
          (poissonDickmanSpacingConfiguration e n)) < ∞ := by
  have hmeas :
      Measurable
        (fun e : PoissonDickmanGapSequence ↦
          ∑' n : ℕ,
            ENNReal.ofReal
              (poissonDickmanSpacingConfiguration e n)) :=
    Measurable.tsum fun n ↦
      (measurable_poissonDickmanSpacingCoordinate n).ennreal_ofReal
  apply ae_lt_top hmeas
  rw [lintegral_poissonDickmanSpacingTotal]
  simp

theorem ae_summable_poissonDickmanSpacingConfiguration :
    ∀ᵐ e : PoissonDickmanGapSequence
      ∂poissonDickmanGapLaw,
      Summable (poissonDickmanSpacingConfiguration e) := by
  filter_upwards [ae_poissonDickmanSpacingTotal_lt_top] with e he
  let a : ℕ → NNReal :=
    fun n ↦
      Real.toNNReal
        (poissonDickmanSpacingConfiguration e n)
  have ha :
      Summable fun n : ℕ ↦ (a n : ℝ) := by
    apply ENNReal.tsum_coe_ne_top_iff_summable_coe.mp
    simpa [a, ENNReal.ofReal] using he.ne
  simpa [a, Real.coe_toNNReal',
    max_eq_left
      (poissonDickmanSpacingConfiguration_mem_Ioc e _).1.le] using ha

/--
A measurable support predicate equivalent to absolute summability on
configurations whose coordinates lie in `[0,1]`.
-/
def IsPoissonDickmanAbsolutelySummableConfiguration
    (π : PoissonDickmanConfiguration) : Prop :=
  (∀ n, π n ∈ Icc (0 : ℝ) 1) ∧
    (∑' n : ℕ, ENNReal.ofReal |π n|) < ∞

theorem measurableSet_isPoissonDickmanAbsolutelySummableConfiguration :
    MeasurableSet
      {π : PoissonDickmanConfiguration |
        IsPoissonDickmanAbsolutelySummableConfiguration π} := by
  have hcoords :
      MeasurableSet
        {π : PoissonDickmanConfiguration |
          ∀ n, π n ∈ Icc (0 : ℝ) 1} := by
    rw [show
      {π : PoissonDickmanConfiguration |
        ∀ n, π n ∈ Icc (0 : ℝ) 1} =
        ⋂ n : ℕ,
          (fun π : PoissonDickmanConfiguration ↦ π n) ⁻¹'
            Icc (0 : ℝ) 1 by
      ext π
      simp]
    exact MeasurableSet.iInter fun n ↦
      (measurable_pi_apply n) measurableSet_Icc
  have hmass :
      Measurable
        (fun π : PoissonDickmanConfiguration ↦
          ∑' n : ℕ, ENNReal.ofReal |π n|) :=
    Measurable.tsum fun n ↦
      ((continuous_abs.measurable.comp
        (measurable_pi_apply n :
          Measurable
            (fun π : PoissonDickmanConfiguration ↦
              π n))).ennreal_ofReal)
  exact hcoords.inter <|
    measurableSet_lt hmass measurable_const

theorem
    IsPoissonDickmanAbsolutelySummableConfiguration.toSummableConfiguration
    {π : PoissonDickmanConfiguration}
    (hπ : IsPoissonDickmanAbsolutelySummableConfiguration π) :
    IsPoissonDickmanSummableConfiguration π := by
  refine ⟨hπ.1, ?_⟩
  let a : ℕ → NNReal :=
    fun n ↦ Real.toNNReal |π n|
  have ha :
      Summable fun n : ℕ ↦ (a n : ℝ) := by
    apply ENNReal.tsum_coe_ne_top_iff_summable_coe.mp
    simpa [a, ENNReal.ofReal] using hπ.2.ne
  have habs : Summable fun n : ℕ ↦ |π n| := by
    simpa [a, Real.coe_toNNReal', abs_nonneg] using ha
  apply summable_norm_iff.mp
  simpa only [Real.norm_eq_abs] using habs

theorem ae_poissonDickmanUnconditionedLaw_support :
    ∀ᵐ π : PoissonDickmanConfiguration
      ∂poissonDickmanUnconditionedLaw,
      IsPoissonDickmanSummableConfiguration π := by
  have hpre :
      ∀ᵐ e : PoissonDickmanGapSequence
        ∂poissonDickmanGapLaw,
        IsPoissonDickmanAbsolutelySummableConfiguration
          (poissonDickmanSpacingConfiguration e) := by
    filter_upwards [ae_poissonDickmanSpacingTotal_lt_top] with e he
    constructor
    · intro n
      exact
        ⟨(poissonDickmanSpacingConfiguration_mem_Ioc e n).1.le,
          (poissonDickmanSpacingConfiguration_mem_Ioc e n).2⟩
    · simpa only [
        abs_of_pos
          (poissonDickmanSpacingConfiguration_mem_Ioc e _).1] using he
  have htarget :
      ∀ᵐ π : PoissonDickmanConfiguration
        ∂poissonDickmanUnconditionedLaw,
        IsPoissonDickmanAbsolutelySummableConfiguration π := by
    unfold poissonDickmanUnconditionedLaw
    exact
      (ae_map_iff
        measurable_poissonDickmanSpacingConfiguration.aemeasurable
        measurableSet_isPoissonDickmanAbsolutelySummableConfiguration).2
        hpre
  exact htarget.mono fun _ hπ ↦
    hπ.toSummableConfiguration

end

end Erdos390
