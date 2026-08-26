import ErdosProblems.Erdos1002.PoissonCompat
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Characteristic functions for Poisson and fixed-jump compound Poisson laws

This file derives the probability generating function of `poissonMeasure` directly from
the defining probability mass function.  In particular, the proof records the absolute
summability needed to pass from the Bochner integral to the exponential series.
-/

open scoped ENNReal NNReal Nat

open MeasureTheory Real Set Filter Topology

namespace Erdos1002

open ProbabilityTheory

/-- The real mass appearing in `poissonPMF` is exactly `poissonPMFReal`. -/
lemma poissonPMF_toReal (r : ℝ≥0) (n : ℕ) :
    (poissonPMF r n).toReal = poissonPMFReal r n := by
  change (ENNReal.ofReal (poissonPMFReal r n)).toReal = poissonPMFReal r n
  exact ENNReal.toReal_ofReal poissonPMFReal_nonneg

/-- The Poisson generating-function summand is absolutely summable for every complex
argument.  This is the integrability input needed below. -/
lemma summable_poissonPMFReal_mul_pow (r : ℝ≥0) (z : ℂ) :
    Summable (fun n : ℕ ↦ (poissonPMFReal r n : ℂ) * z ^ n) := by
  have hExp : Summable (fun n : ℕ ↦ (((r : ℝ) * ‖z‖) : ℝ) ^ n / n !) :=
    NormedSpace.expSeries_div_summable (((r : ℝ) * ‖z‖) : ℝ)
  apply Summable.of_norm
  apply (hExp.mul_left (Real.exp (-(r : ℝ)))).congr
  intro n
  rw [poissonPMFReal, norm_mul, Complex.norm_real, norm_pow, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]
  rw [mul_pow]
  ring

/-- The defining Poisson mass is integrable against every complex geometric sequence. -/
lemma integrable_pow_poissonMeasure (r : ℝ≥0) (z : ℂ) :
    Integrable (fun n : ℕ ↦ z ^ n) (poissonMeasure r) := by
  refine ⟨StronglyMeasurable.of_discrete.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm, lintegral_countable']
  simp_rw [poissonMeasure_eq_toMeasure, PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    norm_pow]
  have hs : Summable (fun n : ℕ ↦ poissonPMFReal r n * ‖z‖ ^ n) := by
    simpa only [Complex.norm_real, norm_pow, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg poissonPMFReal_nonneg] using!
      (summable_poissonPMFReal_mul_pow r z).norm
  calc
    (∑' n : ℕ, ENNReal.ofReal (‖z‖ ^ n) *
        poissonPMF r n) =
        ∑' n : ℕ, ENNReal.ofReal (poissonPMFReal r n * ‖z‖ ^ n) := by
      apply tsum_congr
      intro n
      rw [show poissonPMF r n = ENNReal.ofReal (poissonPMFReal r n) by rfl]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ < ∞ := hs.tsum_ofReal_lt_top

/-- The probability generating function of the Poisson law, valid for every complex
argument `z` (not merely for `‖z‖ ≤ 1`). -/
theorem integral_pow_poissonMeasure (r : ℝ≥0) (z : ℂ) :
    ∫ n : ℕ, z ^ n ∂(poissonMeasure r) =
      Complex.exp ((r : ℂ) * (z - 1)) := by
  rw [poissonMeasure_eq_toMeasure, PMF.integral_eq_tsum _ _ (by
    simpa only [poissonMeasure_eq_toMeasure] using! integrable_pow_poissonMeasure r z)]
  simp_rw [poissonPMF_toReal, poissonPMFReal, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_exp, Complex.ofReal_neg,
    Complex.ofReal_natCast]
  rw [show (fun n : ℕ ↦ Complex.exp (-(r : ℂ)) * (r : ℂ) ^ n / n ! * z ^ n) =
      (fun n : ℕ ↦ Complex.exp (-(r : ℂ)) * (((r : ℂ) ^ n / n !) * z ^ n)) by
    funext n
    ring]
  rw [tsum_mul_left]
  rw [show (fun n : ℕ ↦ ((r : ℂ) ^ n / n !) * z ^ n) =
      (fun n : ℕ ↦ (((r : ℂ) * z) ^ n / n !)) by
    funext n
    rw [mul_pow]
    ring]
  rw [(NormedSpace.expSeries_div_hasSum_exp ((r : ℂ) * z)).tsum_eq]
  rw [← Complex.exp_eq_exp_ℂ]
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The characteristic function of a Poisson random variable, written as an integral
on its canonical sample space `ℕ`. -/
theorem integral_probChar_poissonMeasure (r : ℝ≥0) (t : ℝ) :
    ∫ n : ℕ, Complex.exp (t * (n : ℝ) * Complex.I) ∂(poissonMeasure r) =
      Complex.exp ((r : ℂ) * (Complex.exp (t * Complex.I) - 1)) := by
  rw [show (fun n : ℕ ↦ Complex.exp (t * (n : ℝ) * Complex.I)) =
      (fun n : ℕ ↦ Complex.exp (t * Complex.I) ^ n) by
    funext n
    rw [← Complex.exp_nsmul]
    congr 1
    push_cast
    ring]
  exact integral_pow_poissonMeasure r (Complex.exp (t * Complex.I))

/-- The law on `ℝ` of `x` times a Poisson random variable. -/
noncomputable def fixedJumpPoissonMeasure (r : ℝ≥0) (x : ℝ) : Measure ℝ :=
  (poissonMeasure r).map (fun n : ℕ ↦ (n : ℝ) * x)

instance fixedJumpPoissonMeasure.isProbabilityMeasure (r : ℝ≥0) (x : ℝ) :
    IsProbabilityMeasure (fixedJumpPoissonMeasure r x) := by
  unfold fixedJumpPoissonMeasure
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- The characteristic function of the fixed-jump compound Poisson law. -/
theorem charFun_fixedJumpPoissonMeasure (r : ℝ≥0) (x t : ℝ) :
    charFun (fixedJumpPoissonMeasure r x) t =
      Complex.exp ((r : ℂ) * (Complex.exp (t * x * Complex.I) - 1)) := by
  rw [charFun_apply_real, fixedJumpPoissonMeasure]
  rw [integral_map]
  · convert! integral_probChar_poissonMeasure r (t * x) using 1
    · apply integral_congr_ae
      filter_upwards [] with n
      congr 1
      push_cast
      ring
    · congr 2
      push_cast
      ring
  · exact (measurable_of_countable (fun n : ℕ ↦ (n : ℝ) * x)).aemeasurable
  · fun_prop

/-- Characteristic functions multiply for a finite sum of independent real random variables.
The statement is phrased for an arbitrary finite set so it can be reused for truncations. -/
theorem charFun_map_finset_sum_eq_prod
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X P) (s : Finset ι) (t : ℝ) :
    charFun (P.map (fun ω ↦ ∑ i ∈ s, X i ω)) t =
      ∏ i ∈ s, charFun (P.map (X i)) t := by
  induction s using Finset.induction_on with
  | empty =>
      simp [Measure.map_const]
  | @insert i s hi hs =>
      have hsum : Measurable (fun ω ↦ ∑ j ∈ s, X j ω) := by
        fun_prop
      have hsum_eq : (∑ j ∈ s, X j) = (fun ω ↦ ∑ j ∈ s, X j ω) := by
        funext ω
        simp only [Finset.sum_apply]
      have hIndep' : X i ⟂ᵢ[P] (fun ω ↦ ∑ j ∈ s, X j ω) := by
        have hbase := (hIndep.indepFun_finset_sum_of_notMem hX hi).symm
        rw [hsum_eq] at hbase
        exact hbase
      have hcf := IndepFun.charFun_map_add_eq_mul
        (P := P) (X := X i) (Y := fun ω ↦ ∑ j ∈ s, X j ω)
        (hX i).aemeasurable hsum.aemeasurable hIndep'
      simp only [Finset.sum_insert hi, Finset.prod_insert hi]
      change charFun (P.map (X i + fun ω ↦ ∑ j ∈ s, X j ω)) t = _
      rw [congrFun hcf t]
      change charFun (P.map (X i)) t *
        charFun (P.map (fun ω ↦ ∑ j ∈ s, X j ω)) t = _
      rw [hs]

/-- A finite sum of independent fixed-jump Poisson variables has the expected product
characteristic function.  `hLaw i` identifies the law of the `i`th summand exactly. -/
theorem charFun_independent_fixedJumpPoisson_sum
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X P) (rate : ι → ℝ≥0) (jump : ι → ℝ)
    (hLaw : ∀ i, HasLaw (X i) (fixedJumpPoissonMeasure (rate i) (jump i)) P)
    (s : Finset ι) (t : ℝ) :
    charFun (P.map (fun ω ↦ ∑ i ∈ s, X i ω)) t =
      ∏ i ∈ s, Complex.exp ((rate i : ℂ) *
        (Complex.exp (t * jump i * Complex.I) - 1)) := by
  rw [charFun_map_finset_sum_eq_prod P X hX hIndep s t]
  apply Finset.prod_congr rfl
  intro i hi
  rw [(hLaw i).map_eq, charFun_fixedJumpPoissonMeasure]

/-- Exponential-of-a-sum form of the preceding finite compound-Poisson formula. -/
theorem charFun_independent_fixedJumpPoisson_sum_exp
    {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hIndep : iIndepFun X P) (rate : ι → ℝ≥0) (jump : ι → ℝ)
    (hLaw : ∀ i, HasLaw (X i) (fixedJumpPoissonMeasure (rate i) (jump i)) P)
    (s : Finset ι) (t : ℝ) :
    charFun (P.map (fun ω ↦ ∑ i ∈ s, X i ω)) t =
      Complex.exp (∑ i ∈ s, (rate i : ℂ) *
        (Complex.exp (t * jump i * Complex.I) - 1)) := by
  rw [charFun_independent_fixedJumpPoisson_sum P X hX hIndep rate jump hLaw s t]
  rw [Complex.exp_sum]

end Erdos1002
