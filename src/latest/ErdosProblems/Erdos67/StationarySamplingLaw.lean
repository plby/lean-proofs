import ErdosProblems.Erdos67.StationaryModel
import ErdosProblems.Erdos67.StationaryDilationAverage
import ErdosProblems.Erdos67.StationaryHarmonicAverage

/-!
# The finite sampling laws

The dilation is sampled uniformly from an exponent box, and the starting point
has harmonic weights. Both variables are finite and independent.
-/

open scoped BigOperators Topology
open Finset Filter
open MeasureTheory hiding average

namespace Erdos67.StationaryModel

open FiniteEntropy StationaryDilationAverage StationaryHarmonicAverage

/-- Harmonic weights on the positive integers `1,…,t+1`. -/
noncomputable def harmonicVector (t : ℕ) : FinProb (Fin (t + 1)) :=
  ⟨fun n ↦ ((n.val + 1 : ℕ) : ℝ)⁻¹ / mass (t + 1), by
    constructor
    · intro n
      exact div_nonneg (by positivity) (mass_pos (Nat.succ_pos t)).le
    · rw [← Finset.sum_div,
        Fin.sum_univ_eq_sum_range (fun n ↦ ((n + 1 : ℕ) : ℝ)⁻¹) (t + 1)]
      exact div_self (mass_pos (Nat.succ_pos t)).ne'⟩

theorem harmonicVector_expectation (t : ℕ) (F : ℕ → ℝ) :
    (∑ n : Fin (t + 1), harmonicVector t n * F (n.val + 1)) = average (t + 1) F := by
  change (∑ n : Fin (t + 1), (((n.val + 1 : ℕ) : ℝ)⁻¹ / mass (t + 1)) *
    F (n.val + 1)) = _
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div,
    Fin.sum_univ_eq_sum_range (fun n ↦ ((n + 1 : ℕ) : ℝ)⁻¹ * F (n + 1)) (t + 1)]
  rfl

abbrev SamplingIndex (t : ℕ) := (Fin (t + 1) → Fin (t + 1)) × Fin (t + 1)

noncomputable def samplingVector (t : ℕ) : FinProb (SamplingIndex t) :=
  product uniformVector (harmonicVector t)

noncomputable def finitePushforward {A : Type*} [Fintype A] (p : FinProb A)
    (X : A → Configuration) : ProbabilityMeasure Configuration :=
  ⟨((toPMF p).map X).toMeasure, by infer_instance⟩

theorem integral_finitePushforward {A : Type*} [Fintype A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p : FinProb A) (X : A → Configuration) (F : C(Configuration, ℝ)) :
    (∫ ω, F ω ∂(finitePushforward p X : Measure Configuration)) =
      ∑ a, p a * F (X a) := by
  change (∫ ω, F ω ∂((toPMF p).map X).toMeasure) = _
  rw [← PMF.toMeasure_map X (toPMF p) (measurable_of_countable X)]
  rw [integral_map (measurable_of_countable X).aemeasurable
    F.continuous.aestronglyMeasurable, PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  change (ENNReal.ofReal (p a)).toReal * F (X a) = p a * F (X a)
  rw [ENNReal.toReal_ofReal (prob_nonneg p a)]

/-- The joint sign/residue law at the finite cutoff `t+1`. -/
noncomputable def samplingLaw (f : ℕ → Bool) (t : ℕ) : ProbabilityMeasure Configuration :=
  finitePushforward (samplingVector t)
    (fun z ↦ sample f (boxValue z.1) (z.2.val + 1))

theorem integral_samplingLaw (f : ℕ → Bool) (t : ℕ) (F : C(Configuration, ℝ)) :
    (∫ ω, F ω ∂(samplingLaw f t : Measure Configuration)) =
      ∑ a : Fin (t + 1) → Fin (t + 1), uniformVector a *
        average (t + 1) (fun N ↦ F (sample f (boxValue a) N)) := by
  rw [samplingLaw, integral_finitePushforward, Fintype.sum_prod_type]
  change (∑ a, ∑ n : Fin (t + 1),
    (uniformVector a * harmonicVector t n) * F (sample f (boxValue a) (n.val + 1))) = _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [harmonicVector_expectation t (fun N ↦ F (sample f (boxValue a) N))]

theorem abs_integral_samplingLaw_shift_sub_le
    (f : ℕ → Bool) (t : ℕ) (F : C(Configuration, ℝ)) :
    |(∫ ω, F (shift 1 ω) ∂(samplingLaw f t : Measure Configuration)) -
      ∫ ω, F ω ∂(samplingLaw f t : Measure Configuration)| ≤
        2 * ‖F‖ / mass (t + 1) := by
  let Fs : C(Configuration, ℝ) := ⟨fun ω ↦ F (shift 1 ω),
    F.continuous.comp (continuous_shift 1)⟩
  change |(∫ ω, Fs ω ∂(samplingLaw f t : Measure Configuration)) -
    ∫ ω, F ω ∂(samplingLaw f t : Measure Configuration)| ≤ _
  rw [integral_samplingLaw, integral_samplingLaw, ← Finset.sum_sub_distrib]
  have hrow (a : Fin (t + 1) → Fin (t + 1)) :
      |average (t + 1) (fun N ↦ Fs (sample f (boxValue a) N)) -
        average (t + 1) (fun N ↦ F (sample f (boxValue a) N))| ≤
          2 * ‖F‖ / mass (t + 1) := by
    have h := abs_average_shift_sub_le (Nat.succ_pos t)
      (fun N ↦ F (sample f (boxValue a) N)) ‖F‖
      (fun N ↦ by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm _)
    simpa only [Fs, ContinuousMap.coe_mk, shift_one_sample] using h
  calc
    |∑ a, (uniformVector a * average (t + 1) (fun N ↦ Fs (sample f (boxValue a) N)) -
        uniformVector a * average (t + 1) (fun N ↦ F (sample f (boxValue a) N)))| ≤
        ∑ a : Fin (t + 1) → Fin (t + 1), uniformVector a *
          (2 * ‖F‖ / mass (t + 1)) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro a _
      rw [← mul_sub, abs_mul, abs_of_nonneg (prob_nonneg _ a)]
      exact mul_le_mul_of_nonneg_left (hrow a) (prob_nonneg _ a)
    _ = 2 * ‖F‖ / mass (t + 1) := by
      rw [← Finset.sum_mul, stdSimplex.sum_eq_one, one_mul]

end Erdos67.StationaryModel
