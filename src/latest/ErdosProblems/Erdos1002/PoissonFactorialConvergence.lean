import ErdosProblems.Erdos1002.PoissonCompat
import ErdosProblems.Erdos1002.FactorialMoments
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Distributions.Poisson.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Poisson convergence from factorial moments

This file isolates the probabilistic closure step used after the manuscript's
factorial-measure calculation.  It proves, rather than assumes, the exact
falling-factorial moments of mathlib's Poisson measure and gives the scalar
method of factorial moments on `ℕ`.
-/

open Finset Filter MeasureTheory Real Set Topology
open scoped BigOperators ENNReal NNReal Nat Topology

namespace Erdos1002

noncomputable section

namespace Poisson

open ProbabilityTheory

/-- The shifted, factorial-weighted Poisson mass is a constant multiple of
the original mass. -/
private lemma pmf_mul_descFactorial_shift (r : ℝ≥0) (m k : ℕ) :
    poissonPMFReal r (m + k) * ((m + k).descFactorial k : ℝ) =
      (r : ℝ) ^ k * poissonPMFReal r m := by
  unfold poissonPMFReal
  rw [pow_add]
  have hfac : m ! * (m + k).descFactorial k = (m + k)! := by
    simpa using! Nat.factorial_mul_descFactorial (n := m + k) (k := k) (by omega)
  have hfacR : (m ! : ℝ) * ((m + k).descFactorial k : ℝ) = ((m + k)! : ℝ) := by
    exact_mod_cast hfac
  field_simp
  linear_combination ((r : ℝ) ^ m * (r : ℝ) ^ k) * hfacR

/-- The real series defining the `k`-th falling-factorial moment of a Poisson
law has sum `r ^ k`. -/
lemma hasSum_poissonPMFReal_mul_descFactorial (r : ℝ≥0) (k : ℕ) :
    HasSum (fun n : ℕ ↦ poissonPMFReal r n * (n.descFactorial k : ℝ))
      ((r : ℝ) ^ k) := by
  let f : ℕ → ℝ := fun n ↦ poissonPMFReal r n * (n.descFactorial k : ℝ)
  have htail : HasSum (fun m : ℕ ↦ f (m + k)) ((r : ℝ) ^ k) := by
    have hscaled :
        HasSum (fun m : ℕ ↦ (r : ℝ) ^ k * poissonPMFReal r m) ((r : ℝ) ^ k) := by
      simpa using! HasSum.mul_left ((r : ℝ) ^ k) (poissonPMFRealSum r)
    apply HasSum.congr_fun hscaled
    intro m
    exact pmf_mul_descFactorial_shift r m k
  have hprefix : ∑ i ∈ range k, f i = 0 := by
    apply sum_eq_zero
    intro i hi
    have hik : i < k := mem_range.mp hi
    simp [f, Nat.descFactorial_eq_zero_iff_lt.mpr hik]
  have hfull :
      HasSum f ((r : ℝ) ^ k + ∑ i ∈ range k, f i) :=
    (hasSum_nat_add_iff k).mp htail
  simpa [f, hprefix] using! hfull

/-- Every falling factorial is integrable under a Poisson law.  The proof
computes its `ℝ≥0∞` norm integral from the preceding real series, so no
implicit convention about a divergent Bochner integral is involved. -/
lemma integrable_descFactorial_poisson (r : ℝ≥0) (k : ℕ) :
    Integrable (fun n : ℕ ↦ (n.descFactorial k : ℝ)) (poissonMeasure r) := by
  let g : ℕ → ℝ := fun n ↦ (n.descFactorial k : ℝ)
  have hs := hasSum_poissonPMFReal_mul_descFactorial r k
  have hnonneg : ∀ n : ℕ,
      0 ≤ poissonPMFReal r n * (n.descFactorial k : ℝ) := fun n ↦
    mul_nonneg poissonPMFReal_nonneg (Nat.cast_nonneg _)
  refine ⟨(measurable_of_countable g).aestronglyMeasurable, ?_⟩
  change (∫⁻ n : ℕ, ‖g n‖ₑ ∂poissonMeasure r) < ⊤
  have hlin :
      (∫⁻ n : ℕ, ‖g n‖ₑ ∂poissonMeasure r) =
        ENNReal.ofReal ((r : ℝ) ^ k) := by
    rw [lintegral_countable']
    calc
      ∑' n : ℕ, ‖g n‖ₑ * (poissonMeasure r) {n} =
          ∑' n : ℕ,
            ENNReal.ofReal (poissonPMFReal r n * (n.descFactorial k : ℝ)) := by
        apply tsum_congr
        intro n
        simp only [g, Real.enorm_eq_ofReal (Nat.cast_nonneg _), poissonMeasure_eq_toMeasure]
        rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton n)]
        simp only [poissonPMF]
        rw [ENNReal.ofReal_mul poissonPMFReal_nonneg]
        change ENNReal.ofReal (n.descFactorial k : ℝ) *
            ENNReal.ofReal (poissonPMFReal r n) = _
        ac_rfl
      _ = ENNReal.ofReal (∑' n : ℕ,
          poissonPMFReal r n * (n.descFactorial k : ℝ)) :=
        (ENNReal.ofReal_tsum_of_nonneg hnonneg hs.summable).symm
      _ = ENNReal.ofReal ((r : ℝ) ^ k) := by rw [hs.tsum_eq]
  rw [hlin]
  exact ENNReal.ofReal_lt_top

/-- Exact Poisson falling-factorial moment. -/
theorem integral_descFactorial_poisson (r : ℝ≥0) (k : ℕ) :
    ∫ n : ℕ, (n.descFactorial k : ℝ) ∂poissonMeasure r = (r : ℝ) ^ k := by
  rw [poissonMeasure_eq_toMeasure, PMF.integral_eq_tsum _ _ (by
    simpa only [poissonMeasure_eq_toMeasure] using! integrable_descFactorial_poisson r k)]
  rw [← (hasSum_poissonPMFReal_mul_descFactorial r k).tsum_eq]
  apply tsum_congr
  intro n
  simp only [smul_eq_mul]
  change (ENNReal.ofReal (poissonPMFReal r n)).toReal *
      (n.descFactorial k : ℝ) = _
  rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg]

end Poisson

namespace FactorialMomentMethod

open ProbabilityTheory

/-- Falling-factorial moment of a law on `ℕ`.  Integrability is deliberately
not built into the definition; the convergence theorem states it explicitly. -/
def factorialMoment (μ : ProbabilityMeasure ℕ) (k : ℕ) : ℝ :=
  ∫ x : ℕ, (x.descFactorial k : ℝ) ∂(μ : Measure ℕ)

/-- Mathlib's Poisson measure, packaged as a probability measure. -/
def poissonProbabilityMeasure (r : ℝ≥0) : ProbabilityMeasure ℕ :=
  ⟨poissonMeasure r, inferInstance⟩

/-- The normalized falling factorial appearing in inclusion--exclusion is a
product of two binomial coefficients. -/
private lemma choose_mul_choose_sub_eq_descFactorial_div (x j k : ℕ) :
    (x.choose j : ℝ) * ((x - j).choose k : ℝ) =
      (x.descFactorial (j + k) : ℝ) / ((j ! : ℝ) * (k ! : ℝ)) := by
  have hnat :
      (j ! * k !) * (x.choose j * (x - j).choose k) =
        x.descFactorial (j + k) := by
    calc
      (j ! * k !) * (x.choose j * (x - j).choose k) =
          (x - j).descFactorial k * x.descFactorial j := by
        rw [Nat.descFactorial_eq_factorial_mul_choose,
          Nat.descFactorial_eq_factorial_mul_choose]
        ring
      _ = x.descFactorial (j + k) := by
        simpa using! Nat.descFactorial_mul_descFactorial
          (n := x) (k := j) (m := j + k) (Nat.le_add_right j k)
  have hreal :
      ((j ! : ℝ) * (k ! : ℝ)) *
          ((x.choose j : ℝ) * ((x - j).choose k : ℝ)) =
        (x.descFactorial (j + k) : ℝ) := by
    exact_mod_cast hnat
  field_simp
  nlinarith

/-- The finite alternating binomial sum, in the form needed for the
Bonferroni remainder. -/
private lemma alternating_sum_choose_eq (y K : ℕ) (hy : 0 < y) :
    (∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * (y.choose k : ℝ)) =
      (-1 : ℝ) ^ K * ((y - 1).choose K : ℝ) := by
  have h := Int.alternating_sum_range_choose_eq_choose (n := y - 1) (m := K)
  rw [Nat.sub_add_cancel hy] at h
  exact_mod_cast h

private lemma alternating_sum_choose_zero (K : ℕ) :
    (∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * ((0 : ℕ).choose k : ℝ)) = 1 := by
  rw [sum_eq_single 0]
  · simp
  · intro b hb hb0
    rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb0)]
    simp
  · simp

/-- The `K`-th Bonferroni truncation for the atom `{j}`. -/
private def bonferroni (j K x : ℕ) : ℝ :=
  (x.choose j : ℝ) *
    ∑ k ∈ range (K + 1), (-1 : ℝ) ^ k * ((x - j).choose k : ℝ)

/-- Odd Bonferroni truncations lie below the singleton indicator. -/
private lemma bonferroni_odd_le_indicator (j q x : ℕ) :
    bonferroni j (2 * q + 1) x ≤ if x = j then 1 else 0 := by
  rcases lt_trichotomy x j with hx | rfl | hx
  · simp [bonferroni, Nat.choose_eq_zero_of_lt hx, hx.ne]
  · simp [bonferroni, alternating_sum_choose_zero]
  · have hy : 0 < x - j := Nat.sub_pos_of_lt hx
    rw [if_neg hx.ne']
    rw [bonferroni, alternating_sum_choose_eq (x - j) (2 * q + 1) hy]
    simp [pow_succ, pow_mul]
    positivity

/-- Even Bonferroni truncations lie above the singleton indicator. -/
private lemma indicator_le_bonferroni_even (j q x : ℕ) :
    (if x = j then 1 else 0) ≤ bonferroni j (2 * q) x := by
  rcases lt_trichotomy x j with hx | rfl | hx
  · simp [bonferroni, Nat.choose_eq_zero_of_lt hx, hx.ne]
  · simp [bonferroni, alternating_sum_choose_zero]
  · have hy : 0 < x - j := Nat.sub_pos_of_lt hx
    rw [if_neg hx.ne']
    rw [bonferroni, alternating_sum_choose_eq (x - j) (2 * q) hy]
    simp only [pow_mul, neg_one_sq, one_pow]
    positivity

private lemma bonferroni_eq_sum_descFactorial (j K x : ℕ) :
    bonferroni j K x =
      ∑ k ∈ range (K + 1),
        ((-1 : ℝ) ^ k / ((j ! : ℝ) * (k ! : ℝ))) *
          (x.descFactorial (j + k) : ℝ) := by
  rw [bonferroni, mul_sum]
  apply sum_congr rfl
  intro k _
  calc
    (x.choose j : ℝ) * ((-1 : ℝ) ^ k * ((x - j).choose k : ℝ)) =
        (-1 : ℝ) ^ k * ((x.choose j : ℝ) * ((x - j).choose k : ℝ)) := by ring
    _ = _ := by
      rw [choose_mul_choose_sub_eq_descFactorial_div]
      ring

private def atomIndicator (j x : ℕ) : ℝ := if x = j then 1 else 0

private lemma integrable_atomIndicator (μ : Measure ℕ) [IsFiniteMeasure μ] (j : ℕ) :
    Integrable (atomIndicator j) μ := by
  have hfun : atomIndicator j = ({j} : Set ℕ).indicator (fun _ ↦ (1 : ℝ)) := by
    funext x
    by_cases h : x = j
    · subst x
      simp [atomIndicator]
    · simp [atomIndicator, h]
  rw [hfun]
  exact (integrable_const (1 : ℝ)).indicator (measurableSet_singleton j)

private lemma integral_atomIndicator (μ : Measure ℕ) (j : ℕ) :
    ∫ x, atomIndicator j x ∂μ = μ.real {j} := by
  have hfun : atomIndicator j = ({j} : Set ℕ).indicator (fun _ ↦ (1 : ℝ)) := by
    funext x
    by_cases h : x = j
    · subst x
      simp [atomIndicator]
    · simp [atomIndicator, h]
  rw [hfun]
  simpa only [Pi.one_apply] using!
    (integral_indicator_one (μ := μ) (measurableSet_singleton j))

private lemma integrable_bonferroni (μ : Measure ℕ) (j K : ℕ)
    (hInt : ∀ s : ℕ, Integrable (fun x : ℕ ↦ (x.descFactorial s : ℝ)) μ) :
    Integrable (bonferroni j K) μ := by
  have hfun : bonferroni j K = fun x : ℕ ↦
      ∑ k ∈ range (K + 1),
        ((-1 : ℝ) ^ k / ((j ! : ℝ) * (k ! : ℝ))) *
          (x.descFactorial (j + k) : ℝ) := by
    funext x
    exact bonferroni_eq_sum_descFactorial j K x
  rw [hfun]
  apply integrable_finset_sum
  intro k hk
  exact (hInt (j + k)).const_mul _

private lemma integral_bonferroni (μ : Measure ℕ) (j K : ℕ)
    (hInt : ∀ s : ℕ, Integrable (fun x : ℕ ↦ (x.descFactorial s : ℝ)) μ) :
    ∫ x, bonferroni j K x ∂μ =
      ∑ k ∈ range (K + 1),
        ((-1 : ℝ) ^ k / ((j ! : ℝ) * (k ! : ℝ))) *
          ∫ x, (x.descFactorial (j + k) : ℝ) ∂μ := by
  have hfun : bonferroni j K = fun x : ℕ ↦
      ∑ k ∈ range (K + 1),
        ((-1 : ℝ) ^ k / ((j ! : ℝ) * (k ! : ℝ))) *
          (x.descFactorial (j + k) : ℝ) := by
    funext x
    exact bonferroni_eq_sum_descFactorial j K x
  rw [hfun]
  rw [integral_finset_sum]
  · apply sum_congr rfl
    intro k _
    exact integral_const_mul _ _
  · intro k _
    exact (hInt (j + k)).const_mul _

/-- The limiting coefficient in the inclusion--exclusion expansion of the
mass at `j`. -/
private def atomSeries (r : ℝ≥0) (j k : ℕ) : ℝ :=
  ((-1 : ℝ) ^ k / ((j ! : ℝ) * (k ! : ℝ))) * (r : ℝ) ^ (j + k)

private lemma hasSum_atomSeries (r : ℝ≥0) (j : ℕ) :
    HasSum (atomSeries r j) (poissonPMFReal r j) := by
  let c : ℝ := (r : ℝ) ^ j / (j ! : ℝ)
  have hbase := NormedSpace.expSeries_div_hasSum_exp (-(r : ℝ))
  have hscaled :
      HasSum (fun k : ℕ ↦ c * ((-(r : ℝ)) ^ k / (k ! : ℝ)))
        (c * NormedSpace.exp (-(r : ℝ))) := by
    exact HasSum.mul_left c hbase
  have hterms :
      HasSum (atomSeries r j) (c * NormedSpace.exp (-(r : ℝ))) := by
    apply HasSum.congr_fun hscaled
    intro k
    unfold atomSeries c
    rw [neg_pow, pow_add]
    field_simp
    ring
  convert! hterms using 1
  unfold c poissonPMFReal
  rw [← Real.exp_eq_exp_ℝ]
  ring

private lemma tendsto_even_truncation (r : ℝ≥0) (j : ℕ) :
    Tendsto (fun q : ℕ ↦ ∑ k ∈ range (2 * q + 1), atomSeries r j k)
      atTop (𝓝 (poissonPMFReal r j)) := by
  have hindex : Tendsto (fun q : ℕ ↦ 2 * q + 1) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with q hq
    omega
  exact (hasSum_atomSeries r j).tendsto_sum_nat.comp hindex

private lemma tendsto_odd_truncation (r : ℝ≥0) (j : ℕ) :
    Tendsto (fun q : ℕ ↦ ∑ k ∈ range (2 * q + 2), atomSeries r j k)
      atTop (𝓝 (poissonPMFReal r j)) := by
  have hindex : Tendsto (fun q : ℕ ↦ 2 * q + 2) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with q hq
    omega
  exact (hasSum_atomSeries r j).tendsto_sum_nat.comp hindex

private lemma tendsto_integral_bonferroni
    (μs : ℕ → ProbabilityMeasure ℕ) (r : ℝ≥0) (j K : ℕ)
    (hInt : ∀ n k, Integrable (fun x : ℕ ↦ (x.descFactorial k : ℝ))
      (μs n : Measure ℕ))
    (hFac : ∀ k, Tendsto (fun n ↦ factorialMoment (μs n) k) atTop
      (𝓝 ((r : ℝ) ^ k))) :
    Tendsto (fun n ↦ ∫ x, bonferroni j K x ∂(μs n : Measure ℕ)) atTop
      (𝓝 (∑ k ∈ range (K + 1), atomSeries r j k)) := by
  have hfun : (fun n ↦ ∫ x, bonferroni j K x ∂(μs n : Measure ℕ)) =
      fun n ↦ ∑ k ∈ range (K + 1),
        ((-1 : ℝ) ^ k / ((j ! : ℝ) * (k ! : ℝ))) *
          factorialMoment (μs n) (j + k) := by
    funext n
    exact integral_bonferroni (μs n : Measure ℕ) j K (hInt n)
  rw [hfun]
  apply tendsto_finset_sum
  intro k hk
  exact (hFac (j + k)).const_mul _

/-- Point probabilities converge under convergence of all falling-factorial
moments.  This is the scalar Bonferroni form of the method of factorial
moments. -/
theorem tendsto_real_singleton_of_factorialMoments
    (μs : ℕ → ProbabilityMeasure ℕ) (r : ℝ≥0)
    (hInt : ∀ n k, Integrable (fun x : ℕ ↦ (x.descFactorial k : ℝ))
      (μs n : Measure ℕ))
    (hFac : ∀ k, Tendsto (fun n ↦ factorialMoment (μs n) k) atTop
      (𝓝 ((r : ℝ) ^ k))) (j : ℕ) :
    Tendsto (fun n ↦ (μs n : Measure ℕ).real {j}) atTop
      (𝓝 (poissonPMFReal r j)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := div_pos hε (by norm_num)
  obtain ⟨qOdd, hqOdd⟩ :=
    (Metric.tendsto_atTop.mp (tendsto_odd_truncation r j)) (ε / 4) hε4
  obtain ⟨qEven, hqEven⟩ :=
    (Metric.tendsto_atTop.mp (tendsto_even_truncation r j)) (ε / 4) hε4
  let q := max qOdd qEven
  have hOddLimit :
      dist (∑ k ∈ range (2 * q + 2), atomSeries r j k) (poissonPMFReal r j) < ε / 4 :=
    hqOdd q (le_max_left _ _)
  have hEvenLimit :
      dist (∑ k ∈ range (2 * q + 1), atomSeries r j k) (poissonPMFReal r j) < ε / 4 :=
    hqEven q (le_max_right _ _)
  obtain ⟨nOdd, hnOdd⟩ :=
    (Metric.tendsto_atTop.mp
      (tendsto_integral_bonferroni μs r j (2 * q + 1) hInt hFac)) (ε / 4) hε4
  obtain ⟨nEven, hnEven⟩ :=
    (Metric.tendsto_atTop.mp
      (tendsto_integral_bonferroni μs r j (2 * q) hInt hFac)) (ε / 4) hε4
  refine ⟨max nOdd nEven, fun n hn ↦ ?_⟩
  have hnO := hnOdd n (le_trans (le_max_left _ _) hn)
  have hnE := hnEven n (le_trans (le_max_right _ _) hn)
  have hLower :
      (∫ x, bonferroni j (2 * q + 1) x ∂(μs n : Measure ℕ)) ≤
        (μs n : Measure ℕ).real {j} := by
    rw [← integral_atomIndicator]
    exact integral_mono
      (integrable_bonferroni (μs n : Measure ℕ) j (2 * q + 1) (hInt n))
      (integrable_atomIndicator (μs n : Measure ℕ) j)
      (bonferroni_odd_le_indicator j q)
  have hUpper :
      (μs n : Measure ℕ).real {j} ≤
        ∫ x, bonferroni j (2 * q) x ∂(μs n : Measure ℕ) := by
    rw [← integral_atomIndicator]
    exact integral_mono
      (integrable_atomIndicator (μs n : Measure ℕ) j)
      (integrable_bonferroni (μs n : Measure ℕ) j (2 * q) (hInt n))
      (indicator_le_bonferroni_even j q)
  rw [Real.dist_eq] at hOddLimit hEvenLimit hnO hnE ⊢
  rw [abs_lt] at hOddLimit hEvenLimit hnO hnE ⊢
  constructor <;> linarith

/-- On the discrete space `ℕ`, convergence of every singleton mass implies
weak convergence.  The proof uses finite subsets of an arbitrary open set
and the open-set half of Portmanteau. -/
theorem tendsto_probabilityMeasure_nat_of_real_singletons
    (μs : ℕ → ProbabilityMeasure ℕ) (μ : ProbabilityMeasure ℕ)
    (hPoint : ∀ j : ℕ,
      Tendsto (fun n ↦ (μs n : Measure ℕ).real {j}) atTop
        (𝓝 ((μ : Measure ℕ).real {j}))) :
    Tendsto μs atTop (𝓝 μ) := by
  have hFinReal (s : Finset ℕ) :
      Tendsto (fun n ↦ (μs n : Measure ℕ).real (s : Set ℕ)) atTop
        (𝓝 ((μ : Measure ℕ).real (s : Set ℕ))) := by
    simpa only [sum_measureReal_singleton] using!
      tendsto_finset_sum s (fun j hj ↦ hPoint j)
  have hFin (s : Finset ℕ) :
      Tendsto (fun n ↦ (μs n : Measure ℕ) (s : Set ℕ)) atTop
        (𝓝 ((μ : Measure ℕ) (s : Set ℕ))) := by
    apply (ENNReal.tendsto_toReal_iff
      (fun n ↦ measure_ne_top (μs n : Measure ℕ) (s : Set ℕ))
      (measure_ne_top (μ : Measure ℕ) (s : Set ℕ))).mp
    simpa only [measureReal_def] using! hFinReal s
  apply tendsto_of_forall_isOpen_le_liminf_nat'
  intro G hG
  classical
  let t : ℕ → Finset ℕ := fun m ↦ (range m).filter (fun x ↦ x ∈ G)
  have htmono : Monotone (fun m ↦ (t m : Set ℕ)) := by
    intro a b hab x hx
    change x ∈ t a at hx
    change x ∈ t b
    rcases Finset.mem_filter.mp hx with ⟨hxa, hxG⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hxa).trans_le hab), hxG⟩
  have htunion : (⋃ m, (t m : Set ℕ)) = G := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨m, hxm⟩
      change x ∈ t m at hxm
      exact (Finset.mem_filter.mp hxm).2
    · intro hxG
      apply Set.mem_iUnion.mpr
      refine ⟨x + 1, ?_⟩
      change x ∈ t (x + 1)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.lt_succ_self x), hxG⟩
  have hfinite_le (m : ℕ) :
      (μ : Measure ℕ) (t m : Set ℕ) ≤
        liminf (fun n ↦ (μs n : Measure ℕ) G) atTop := by
    rw [← (hFin (t m)).liminf_eq]
    apply Filter.liminf_le_liminf
      (Eventually.of_forall fun n ↦ measure_mono (by
        intro x hx
        change x ∈ t m at hx
        exact (Finset.mem_filter.mp hx).2))
  have hcont :
      Tendsto (fun m ↦ (μ : Measure ℕ) (t m : Set ℕ)) atTop
        (𝓝 ((μ : Measure ℕ) G)) := by
    simpa only [Function.comp_apply, htunion] using!
      (tendsto_measure_iUnion_atTop (μ := (μ : Measure ℕ)) htmono)
  exact le_of_tendsto hcont (Eventually.of_forall hfinite_le)

private lemma poissonProbabilityMeasure_real_singleton (r : ℝ≥0) (j : ℕ) :
    (poissonProbabilityMeasure r : Measure ℕ).real {j} = poissonPMFReal r j := by
  rw [measureReal_def]
  change (poissonMeasure r {j}).toReal = poissonPMFReal r j
  rw [poissonMeasure_eq_toMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton j)]
  change (ENNReal.ofReal (poissonPMFReal r j)).toReal = poissonPMFReal r j
  exact ENNReal.toReal_ofReal poissonPMFReal_nonneg

/-- **Method of factorial moments for a Poisson limit on `ℕ`.**

For every fixed order we assume genuine Bochner integrability and convergence
of the corresponding falling-factorial moment.  No additional uniform moment
or exponential-moment hypothesis is needed: finite Bonferroni truncations
give the two-sided point-mass bounds used above. -/
theorem tendsto_poisson_of_factorialMoments
    (μs : ℕ → ProbabilityMeasure ℕ) (r : ℝ≥0)
    (hInt : ∀ n k, Integrable (fun x : ℕ ↦ (x.descFactorial k : ℝ))
      (μs n : Measure ℕ))
    (hFac : ∀ k, Tendsto (fun n ↦ factorialMoment (μs n) k) atTop
      (𝓝 ((r : ℝ) ^ k))) :
    Tendsto μs atTop (𝓝 (poissonProbabilityMeasure r)) := by
  apply tendsto_probabilityMeasure_nat_of_real_singletons
  intro j
  simpa only [poissonProbabilityMeasure_real_singleton] using!
    tendsto_real_singleton_of_factorialMoments μs r hInt hFac j

end FactorialMomentMethod

end

end Erdos1002
