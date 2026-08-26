/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Maximal estimates for weighted sign partial sums in Erdős 521.
Formal proof: Codex. The conditional-Jensen and squared-martingale arguments
are adapted from the verified helpers in Erdos1166HLOZLemmaA8.lean.
-/
import ErdosProblems.Erdos521.Moments
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Independence.Conditional

namespace Erdos521

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

def weightedIncrement (a : ℕ → ℝ) (i : ℕ) (ε : ℕ → ℝ) : ℝ := a i * ε i

theorem measurable_weightedIncrement (a : ℕ → ℝ) (i : ℕ) :
    Measurable (weightedIncrement a i) := by fun_prop [weightedIncrement]

noncomputable def weightedFiltration (a : ℕ → ℝ) :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  Filtration.natural (weightedIncrement a) (fun i ↦ (measurable_weightedIncrement a i).stronglyMeasurable)

def weightedPartialSum (a : ℕ → ℝ) (n : ℕ) (ε : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), weightedIncrement a i ε

theorem independent_weightedIncrements (a : ℕ → ℝ) :
    iIndepFun (weightedIncrement a) sequenceLaw :=
  independent_coefficients.comp (fun i x ↦ a i * x) (fun _ ↦ by fun_prop)

theorem integral_weightedIncrement (a : ℕ → ℝ) (i : ℕ) :
    (∫ ε, weightedIncrement a i ε ∂sequenceLaw) = 0 := by
  simp [weightedIncrement, integral_const_mul, integral_coordinate]

theorem weightedIncrement_memLp (a : ℕ → ℝ) (i : ℕ) (p : ℝ≥0∞) :
    MemLp (weightedIncrement a i) p sequenceLaw := (coordinate_memLp i p).const_mul (a i)

theorem weightedPartialSum_memLp (a : ℕ → ℝ) (n : ℕ) (p : ℝ≥0∞) :
    MemLp (weightedPartialSum a n) p sequenceLaw := by
  unfold weightedPartialSum
  convert memLp_finsetSum' (Finset.range (n + 1))
    (fun i _ ↦ weightedIncrement_memLp a i p) using 1
  ext ε
  simp

theorem weightedPartialSum_stronglyAdapted (a : ℕ → ℝ) :
    StronglyAdapted (weightedFiltration a) (weightedPartialSum a) := by
  have hnat : StronglyAdapted (weightedFiltration a) (weightedIncrement a) :=
    Filtration.stronglyAdapted_natural (fun i ↦ (measurable_weightedIncrement a i).stronglyMeasurable)
  intro n
  unfold weightedPartialSum
  apply Finset.stronglyMeasurable_fun_sum
  intro i hi
  exact (hnat i).mono ((weightedFiltration a).mono
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))

theorem weightedPartialSum_martingale (a : ℕ → ℝ) :
    Martingale (weightedPartialSum a) (weightedFiltration a) sequenceLaw := by
  apply martingale_nat (weightedPartialSum_stronglyAdapted a)
    (fun n ↦ (weightedPartialSum_memLp a n 1).integrable le_rfl)
  intro n
  have hcond := (independent_weightedIncrements a).condExp_natural_ae_eq_of_lt
    (fun i ↦ (measurable_weightedIncrement a i).stronglyMeasurable) (Nat.lt_succ_self n)
  change sequenceLaw[weightedIncrement a (n + 1) | weightedFiltration a n] =ᵐ[sequenceLaw]
    fun _ ↦ ∫ ε, weightedIncrement a (n + 1) ε ∂sequenceLaw at hcond
  rw [integral_weightedIncrement] at hcond
  have hSn : sequenceLaw[weightedPartialSum a n | weightedFiltration a n] =
      weightedPartialSum a n :=
    condExp_of_stronglyMeasurable ((weightedFiltration a).le n)
      (weightedPartialSum_stronglyAdapted a n) ((weightedPartialSum_memLp a n 1).integrable le_rfl)
  have heq : weightedPartialSum a (n + 1) = weightedPartialSum a n + weightedIncrement a (n + 1) := by
    funext ε
    exact Finset.sum_range_succ _ _
  rw [heq]
  have hadd := condExp_add ((weightedPartialSum_memLp a n 1).integrable le_rfl)
    ((weightedIncrement_memLp a (n + 1) 1).integrable le_rfl) (weightedFiltration a n)
  filter_upwards [hadd, hcond] with ε hε hinc
  rw [hε, hSn]
  simp [hinc]

theorem martingale_square_submartingale {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {𝒢 : Filtration ℕ ‹MeasurableSpace Ω›}
    [SigmaFiniteFiltration μ 𝒢] {S : ℕ → Ω → ℝ}
    (hS : Martingale S 𝒢 μ) (h2 : ∀ n, MemLp (S n) 2 μ) :
    Submartingale (fun n ω ↦ (S n ω) ^ 2) 𝒢 μ := by
  refine ⟨?_, ?_, fun n ↦ (h2 n).integrable_sq⟩
  · convert hS.stronglyAdapted.mul hS.stronglyAdapted using 1
    funext n ω
    simp [pow_two]
  · intro i j hij
    have hjensen := (even_two.convexOn_pow (𝕜 := ℝ)).map_condExp_le_univ
      (𝒢.le i) (continuous_pow 2).lowerSemicontinuous
      ((h2 j).integrable one_le_two) (h2 j).integrable_sq
    filter_upwards [hS.condExp_ae_eq hij, hjensen] with ω hcond hj
    dsimp only [Function.comp_apply] at hj
    rw [hcond] at hj
    exact hj

/-- Kolmogorov's maximal inequality for arbitrary deterministic weights of the
original coefficient sequence. -/
theorem weightedPartialSum_maximal (a : ℕ → ℝ) (n : ℕ) {r : ℝ} (hr : 0 < r) :
    sequenceLaw.real {ε | r ^ 2 ≤ (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k ↦ (weightedPartialSum a k ε) ^ 2)} ≤
      (∑ k ∈ Finset.range (n + 1), (a k) ^ 2) / r ^ 2 := by
  have hsub := martingale_square_submartingale (weightedPartialSum_martingale a)
    (fun k ↦ weightedPartialSum_memLp a k 2)
  have hmax := maximal_ineq hsub (fun _ _ ↦ sq_nonneg _) (ε := ⟨r ^ 2, sq_nonneg r⟩) n
  have htotal := setIntegral_le_integral
    (s := {ε | r ^ 2 ≤ (Finset.range (n + 1)).sup'
      Finset.nonempty_range_add_one (fun k ↦ (weightedPartialSum a k ε) ^ 2)}) (hsub.integrable n)
    (Filter.Eventually.of_forall fun ε ↦ sq_nonneg (weightedPartialSum a n ε))
  have hbound := hmax.trans (ENNReal.ofReal_le_ofReal htotal)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg fun ε ↦
    sq_nonneg (weightedPartialSum a n ε))] at hreal
  change r ^ 2 * sequenceLaw.real {ε | r ^ 2 ≤ (Finset.range (n + 1)).sup'
    Finset.nonempty_range_add_one (fun k ↦ (weightedPartialSum a k ε) ^ 2)} ≤
      ∫ ε, (weightedPartialSum a n ε) ^ 2 ∂sequenceLaw at hreal
  have hmoment : (∫ ε, (weightedPartialSum a n ε) ^ 2 ∂sequenceLaw) =
      ∑ k ∈ Finset.range (n + 1), (a k) ^ 2 := integral_linearForm_sq _ a
  rw [hmoment] at hreal
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  simpa only [mul_comm] using hreal

end Erdos521
