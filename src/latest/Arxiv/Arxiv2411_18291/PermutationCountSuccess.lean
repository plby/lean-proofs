import Arxiv.Arxiv2411_18291.PermutationMomentBounds
import Mathlib.Probability.Moments.Variance

/-!
# A success criterion for coloured candidate counts

Chebyshev's inequality converts a relative second-moment estimate into a
lower-tail probability bound. When this bound is below one, there is an
actual assignment of permutations retaining more than half the mean count.
-/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291.RandomPermutation

variable {I V C : Type*} [Fintype V] [DecidableEq V]
variable [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)]

theorem eventCount_memLp_two (s : Finset I) (T : Finset C)
    (A : C → I → Set (Equiv.Perm V)) : MemLp (eventCount s T A) 2 (probability I V) :=
  (memLp_two_iff_integrable_sq (eventCount_integrable s T A).aestronglyMeasurable).mpr
    (eventCount_sq_integrable s T A)

theorem eventCount_lower_tail_le (s : Finset I) (T : Finset C)
    (A : C → I → Set (Equiv.Perm V)) {μ ε : ℝ} (hμ : 0 < μ)
    (hmean : (∫ ω, eventCount s T A ω ∂probability I V) = μ)
    (hsecond : (∫ ω, eventCount s T A ω ^ 2 ∂probability I V) ≤ (1 + ε) * μ ^ 2) :
    (probability I V).real {ω | eventCount s T A ω ≤ μ / 2} ≤ 4 * ε := by
  have hX := eventCount_memLp_two s T A
  have hvar : variance (eventCount s T A) (probability I V) ≤ ε * μ ^ 2 := by
    rw [variance_eq_sub hX]
    change (∫ ω, eventCount s T A ω ^ 2 ∂probability I V) -
      (∫ ω, eventCount s T A ω ∂probability I V) ^ 2 ≤ ε * μ ^ 2
    rw [hmean]
    nlinarith only [hsecond]
  have hcheb := meas_ge_le_variance_div_sq hX (by linarith : 0 < μ / 2)
  rw [hmean] at hcheb
  have hsub : {ω | eventCount s T A ω ≤ μ / 2} ⊆
      {ω | μ / 2 ≤ |eventCount s T A ω - μ|} := by
    intro ω hω
    have hab := neg_le_abs (eventCount s T A ω - μ)
    change eventCount s T A ω ≤ μ / 2 at hω
    change μ / 2 ≤ |eventCount s T A ω - μ|
    linarith
  have hprob := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans hcheb)
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at hprob
  calc
    _ ≤ variance (eventCount s T A) (probability I V) / (μ / 2) ^ 2 := hprob
    _ ≤ (ε * μ ^ 2) / (μ / 2) ^ 2 := div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = 4 * ε := by field_simp; norm_num

theorem eventCount_lower_tail_three_quarters_le (s : Finset I) (T : Finset C)
    (A : C → I → Set (Equiv.Perm V)) {μ ε : ℝ} (hμ : 0 < μ)
    (hmean : (∫ ω, eventCount s T A ω ∂probability I V) = μ)
    (hsecond : (∫ ω, eventCount s T A ω ^ 2 ∂probability I V) ≤ (1 + ε) * μ ^ 2) :
    (probability I V).real {ω | eventCount s T A ω ≤ 3 * μ / 4} ≤ 16 * ε := by
  have hX := eventCount_memLp_two s T A
  have hvar : variance (eventCount s T A) (probability I V) ≤ ε * μ ^ 2 := by
    rw [variance_eq_sub hX]
    change (∫ ω, eventCount s T A ω ^ 2 ∂probability I V) -
      (∫ ω, eventCount s T A ω ∂probability I V) ^ 2 ≤ ε * μ ^ 2
    rw [hmean]
    nlinarith only [hsecond]
  have hcheb := meas_ge_le_variance_div_sq hX (by linarith : 0 < μ / 4)
  rw [hmean] at hcheb
  have hsub : {ω | eventCount s T A ω ≤ 3 * μ / 4} ⊆
      {ω | μ / 4 ≤ |eventCount s T A ω - μ|} := by
    intro ω hω
    have hab := neg_le_abs (eventCount s T A ω - μ)
    change eventCount s T A ω ≤ 3 * μ / 4 at hω
    change μ / 4 ≤ |eventCount s T A ω - μ|
    linarith
  have hprob := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans hcheb)
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _))] at hprob
  calc
    _ ≤ variance (eventCount s T A) (probability I V) / (μ / 4) ^ 2 := hprob
    _ ≤ (ε * μ ^ 2) / (μ / 4) ^ 2 := div_le_div_of_nonneg_right hvar (sq_nonneg _)
    _ = 16 * ε := by field_simp; norm_num

theorem eventCount_exists_many (s : Finset I) (T : Finset C)
    (A : C → I → Set (Equiv.Perm V)) {μ ε : ℝ} (hμ : 0 < μ)
    (hmean : (∫ ω, eventCount s T A ω ∂probability I V) = μ)
    (hsecond : (∫ ω, eventCount s T A ω ^ 2 ∂probability I V) ≤ (1 + ε) * μ ^ 2)
    (hε : 4 * ε < 1) : ∃ ω, μ / 2 < eventCount s T A ω := by
  by_contra h
  have heq : {ω | eventCount s T A ω ≤ μ / 2} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    exact le_of_not_gt (fun hω => h ⟨ω, hω⟩)
  have hprob := eventCount_lower_tail_le s T A hμ hmean hsecond
  simp only [heq, measureReal_def, measure_univ, ENNReal.toReal_one] at hprob
  linarith

end Arxiv2411_18291.RandomPermutation
