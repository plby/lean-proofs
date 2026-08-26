import ErdosProblems.Erdos67b.Compactness
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.FunProp

/-!
# Stochastic circle-character partial sums

This file fixes the concrete probability space used in Tao's stochastic
reformulation.  A random completely multiplicative circle-valued function is
represented by a probability measure on the compact prime-coordinate space
`PrimeAssignment`.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory

namespace Erdos67b

noncomputable instance instMeasurableSpacePrimeAssignment :
    MeasurableSpace PrimeAssignment := borel PrimeAssignment

instance instBorelSpacePrimeAssignment : BorelSpace PrimeAssignment := ⟨rfl⟩

noncomputable def compactCharacterBasePartialSum
    (m : ℕ) (g : CompactCircleCharacter) : ℂ :=
  ∑ k ∈ Finset.range m, (g.1 ⟨k + 1, by omega⟩ : ℂ)

theorem compactCharacterPartialSum_dilation
    (g : CompactCircleCharacter) (d : ℕ+) (m : ℕ) :
    compactCharacterPartialSum d m g =
      compactCharacterBasePartialSum m g * (g.1 d : ℂ) := by
  unfold compactCharacterPartialSum
  calc
    (∑ k ∈ Finset.range m, (g.1 (⟨k + 1, by omega⟩ * d) : ℂ)) =
        ∑ k ∈ Finset.range m,
          (g.1 ⟨k + 1, by omega⟩ : ℂ) * (g.1 d : ℂ) := by
      apply Finset.sum_congr rfl
      intro k hk
      let n : ℕ+ := ⟨k + 1, by omega⟩
      change ((g.1 (n * d) : Circle) : ℂ) =
        ((g.1 n : Circle) : ℂ) * ((g.1 d : Circle) : ℂ)
      rw [g.2.2 n d]
      rfl
    _ = (∑ k ∈ Finset.range m, (g.1 ⟨k + 1, by omega⟩ : ℂ)) *
        (g.1 d : ℂ) := by rw [Finset.sum_mul]
    _ = compactCharacterBasePartialSum m g * (g.1 d : ℂ) := rfl

theorem compactCharacterPartialSumSq_dilation
    (g : CompactCircleCharacter) (d : ℕ+) (m : ℕ) :
    compactCharacterPartialSumSq d m g = compactCharacterPartialSumSq 1 m g := by
  unfold compactCharacterPartialSumSq
  rw [compactCharacterPartialSum_dilation, compactCharacterPartialSum_dilation,
    norm_mul, norm_mul, Circle.norm_coe, Circle.norm_coe]

/-- The complex prefix sum of the completely multiplicative function generated
by the prime assignment `z`.  Index zero is excluded. -/
noncomputable def circlePartialSum (z : PrimeAssignment) (m : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 m, (primeExtension z k : ℂ)

theorem continuous_circlePartialSum (m : ℕ) :
    Continuous fun z : PrimeAssignment ↦ circlePartialSum z m := by
  unfold circlePartialSum
  apply continuous_finsetSum
  intro k hk
  exact continuous_subtype_val.comp (continuous_primeExtension k)

/-- Squared norm of a completely multiplicative prefix sum. -/
noncomputable def circlePartialSumEnergy (m : ℕ) (z : PrimeAssignment) : ℝ :=
  ‖circlePartialSum z m‖ ^ 2

theorem continuous_circlePartialSumEnergy (m : ℕ) :
    Continuous (circlePartialSumEnergy m) := by
  unfold circlePartialSumEnergy
  exact (continuous_circlePartialSum m).norm.pow 2

theorem circlePartialSumEnergy_nonneg (m : ℕ) (z : PrimeAssignment) :
    0 ≤ circlePartialSumEnergy m z := by
  exact sq_nonneg _

/-- The mean-square prefix sum under a law on prime assignments. -/
noncomputable def meanSquarePartialSum
    (μ : ProbabilityMeasure PrimeAssignment) (m : ℕ) : ℝ :=
  ∫ z, circlePartialSumEnergy m z ∂(μ : Measure PrimeAssignment)

theorem meanSquarePartialSum_nonneg
    (μ : ProbabilityMeasure PrimeAssignment) (m : ℕ) :
    0 ≤ meanSquarePartialSum μ m := by
  unfold meanSquarePartialSum
  apply integral_nonneg
  exact fun z ↦ circlePartialSumEnergy_nonneg m z

/-- The exact stochastic theorem needed in the Fourier reduction. -/
noncomputable def compactMeanSquarePartialSum
    (μ : ProbabilityMeasure CompactCircleCharacter) (m : ℕ) : ℝ :=
  ∫ g, compactCharacterPartialSumSq 1 m g
    ∂(μ : Measure CompactCircleCharacter)

theorem compactMeanSquarePartialSum_nonneg
    (μ : ProbabilityMeasure CompactCircleCharacter) (m : ℕ) :
    0 ≤ compactMeanSquarePartialSum μ m := by
  unfold compactMeanSquarePartialSum
  apply integral_nonneg
  intro g
  exact sq_nonneg _

@[simp] theorem compactMeanSquarePartialSum_zero
    (μ : ProbabilityMeasure CompactCircleCharacter) :
    compactMeanSquarePartialSum μ 0 = 0 := by
  simp [compactMeanSquarePartialSum, compactCharacterPartialSumSq,
    compactCharacterPartialSum]

/-- The exact stochastic theorem needed in the Fourier reduction. -/
def StochasticDiscrepancyStatement : Prop :=
  ∀ (μ : ProbabilityMeasure CompactCircleCharacter) (C : ℝ),
    ∃ m : ℕ, 1 ≤ m ∧ C < compactMeanSquarePartialSum μ m

def HasUniformMeanSquareBound
    (μ : ProbabilityMeasure CompactCircleCharacter) (C : ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → compactMeanSquarePartialSum μ m ≤ C

theorem stochasticDiscrepancy_iff_no_uniform_meanSquare_bound :
    StochasticDiscrepancyStatement ↔
      ∀ μ : ProbabilityMeasure CompactCircleCharacter,
        ¬ ∃ C : ℝ, HasUniformMeanSquareBound μ C := by
  constructor
  · intro h μ ⟨C, hC⟩
    obtain ⟨m, hm, hlarge⟩ := h μ C
    exact (not_lt_of_ge (hC m hm)) hlarge
  · intro h μ C
    by_contra hnot
    apply h μ
    refine ⟨C, ?_⟩
    intro m hm
    by_contra hle
    apply hnot
    exact ⟨m, hm, lt_of_not_ge hle⟩

/-- Failure of the stochastic discrepancy statement is exactly a law whose
mean-square prefix sums have one square bound at every length.  Including
length zero is convenient for the shifted-sum estimates in Tao's argument. -/
theorem not_stochasticDiscrepancy_iff_exists_uniform_square_bound :
    ¬ StochasticDiscrepancyStatement ↔
      ∃ μ : ProbabilityMeasure CompactCircleCharacter, ∃ C : ℝ,
        ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2 := by
  constructor
  · intro hnot
    have hnotall :
        ¬ ∀ μ : ProbabilityMeasure CompactCircleCharacter,
          ¬ ∃ C : ℝ, HasUniformMeanSquareBound μ C := by
      intro h
      exact hnot (stochasticDiscrepancy_iff_no_uniform_meanSquare_bound.mpr h)
    push Not at hnotall
    obtain ⟨μ, B, hB⟩ := hnotall
    have hBnonneg : 0 ≤ B :=
      (compactMeanSquarePartialSum_nonneg μ 1).trans (hB 1 le_rfl)
    refine ⟨μ, Real.sqrt B, ?_⟩
    intro m
    by_cases hm : m = 0
    · subst m
      simp
    · simpa [Real.sq_sqrt hBnonneg] using hB m (Nat.one_le_iff_ne_zero.mpr hm)
  · rintro ⟨μ, C, hC⟩ hS
    obtain ⟨m, _hm, hlarge⟩ := hS μ (C ^ 2)
    exact (not_lt_of_ge (hC m)) hlarge

/-- Compactness turns laws which satisfy a common bound through a growing
finite cutoff into one law satisfying that bound at every length. -/
theorem exists_global_law_of_finite_laws
    (P : ℕ → ProbabilityMeasure CompactCircleCharacter) (C : ℝ)
    (hP : ∀ X m : ℕ, m ≤ X → compactMeanSquarePartialSum (P X) m ≤ C) :
    ∃ Q : ProbabilityMeasure CompactCircleCharacter,
      ∀ m : ℕ, compactMeanSquarePartialSum Q m ≤ C := by
  obtain ⟨Q, r, hr, hweak, hmoment⟩ :=
    exists_subseq_tendsto_integral_compactCharacterPartialSumSq P
  refine ⟨Q, ?_⟩
  intro m
  have hr_top : Filter.Tendsto r Filter.atTop Filter.atTop := hr.tendsto_atTop
  have hm_le : ∀ᶠ j in Filter.atTop, m ≤ r j :=
    (Filter.tendsto_atTop.1 hr_top) m
  have hbound : ∀ᶠ j in Filter.atTop,
      compactMeanSquarePartialSum (P (r j)) m ≤ C := by
    filter_upwards [hm_le] with j hj
    exact hP (r j) m hj
  have hlim : Filter.Tendsto
      (fun j ↦ compactMeanSquarePartialSum (P (r j)) m)
      Filter.atTop (nhds (compactMeanSquarePartialSum Q m)) := by
    simpa only [compactMeanSquarePartialSum] using hmoment 1 m
  exact le_of_tendsto hlim hbound

end Erdos67b
