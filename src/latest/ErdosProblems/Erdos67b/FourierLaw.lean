import ErdosProblems.Erdos67b.FourierBox
import ErdosProblems.Erdos67b.Stochastic
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# Probability laws from arbitrary bounded-discrepancy sequences

The finite exponent-box construction is pushed forward to the compact
space of circle-valued completely multiplicative functions.  Compactness
then produces a single law whose prefix moments are uniformly bounded.
No multiplicativity is assumed of the original input sequence.
-/

open scoped BigOperators
open MeasureTheory

namespace Erdos67b

theorem compactCharacterPartialSum_exponentBoxCharacter
    (s : Finset ℕ) (M : ℕ) [NeZero M]
    (ψ : AddChar (ExponentBox s M) ℂ) (m : ℕ) :
    compactCharacterPartialSum 1 m (exponentBoxCharacter s M ψ) =
      ∑ j ∈ Finset.Icc 1 m, ψ (exponentBoxVector s M j) := by
  unfold compactCharacterPartialSum
  simp only [exponentBoxCharacter_apply]
  apply Finset.sum_bij (fun j _ ↦ j + 1)
  · intro j hj
    simp only [Finset.mem_range] at hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a _ b _ hab
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro j _
    change ψ (exponentBoxVector s M ((j + 1) * 1)) = _
    rw [Nat.mul_one]

/-- Every finite law on exponent-box frequencies gives an actual
probability measure on the compact space, with the expected moments. -/
theorem exists_exponentBox_probability_law
    (s : Finset ℕ) (M : ℕ) [NeZero M]
    (P : PMF (AddChar (ExponentBox s M) ℂ)) :
    ∃ μ : ProbabilityMeasure CompactCircleCharacter,
      ∀ m : ℕ, compactMeanSquarePartialSum μ m =
        ∑ ψ : AddChar (ExponentBox s M) ℂ,
          (P ψ).toReal *
            ‖∑ j ∈ Finset.Icc 1 m, ψ (exponentBoxVector s M j)‖ ^ 2 := by
  classical
  let : MeasurableSpace (AddChar (ExponentBox s M) ℂ) := ⊤
  let ν : ProbabilityMeasure (AddChar (ExponentBox s M) ℂ) :=
    ⟨P.toMeasure, inferInstance⟩
  have hmap : Measurable (exponentBoxCharacter s M) := measurable_of_finite _
  refine ⟨ν.map hmap.aemeasurable, ?_⟩
  intro m
  unfold compactMeanSquarePartialSum
  rw [ProbabilityMeasure.toMeasure_map,
    integral_map hmap.aemeasurable
      (continuous_compactCharacterPartialSumSq 1 m).aestronglyMeasurable]
  change (∫ ψ, compactCharacterPartialSumSq 1 m (exponentBoxCharacter s M ψ)
      ∂P.toMeasure) = _
  rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro ψ _
  simp only [smul_eq_mul, compactCharacterPartialSumSq,
    compactCharacterPartialSum_exponentBoxCharacter]

/-- Tao's finite stochastic reduction, with the explicit bound `C²+1`. -/
theorem exists_finite_law_of_bounded_discrepancy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : ℕ → E) (hf : ∀ n, 0 < n → ‖f n‖ = 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hdiscrepancy : ∀ d l : ℕ, 0 < d →
      ‖∑ j ∈ Finset.Icc 1 l, f (j * d)‖ ≤ C) (X : ℕ) :
    ∃ μ : ProbabilityMeasure CompactCircleCharacter,
      ∀ m : ℕ, m ≤ X → compactMeanSquarePartialSum μ m ≤ C ^ 2 + 1 := by
  obtain ⟨M, hM, hF, hbound⟩ :=
    exists_bounded_spectral_exponentBox f hf C hC hdiscrepancy X
  let : NeZero M := hM
  obtain ⟨μ, hμ⟩ := exists_exponentBox_probability_law (Finset.Icc 1 X) M
    (spectralPMF (exponentBoxPullback (Finset.Icc 1 X) M f) hF)
  refine ⟨μ, ?_⟩
  intro m hm
  rw [hμ]
  exact hbound m hm

/-- An arbitrary unit-vector sequence with bounded homogeneous sums
produces a single stochastic completely multiplicative counterexample.
This is the full forward reduction, not a proof that such a counterexample
is impossible. -/
theorem exists_global_law_of_bounded_discrepancy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : ℕ → E) (hf : ∀ n, 0 < n → ‖f n‖ = 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hdiscrepancy : ∀ d l : ℕ, 0 < d →
      ‖∑ j ∈ Finset.Icc 1 l, f (j * d)‖ ≤ C) :
    ∃ μ : ProbabilityMeasure CompactCircleCharacter,
      ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2 + 1 := by
  classical
  choose P hP using exists_finite_law_of_bounded_discrepancy f hf C hC hdiscrepancy
  exact exists_global_law_of_finite_laws P (C ^ 2 + 1) hP

/-- The arbitrary-sign formulation of the forward reduction.  The
bound on length-zero sums follows from nonnegativity of `C`; no condition
is placed on the irrelevant value of the sequence at zero. -/
theorem exists_global_law_of_bounded_sign_discrepancy
    (f : ℕ → ℝ) (hf : ∀ n, 0 < n → f n = -1 ∨ f n = 1)
    (C : ℝ) (hC : 0 ≤ C)
    (hdiscrepancy : ∀ d m : ℕ, 0 < d → 0 < m →
      |∑ j ∈ Finset.Icc 1 m, f (j * d)| ≤ C) :
    ∃ μ : ProbabilityMeasure CompactCircleCharacter,
      ∀ m : ℕ, compactMeanSquarePartialSum μ m ≤ C ^ 2 + 1 := by
  refine exists_global_law_of_bounded_discrepancy (fun n ↦ (f n : ℂ)) ?_ C hC ?_
  · intro n hn
    rcases hf n hn with h | h <;> simp [h]
  · intro d m hd
    by_cases hm : 0 < m
    · simpa only [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] using
        hdiscrepancy d m hd hm
    · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
      simpa [hm0] using hC

/-- The exact real sign-sequence conclusion follows from the stochastic
theorem.  This explicitly conditional bridge is not the final theorem. -/
theorem sign_discrepancy_of_stochastic
    (hS : StochasticDiscrepancyStatement)
    (f : ℕ → ℝ) (hf : ∀ n, f n = -1 ∨ f n = 1)
    (C : ℝ) (hC : 0 < C) :
    ∃ d m : ℕ, 0 < d ∧ 0 < m ∧
      C < |∑ j ∈ Finset.Icc 1 m, f (j * d)| := by
  by_contra hnot
  have hbound : ∀ d m : ℕ, 0 < d → 0 < m →
      |∑ j ∈ Finset.Icc 1 m, f (j * d)| ≤ C := by
    intro d m hd hm
    exact le_of_not_gt (fun h ↦ hnot ⟨d, m, hd, hm, h⟩)
  obtain ⟨μ, hμ⟩ := exists_global_law_of_bounded_sign_discrepancy
    f (fun n _ ↦ hf n) C hC.le hbound
  obtain ⟨m, _, hm⟩ := hS μ (C ^ 2 + 1)
  exact (not_lt_of_ge (hμ m)) hm

end Erdos67b
