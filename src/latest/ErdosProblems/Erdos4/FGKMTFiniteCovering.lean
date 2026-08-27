import ErdosProblems.Erdos4.FGKMTIterationBudget
import ErdosProblems.Erdos4.FGKMTExpectationExtraction

/-!
# A finite quantitative covering theorem

The sparsity threshold is explicit. The proof constructs the random
covering process, proves joint survival estimates by induction, then
extracts one legal deterministic covering. The cardinality budget `A`
does not decrease during the induction.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

noncomputable def coveringThreshold (r A : ℕ) (κ D : ℝ) : ℝ :=
  1 / (2 * propagationCoefficient r A κ D)

theorem coveringThreshold_pos (r A : ℕ) {κ D : ℝ} (hκ : 0 < κ) (hD : 0 ≤ D) :
    0 < coveringThreshold r A κ D := by
  have hH := propagationCoefficient_ge_one r A hκ hD
  unfold coveringThreshold
  positivity

theorem coveringThreshold_le_half (r A : ℕ) {κ D : ℝ} (hκ : 0 < κ) (hD : 0 ≤ D) :
    coveringThreshold r A κ D ≤ 1 / 2 := by
  have hH := propagationCoefficient_ge_one r A hκ hD
  exact one_div_le_one_div_of_le (by norm_num) (by linarith : 2 ≤ 2 * propagationCoefficient r A κ D)

theorem coveringThreshold_budget (r A : ℕ) {κ D : ℝ} (hκ : 0 < κ) (hD : 0 ≤ D) :
    propagationCoefficient r A κ D * coveringThreshold r A κ D ≤ 1 := by
  have hH := propagationCoefficient_ge_one r A hκ hD
  have hpos : 0 < propagationCoefficient r A κ D := by linarith
  have heq : propagationCoefficient r A κ D * coveringThreshold r A κ D = 1 / 2 := by
    unfold coveringThreshold
    field_simp
  rw [heq]
  norm_num

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

/-- Joint survival accuracy for the explicit finite covering process.
The hypothesis on `δ` is a fully specified numeric threshold. -/
theorem finite_covering_accuracy (μ : ℕ → I → FiniteLaw (Finset V))
    {m r A : ℕ} {κ δ D τ : ℝ} (hκ : 0 < κ) (hδ : 0 ≤ δ) (hD : 0 ≤ D)
    (hrA : 2 * r ≤ A) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (hsmall : propagationCoefficient r A κ D * τ ≤ 1)
    (hsparse : δ ≤ τ ^ (4 * 8 ^ m))
    (hround : ∀ j < m, RoundBounds (μ j) (modelSequence μ j) r κ δ D) :
    SurvivalAccurate (survivorProcess μ (iterationThreshold τ m) m)
      (modelSequence μ m) A (τ ^ 4) := by
  have hτle : τ ≤ 1 := by linarith
  have hh := survivorProcess_accuracy μ (iterationThreshold τ m) (iterationError τ m) hrA hround
    (fun j _hj => ⟨iterationError_nonneg hτ0.le m j,
      (iterationError_le hτ0.le hτle m j).trans hτ1⟩)
    (fun j _hj => ⟨iterationThreshold_pos hτ0 m j,
      (iterationThreshold_le hτ0.le hτle m j).trans hτ1⟩)
    (fun j hj => iterationBudget_step r A m hκ hδ hD hτ0 hτ1 hsmall hsparse hj)
  simpa only [iterationError, Nat.sub_self, pow_zero, mul_one] using hh

/-- One legal edge (or the empty edge) is chosen from every source.
At most twice the model's final expected number of vertices survive. -/
theorem finite_covering (μ : ℕ → I → FiniteLaw (Finset V))
    {m r A : ℕ} {κ δ D : ℝ} (hκ : 0 < κ) (hδ : 0 ≤ δ) (hD : 0 ≤ D)
    (hA : 1 ≤ A) (hrA : 2 * r ≤ A)
    (hsparse : δ ≤ coveringThreshold r A κ D ^ (4 * 8 ^ m))
    (hround : ∀ j < m, RoundBounds (μ j) (modelSequence μ j) r κ δ D) :
    ∃ choice : ℕ → I → Finset V,
      (∀ j < m, ∀ i, choice j i = ∅ ∨ 0 < (μ j i).weight (choice j i)) ∧
      ((Finset.univ \ coveredThrough choice m).card : ℝ) ≤
        2 * ∑ v, modelSequence μ m v := by
  have hτ0 := coveringThreshold_pos r A hκ hD
  have hτ1 := coveringThreshold_le_half r A hκ hD
  have hacc := finite_covering_accuracy μ hκ hδ hD hrA hτ0 hτ1
    (coveringThreshold_budget r A hκ hD) hsparse hround
  obtain ⟨choice, hlegal, hcard⟩ := exists_legal_cover μ
    (iterationThreshold (coveringThreshold r A κ D) m) hA hacc
  refine ⟨choice, hlegal, hcard.trans ?_⟩
  have hτ4 : coveringThreshold r A κ D ^ 4 ≤ 1 :=
    pow_le_one₀ hτ0.le (by linarith : coveringThreshold r A κ D ≤ 1)
  exact mul_le_mul_of_nonneg_right (by linarith)
    (Finset.sum_nonneg (fun v _hv => (modelSequence_pos μ m v).le))

end Erdos4.FGKMT
