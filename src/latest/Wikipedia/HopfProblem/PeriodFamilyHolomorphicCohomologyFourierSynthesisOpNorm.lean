import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Summable operator bounds from genuine fixed-direction bounds

A fixed finite-dimensional basis bounds the operator norm of every
actual derivative. Finitely many summable directional majorants thus
give a summable operator-norm majorant on the same parameter set.
No uniform bound on a whole unit sphere is an additional hypothesis.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

variable {E F α X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Summable bounds in each fixed direction yield an actual summable
operator-norm bound, uniformly on the original set of parameters. -/
theorem exists_summable_opNorm_bound (S : Set X) (L : α → X → E →L[ℝ] F)
    (h : ∀ v : E, ∃ u : α → ℝ, (∀ k, 0 ≤ u k) ∧ Summable u ∧
      ∀ x ∈ S, ∀ k, ‖L k x v‖ ≤ u k) :
    ∃ u : α → ℝ, (∀ k, 0 ≤ u k) ∧ Summable u ∧
      ∀ x ∈ S, ∀ k, ‖L k x‖ ≤ u k := by
  classical
  let b := Module.finBasis ℝ E
  obtain ⟨C, hC, hb⟩ := b.exists_opNorm_le (F := F)
  choose u hnonneg hsum hbound using fun i => h (b i)
  refine ⟨fun k => C * ∑ i, u i k, ?_, ?_, ?_⟩
  · intro k
    exact mul_nonneg hC.le (Finset.sum_nonneg fun i _ => hnonneg i k)
  · exact (summable_sum fun i _ => hsum i).mul_left C
  · intro x hx k
    apply hb (Finset.sum_nonneg fun i _ => hnonneg i k)
    intro i
    exact (hbound i x hx k).trans
      (Finset.single_le_sum (fun j _ => hnonneg j k) (Finset.mem_univ i))

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
