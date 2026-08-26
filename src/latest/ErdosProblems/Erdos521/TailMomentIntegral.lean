/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Integrated finite-tail bounds for bounded integer-valued random variables.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.NatTailMoments

namespace Erdos521

open MeasureTheory
open scoped BigOperators

theorem integral_nat_pow_le_tail_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℕ} (hX : AEMeasurable X μ) (n J p : ℕ)
    (hbound : ∀ ω, X ω ≤ n) :
    (∫ ω, (X ω : ℝ) ^ p ∂μ) ≤ 16 ^ p +
      (∑ j ∈ Finset.Ico 8 J, (2 * ((j : ℝ) + 1)) ^ p * μ.real {ω | 2 * j ≤ X ω}) +
      (n : ℝ) ^ p * μ.real {ω | 2 * J ≤ X ω} := by
  have hterms (j : ℕ) := natTailTerm_integrable μ hX (2 * j) ((2 * ((j : ℝ) + 1)) ^ p)
  have hsum := integrable_finsetSum (Finset.Ico 8 J) (fun j _ ↦ hterms j)
  have hlast := natTailTerm_integrable μ hX (2 * J) ((n : ℝ) ^ p)
  have hfirst : Integrable (fun ω ↦ (16 : ℝ) ^ p +
      ∑ j ∈ Finset.Ico 8 J, natTailTerm X (2 * j) ((2 * ((j : ℝ) + 1)) ^ p) ω) μ :=
    (integrable_const _).add hsum
  have h := integral_mono (bounded_nat_pow_integrable μ hX n p hbound)
    (hfirst.add hlast)
    (fun ω ↦ nat_pow_le_tail_sum n (X ω) J p (hbound ω))
  dsimp only [Pi.add_apply] at h
  rw [integral_add hfirst hlast,
    integral_add (integrable_const (16 ^ p : ℝ)) hsum,
    integral_finsetSum (Finset.Ico 8 J) (fun j _ ↦ hterms j)] at h
  simp only [integral_natTailTerm μ hX, integral_const, probReal_univ, one_smul] at h
  exact h

end Erdos521
