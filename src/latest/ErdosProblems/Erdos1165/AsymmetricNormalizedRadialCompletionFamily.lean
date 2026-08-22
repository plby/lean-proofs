/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AsymmetricCompatibleRadialCompletionFamily

/-!
# Normalizing genuine nested completion atoms

The pathwise recursive disintegration naturally proves an aggregate local
estimate

`sum_t P(tail r t) <= radialTail * P(retained r)`.

This file converts that estimate into the exact conditional-weight contract
used by `CompatibleRadialCompletionFamily`.  The weight is the genuine
conditional mass `P(tail r t) / P(retained r)`.  The zero-mass retained case
is handled from the pathwise inclusion `tail r t \subseteq retained r`; no
positive-mass assumption and no synthetic cylinder identity are needed.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Erdos1165.AsymmetricNormalizedRadialCompletionFamily

open AsymmetricCompatibleRadialCompletionFamily

noncomputable section

/-- A source-facing family whose quantitative input is the aggregate mass
of genuine tail refinements inside each genuine retained atom. -/
structure NormalizedCompletionRows
    (successful retained gammaX : Set StepPath) (radialTail : ℝ) : Type 2 where
  RetainedCode : Type
  retainedCode_countable : Countable RetainedCode
  TailCode : RetainedCode → Type
  tailCode_countable : ∀ r, Countable (TailCode r)
  retainedAtom : RetainedCode → Set StepPath
  tailAtom : ∀ r, TailCode r → Set StepPath
  successful_subset : successful ⊆ ⋃ r, ⋃ t, tailAtom r t
  retained_eq : retained = ⋃ r, retainedAtom r
  retained_measurable : ∀ r, MeasurableSet (retainedAtom r)
  retained_pairwise : Pairwise fun r s ↦
    Disjoint (retainedAtom r) (retainedAtom s)
  tail_subset : ∀ r t, tailAtom r t ⊆ retainedAtom r
  tail_sum_le : ∀ r,
    ∑' t, fairSteps (tailAtom r t) ≤
      ENNReal.ofReal radialTail * fairSteps (retainedAtom r)
  retained_subset : retained ⊆ gammaX

attribute [instance] NormalizedCompletionRows.retainedCode_countable
attribute [instance] NormalizedCompletionRows.tailCode_countable

/-- The normalized conditional mass of one genuine tail refinement. -/
def NormalizedCompletionRows.tailWeight
    {successful retained gammaX : Set StepPath} {radialTail : ℝ}
    (rows : NormalizedCompletionRows successful retained gammaX radialTail)
    (r : rows.RetainedCode) (t : rows.TailCode r) : ℝ≥0∞ :=
  if fairSteps (rows.retainedAtom r) = 0 then 0 else
    fairSteps (rows.tailAtom r t) / fairSteps (rows.retainedAtom r)

/-- Normalization gives the exact conditional factorization, including when
the retained atom has mass zero. -/
theorem NormalizedCompletionRows.tail_mass
    {successful retained gammaX : Set StepPath} {radialTail : ℝ}
    (rows : NormalizedCompletionRows successful retained gammaX radialTail)
    (r : rows.RetainedCode) (t : rows.TailCode r) :
    fairSteps (rows.tailAtom r t) =
      rows.tailWeight r t * fairSteps (rows.retainedAtom r) := by
  by_cases hzero : fairSteps (rows.retainedAtom r) = 0
  · have htail : fairSteps (rows.tailAtom r t) = 0 :=
      measure_mono_null (rows.tail_subset r t) hzero
    simp only [NormalizedCompletionRows.tailWeight, hzero, if_pos, zero_mul,
      htail]
  · symm
    rw [NormalizedCompletionRows.tailWeight, if_neg hzero]
    exact ENNReal.div_mul_cancel hzero (measure_ne_top fairSteps _)

/-- The aggregate local mass estimate is exactly the conditional row bound
after normalization. -/
theorem NormalizedCompletionRows.row_le
    {successful retained gammaX : Set StepPath} {radialTail : ℝ}
    (rows : NormalizedCompletionRows successful retained gammaX radialTail)
    (r : rows.RetainedCode) :
    ∑' t, rows.tailWeight r t ≤ ENNReal.ofReal radialTail := by
  by_cases hzero : fairSteps (rows.retainedAtom r) = 0
  · have htail : ∀ t, fairSteps (rows.tailAtom r t) = 0 := fun t ↦
      measure_mono_null (rows.tail_subset r t) hzero
    simp only [NormalizedCompletionRows.tailWeight, hzero, if_pos, tsum_zero,
      zero_le]
  · rw [show (∑' t, rows.tailWeight r t) =
        (∑' t, fairSteps (rows.tailAtom r t)) /
          fairSteps (rows.retainedAtom r) by
      simp only [NormalizedCompletionRows.tailWeight]
      simp_rw [if_neg hzero]
      simpa only [div_eq_mul_inv] using
        (ENNReal.tsum_mul_right :
          (∑' t, fairSteps (rows.tailAtom r t) *
              (fairSteps (rows.retainedAtom r))⁻¹) = _)]
    exact (ENNReal.div_le_iff hzero (measure_ne_top fairSteps _)).2
      (rows.tail_sum_le r)

/-- Package normalized genuine refinements as the completion family used by
the asymmetric far-pair constructor. -/
def NormalizedCompletionRows.toCompatibleRadialCompletionFamily
    {successful retained gammaX : Set StepPath} {radialTail : ℝ}
    (rows : NormalizedCompletionRows successful retained gammaX radialTail) :
    CompatibleRadialCompletionFamily successful retained gammaX radialTail where
  RetainedCode := rows.RetainedCode
  retainedCode_countable := rows.retainedCode_countable
  TailCode := rows.TailCode
  tailCode_countable := rows.tailCode_countable
  retainedAtom := rows.retainedAtom
  tailAtom := rows.tailAtom
  tailWeight := rows.tailWeight
  successful_subset := rows.successful_subset
  retained_eq := rows.retained_eq
  retained_measurable := rows.retained_measurable
  retained_pairwise := rows.retained_pairwise
  tail_mass := rows.tail_mass
  row_le := rows.row_le
  retained_subset := rows.retained_subset

end

end Erdos1165.AsymmetricNormalizedRadialCompletionFamily
