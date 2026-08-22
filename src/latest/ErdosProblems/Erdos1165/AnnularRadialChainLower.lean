/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialLabelWord

/-!
# Scalar lower bounds for chronological radial chains

The source-correct Appendix-A.6 object is a single chronological label word.
Its exact kernel integrates the random endpoint after every successive
different-boundary hit.  This module shows that uniform scalar lower bounds
for those endpoint-summed rows multiply along the word.  No intermediate
spatial endpoint is frozen.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularRadialChainLower

open AnnularRadialLabelWord MarkedBoundaryVisitKernel ThickPoint

noncomputable section

/-- Product of prescribed scalar one-step masses along a radial label list. -/
def radialChainReference
    {n : ℕ} (edge : Fin (n + 2) → Fin (n + 2) → ℝ≥0∞) :
    Fin (n + 2) → List (Fin (n + 2)) → ℝ≥0∞
  | _, [] => 1
  | source, target :: tail =>
      edge source target * radialChainReference edge target tail

lemma radialChainReference_nonneg
    {n : ℕ} (edge : Fin (n + 2) → Fin (n + 2) → ℝ≥0∞)
    (source : Fin (n + 2)) (targets : List (Fin (n + 2))) :
    0 ≤ radialChainReference edge source targets := bot_le

/-- Uniform endpoint-integrated row bounds multiply through the exact
random-endpoint chronological chain kernel. -/
theorem radialChainReference_le_kernel
    {n : ℕ} (center : Point)
    (edge : Fin (n + 2) → Fin (n + 2) → ℝ≥0∞)
    (hrow : ∀ source target : Fin (n + 2),
      ∀ start : Point, start ∈ radialBoundary n center source →
        edge source target ≤
          ∑ endpoint : RadialBoundaryPoint n center target,
            skeletonExitKernel (otherRadialBoundaries n center source)
              start endpoint.1) :
    ∀ source targets start, start ∈ radialBoundary n center source →
      radialChainReference edge source targets ≤
        radialChainKernelENNReal n center source targets start := by
  intro source targets
  induction targets generalizing source with
  | nil =>
      intro start _
      simp [radialChainReference, radialChainKernelENNReal]
  | cons target tail ih =>
      intro start hstart
      have hhead := hrow source target start hstart
      have htail (endpoint : RadialBoundaryPoint n center target) :
          radialChainReference edge target tail ≤
            radialChainKernelENNReal n center target tail endpoint.1 :=
        ih target endpoint.1 endpoint.2
      rw [radialChainReference, radialChainKernelENNReal]
      calc
        edge source target * radialChainReference edge target tail ≤
            (∑ endpoint : RadialBoundaryPoint n center target,
                skeletonExitKernel (otherRadialBoundaries n center source)
                  start endpoint.1) *
              radialChainReference edge target tail :=
          mul_le_mul hhead le_rfl bot_le bot_le
        _ = ∑ endpoint : RadialBoundaryPoint n center target,
              skeletonExitKernel (otherRadialBoundaries n center source)
                  start endpoint.1 *
                radialChainReference edge target tail := by
          rw [Finset.sum_mul]
        _ ≤ ∑ endpoint : RadialBoundaryPoint n center target,
              skeletonExitKernel (otherRadialBoundaries n center source)
                  start endpoint.1 *
                radialChainKernelENNReal n center target tail endpoint.1 := by
          exact Finset.sum_le_sum fun endpoint _ ↦
            mul_le_mul le_rfl (htail endpoint) bot_le bot_le

/-- Word specialization of `radialChainReference_le_kernel`, transferred to
the literal prefix-free stopped-word event by the exact chain/atom identity. -/
theorem radialChainReference_le_fairSteps_radialLabelWordAtom
    {n L : ℕ} (hn : 2 ≤ n) (center start : Point)
    (word : RadialLabelWord n L)
    (hstart : start ∈ radialBoundary n center ⟨1, by omega⟩)
    (edge : Fin (n + 2) → Fin (n + 2) → ℝ≥0∞)
    (hrow : ∀ source target : Fin (n + 2),
      ∀ z : Point, z ∈ radialBoundary n center source →
        edge source target ≤
          ∑ endpoint : RadialBoundaryPoint n center target,
            skeletonExitKernel (otherRadialBoundaries n center source)
              z endpoint.1) :
    radialChainReference edge (word.level ⟨0, by omega⟩) word.toList.tail ≤
      fairSteps (radialLabelWordAtom n L center start word) := by
  rw [fairSteps_radialLabelWordAtom_eq_radialWordChainKernelENNReal
    hn center start word hstart]
  apply radialChainReference_le_kernel center edge hrow
  rw [word.startsAtOne]
  exact hstart

end

end Erdos1165.AnnularRadialChainLower
