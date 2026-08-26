/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58OwnerLocalStep
import ErdosProblems.Erdos547b.Lemma58FixedThresholdGroupEmbedding

/-!
# Canonical realization of a threshold local step

`ActualThresholdStepData.realize` intentionally hides the balanced base
orientation.  Root target cleaning needs the literal orientation before the
root images are selected, so this companion theorem realizes the canonical
choice from `Lemma54CanonicalThresholdOrientation` exactly.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58CanonicalThresholdStep

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma54CanonicalThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdOrientation
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58FixedThresholdGroupEmbedding

universe v

/-- The exact orientation determined by threshold source data. -/
abbrev canonicalStepOrientation
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (D : ActualThresholdStepData F G externalParent whole live rho density) :=
  (canonicalActualThresholdSwitchOrientation F D.slack D.lowBudget
    D.highBudget D.lowSide D.highSide D.small D.sides_ne
    D.suffix_display).orient

/-- Realize an `ActualThresholdStepData` with its literal canonical
orientation, rather than existentially hiding the balanced base. -/
theorem ActualThresholdStepData.realize_canonical
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (D : ActualThresholdStepData F G externalParent whole live rho density) :
    Nonempty (DynamicAttachedForestEmbedding F G externalParent
      (canonicalStepOrientation F G externalParent whole live rho density D)
      live) := by
  apply exists_canonicalActualThresholdDynamicGroupEmbedding F D.slack
    D.lowBudget D.highBudget D.lowSide D.highSide D.small D.sides_ne
    D.suffix_display G externalParent whole live D.reserve rho density
    D.low_le_high D.uniform D.live_subset D.whole_disjoint D.density_lower
    D.factor_nonneg D.reserve_regular D.live_capacity
  · intro i
    exact D.parent_neighbours
      (canonicalPrefixBalancedOrientation F D.slack D.small)
      (canonicalPrefixBalancedOrientation_spec F D.slack D.small) i
  · exact D.component_margin

end Erdos547b.ZhaoLemma58CanonicalThresholdStep

#print axioms Erdos547b.ZhaoLemma58CanonicalThresholdStep.ActualThresholdStepData.realize_canonical
