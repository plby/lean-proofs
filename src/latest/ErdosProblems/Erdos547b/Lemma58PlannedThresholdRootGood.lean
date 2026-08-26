/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58PlannedOwnerLocalStep
import ErdosProblems.Erdos547b.Lemma58FiberRootOrientation

/-!
# Root-side admissibility for canonical threshold steps

The canonical local threshold orientation is the same source-only maximal
cutoff used by the root-orientation certificate.  Hence its branch roots are
admissible whenever the high side is admissible and the low side is
admissible whenever its integral budget is nonzero.
-/

open scoped SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58PlannedThresholdRootGood

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58OwnerLocalStep
open Erdos547b.ZhaoLemma58CanonicalThresholdStep
open Erdos547b.ZhaoLemma58FiberRootOrientation

universe v

theorem canonicalStepOrientation_root_good
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b) (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole live : Fin 2 → Finset B)
    (rho density : ℝ)
    (D : ActualThresholdStepData F G externalParent whole live rho density)
    (rootGood : Fin 2 → Prop)
    (hhigh : rootGood D.highSide)
    (hlow : D.lowBudget ≠ 0 → rootGood D.lowSide)
    (i : Fin b) :
    rootGood
      (canonicalStepOrientation F G externalParent whole live rho density D i
        0) := by
  let O := thresholdRootOrientation F rootGood D.slack D.lowBudget D.highBudget
    D.lowSide D.highSide D.small D.sides_ne D.suffix_display hhigh hlow
  have hi := O.root_good i
  simpa only [O, thresholdRootOrientation, canonicalStepOrientation] using hi

end Erdos547b.ZhaoLemma58PlannedThresholdRootGood

#print axioms Erdos547b.ZhaoLemma58PlannedThresholdRootGood.canonicalStepOrientation_root_good
