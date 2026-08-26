/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma54CanonicalThresholdOrientation
import ErdosProblems.Erdos547b.Lemma58ThresholdGroupEmbedding

/-!
# Fixed-orientation threshold realization

This is the graph realization companion to the canonical source orientation.
It returns an embedding with the literal, precomputable orientation rather
than hiding the chosen base behind an existential.  That endpoint is needed
to clean component roots only toward the physical sides on which their cut
parents can actually land.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58FixedThresholdGroupEmbedding

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma54ThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdNumerics
open Erdos547b.ZhaoLemma54CanonicalThresholdOrientation
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma58ThresholdGroupEmbedding

universe v

/-- Realize the canonical prefix-balanced/maximal-cutoff orientation. -/
theorem exists_canonicalActualThresholdDynamicGroupEmbedding
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b)
    (slack lowBudget highBudget : ℕ) (lowSide highSide : Fin 2)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hsides : highSide ≠ lowSide)
    (hfinal : ∀ (base : Fin b → Fin 2 ≃ Fin 2),
      (∀ t c,
        2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack) →
      ∀ c,
        lowBudget + fixedSuffixLoad F
            (maximalFittingCutoff F base lowBudget) highSide c ≤
          highBudget)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (reserve : Fin 2 → ℕ) (rho density : ℝ)
    (hlowHigh : lowBudget ≤ highBudget)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (hreserve : ∀ c, rho * (#(whole c) : ℝ) ≤ reserve c)
    (havailableCapacity : ∀ c,
      highBudget + reserve c ≤ #(available c))
    (hparent : ∀ i,
      let O := canonicalActualThresholdSwitchOrientation F slack lowBudget
        highBudget lowSide highSide hsmall hsides hfinal
      1 + reserve (branchRootSide F O.orient i) +
          sideLoadBefore F O.orient i (branchRootSide F O.orient i) ≤
        #((available (branchRootSide F O.orient i)).filter
          (G.Adj (externalParent i))))
    (hmargin : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(available c) : ℝ) - highBudget)) :
    Nonempty (DynamicAttachedForestEmbedding F G externalParent
      (canonicalActualThresholdSwitchOrientation F slack lowBudget
        highBudget lowSide highSide hsmall hsides hfinal).orient available) := by
  let O := canonicalActualThresholdSwitchOrientation F slack lowBudget
    highBudget lowSide highSide hsmall hsides hfinal
  exact exists_dynamicGroupEmbedding_of_thresholdSwitch F lowSide lowBudget
    highBudget O G externalParent whole available reserve rho density
    hlowHigh hunif havailable hwholeDisjoint hdensity hfactor hreserve
    havailableCapacity hparent hmargin

end Erdos547b.ZhaoLemma58FixedThresholdGroupEmbedding

#print axioms Erdos547b.ZhaoLemma58FixedThresholdGroupEmbedding.exists_canonicalActualThresholdDynamicGroupEmbedding
