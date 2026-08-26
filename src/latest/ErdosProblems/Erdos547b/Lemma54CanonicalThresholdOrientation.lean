/- leanprover/lean4:v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma54ThresholdNumerics

/-!
# A canonical Zhao threshold orientation

The source balancing theorem is existential, but root-target cleaning must
know the physical endpoint of every branch before any root image is chosen.
This file fixes one prefix-balanced base by classical choice and applies the
already checked maximal-fitting cutoff to it.  The definitions contain only
source data and therefore introduce no host or embedding premise.
-/

open scoped BigOperators
noncomputable section

namespace Erdos547b.ZhaoLemma54CanonicalThresholdOrientation

open Finset Fintype
open Erdos547b.RegularPair
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54ThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdNumerics

/-- A fixed prefix-balanced base orientation for one ordered small forest. -/
noncomputable def canonicalPrefixBalancedOrientation
    {b : ℕ} (F : OrderedRootedForest b) (slack : ℕ)
    (hsmall : ∀ i, F.size i ≤ slack) : Fin b → Fin 2 ≃ Fin 2 :=
  Classical.choose (exists_prefix_balanced_orientation F slack hsmall)

theorem canonicalPrefixBalancedOrientation_spec
    {b : ℕ} (F : OrderedRootedForest b) (slack : ℕ)
    (hsmall : ∀ i, F.size i ≤ slack) :
    ∀ t c,
      2 * sideLoadPrefix F
          (canonicalPrefixBalancedOrientation F slack hsmall) t c ≤
        prefixOrder F t + slack :=
  Classical.choose_spec (exists_prefix_balanced_orientation F slack hsmall)

/-- Zhao's literal maximal-fitting threshold switch applied to the canonical
prefix-balanced base. -/
noncomputable def canonicalActualThresholdSwitchOrientation
    {b : ℕ} (F : OrderedRootedForest b)
    (slack lowBudget highBudget : ℕ) (lowSide highSide : Fin 2)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hsides : highSide ≠ lowSide)
    (hfinal : ∀ (base : Fin b → Fin 2 ≃ Fin 2),
      (∀ t c,
        2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack) →
      ∀ c,
        lowBudget + fixedSuffixLoad F
            (maximalFittingCutoff F base lowBudget) highSide c ≤
          highBudget) :
    ThresholdSwitchOrientation F lowSide lowBudget highBudget :=
  actualThresholdSwitchOrientation F slack lowBudget highBudget
    lowSide highSide hsmall hsides hfinal
    (canonicalPrefixBalancedOrientation F slack hsmall)
    (canonicalPrefixBalancedOrientation_spec F slack hsmall)

end Erdos547b.ZhaoLemma54CanonicalThresholdOrientation

#print axioms Erdos547b.ZhaoLemma54CanonicalThresholdOrientation.canonicalPrefixBalancedOrientation_spec
#print axioms Erdos547b.ZhaoLemma54CanonicalThresholdOrientation.canonicalActualThresholdSwitchOrientation
