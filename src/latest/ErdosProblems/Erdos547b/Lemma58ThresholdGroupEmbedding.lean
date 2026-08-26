/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma58GroupedSmallForest
import ErdosProblems.Erdos547b.Lemma54ThresholdOrientation
import ErdosProblems.Erdos547b.Lemma54ThresholdNumerics

/-!
# Threshold-switched dynamic groups in Zhao Lemma 5.4

This is the acyclic composition layer between the source-only threshold
orientation and the dynamic regular-pair engine.  The parent of a branch
only needs enough neighbors for the load already used before that branch.
Before the cutoff this is the low-density budget; after the cutoff every
branch root is sent to the high side and uses the high-density budget.

The conclusions are actual simultaneous embeddings into the current
available subsets.  No copy, continuation, or static per-endpoint load is
assumed.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoLemma58ThresholdGroupEmbedding

open Finset Fintype SimpleGraph
open Erdos547b.RegularPair
open Erdos547b.ForestMatching
open Erdos547b.ZhaoLemma58GroupedSmallForest
open Erdos547b.ZhaoLemma54ThresholdOrientation
open Erdos547b.ZhaoLemma54ThresholdNumerics

universe v

/-- Realize a supplied threshold-switch orientation in one regular pair.
The root-degree hypothesis is deliberately expressed using the low budget
only when the branch root is sent to the low endpoint.  This is the exact
prefix feature missing from a static whole-pool formulation. -/
theorem exists_dynamicGroupEmbedding_of_thresholdSwitch
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b)
    (lowSide : Fin 2) (lowBudget highBudget : ℕ)
    (O : ThresholdSwitchOrientation F lowSide lowBudget highBudget)
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
      1 + reserve (branchRootSide F O.orient i) +
          sideLoadBefore F O.orient i (branchRootSide F O.orient i) ≤
        #((available (branchRootSide F O.orient i)).filter
          (G.Adj (externalParent i))))
    (hmargin : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(available c) : ℝ) - highBudget)) :
    Nonempty (DynamicAttachedForestEmbedding
      F G externalParent O.orient available) := by
  apply exists_dynamic_ordered_forest_embedding_of_uniform
    F G externalParent O.orient whole available reserve rho density
    hunif havailable hwholeDisjoint hdensity hfactor hreserve
  · intro c
    exact (Nat.add_le_add_right (O.final_load c) (reserve c)).trans
      (havailableCapacity c)
  · exact hparent
  · intro i c
    calc
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
          (density - rho) *
            ((#(available c) : ℝ) - highBudget) := hmargin i c
      _ ≤ (density - rho) *
          ((#(available c) : ℝ) - sideLoad F O.orient c) := by
        apply mul_le_mul_of_nonneg_left _ hfactor
        exact sub_le_sub_left (by exact_mod_cast O.final_load c) _

/-- Construct the source threshold orientation and immediately realize it.
This is the local graph endpoint used by Lemma 5.8(2). -/
theorem exists_thresholdDynamicGroupEmbedding
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b)
    (slack lowBudget highBudget : ℕ) (lowSide highSide : Fin 2)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hsides : highSide ≠ lowSide)
    (D : ThresholdMassBudget F slack lowBudget highBudget highSide)
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
    (hparent : ∀ i c,
      1 + reserve c +
          (if c = lowSide then lowBudget else highBudget) ≤
        #((available c).filter (G.Adj (externalParent i))))
    (hmargin : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(available c) : ℝ) - highBudget)) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        F G externalParent orient available) := by
  obtain ⟨O⟩ := exists_thresholdSwitchOrientation F slack lowBudget
    highBudget lowSide highSide hsmall hsides D
  refine ⟨O.orient,
    exists_dynamicGroupEmbedding_of_thresholdSwitch F lowSide lowBudget
      highBudget O G externalParent whole available reserve rho density
      hlowHigh hunif havailable hwholeDisjoint hdensity hfactor hreserve
      havailableCapacity ?_ hmargin⟩
  intro i
  have hpref := O.prefix_root_le hlowHigh i
  exact (Nat.add_le_add_left hpref
    (1 + reserve (branchRootSide F O.orient i))).trans
      (hparent i (branchRootSide F O.orient i))

/-- Construct and realize Zhao's *actual* maximal-fitting cutoff, asking for
the parent degree only on the physical side to which the constructed
orientation sends that branch root.  This is essential when the low source
density is zero: the maximal cutoff is then empty and no root is sent to the
low endpoint. -/
theorem exists_actualThresholdDynamicGroupEmbedding_of_actualParent
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b)
    (slack lowBudget highBudget : ℕ) (lowSide highSide : Fin 2)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hsides : highSide ≠ lowSide)
    (hfinal : ∀ (base : Fin b → Fin 2 ≃ Fin 2),
      (∀ t c, 2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack) →
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
    (hparent : ∀ (base : Fin b → Fin 2 ≃ Fin 2)
      (hbase : ∀ t c,
        2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack),
      let O := actualThresholdSwitchOrientation F slack lowBudget highBudget
        lowSide highSide hsmall hsides hfinal base hbase
      ∀ i,
        1 + reserve (branchRootSide F O.orient i) +
            sideLoadBefore F O.orient i (branchRootSide F O.orient i) ≤
          #((available (branchRootSide F O.orient i)).filter
            (G.Adj (externalParent i))))
    (hmargin : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(available c) : ℝ) - highBudget)) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        F G externalParent orient available) := by
  obtain ⟨base, hbase⟩ :=
    exists_prefix_balanced_orientation F slack hsmall
  let O := actualThresholdSwitchOrientation F slack lowBudget highBudget
    lowSide highSide hsmall hsides hfinal base hbase
  refine ⟨O.orient,
    exists_dynamicGroupEmbedding_of_thresholdSwitch F lowSide lowBudget
      highBudget O G externalParent whole available reserve rho density
      hlowHigh hunif havailable hwholeDisjoint hdensity hfactor hreserve
      havailableCapacity (hparent base hbase) hmargin⟩

/-- Compatibility form of the actual-cutoff theorem.  A caller with a
uniform low/high parent budget can still discharge the sharper actual-side
premise, but concrete Lemma-5.8 applications should prefer
`exists_actualThresholdDynamicGroupEmbedding_of_actualParent`. -/
theorem exists_actualThresholdDynamicGroupEmbedding
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b)
    (slack lowBudget highBudget : ℕ) (lowSide highSide : Fin 2)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hsides : highSide ≠ lowSide)
    (hfinal : ∀ (base : Fin b → Fin 2 ≃ Fin 2),
      (∀ t c, 2 * sideLoadPrefix F base t c ≤ prefixOrder F t + slack) →
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
    (hparent : ∀ i c,
      1 + reserve c +
          (if c = lowSide then lowBudget else highBudget) ≤
        #((available c).filter (G.Adj (externalParent i))))
    (hmargin : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(available c) : ℝ) - highBudget)) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        F G externalParent orient available) := by
  apply exists_actualThresholdDynamicGroupEmbedding_of_actualParent
    F slack lowBudget highBudget lowSide highSide hsmall hsides hfinal
    G externalParent whole available reserve rho density hlowHigh hunif
    havailable hwholeDisjoint hdensity hfactor hreserve havailableCapacity
  · intro base hbase O i
    have hpref := O.prefix_root_le hlowHigh i
    exact (Nat.add_le_add_left hpref
      (1 + reserve (branchRootSide F O.orient i))).trans
        (hparent i (branchRootSide F O.orient i))
  · exact hmargin

/-- The stronger full-prefix balanced subcase (cutoff after the last branch),
with the same concrete dynamic embedding conclusion.  Zhao Lemma 5.4(1) in
general still uses a maximal cutoff when the two source densities differ;
this theorem is not presented as that general endpoint. -/
theorem exists_fullPrefixBalancedDynamicGroupEmbedding
    {b : ℕ} {B : Type v} [Fintype B] [DecidableEq B]
    (F : OrderedRootedForest b)
    (slack lowBudget highBudget : ℕ) (lowSide highSide : Fin 2)
    (hsmall : ∀ i, F.size i ≤ slack)
    (hsides : highSide ≠ lowSide)
    (hcapacity : F.order + slack ≤ 2 * lowBudget)
    (hlowHigh : lowBudget ≤ highBudget)
    (G : SimpleGraph B) [DecidableRel G.Adj]
    (externalParent : Fin b → B)
    (whole available : Fin 2 → Finset B)
    (reserve : Fin 2 → ℕ) (rho density : ℝ)
    (hunif : G.IsUniform rho (whole 0) (whole 1))
    (havailable : ∀ c, available c ⊆ whole c)
    (hwholeDisjoint : Disjoint (whole 0) (whole 1))
    (hdensity : density ≤ G.edgeDensity (whole 0) (whole 1))
    (hfactor : 0 ≤ density - rho)
    (hreserve : ∀ c, rho * (#(whole c) : ℝ) ≤ reserve c)
    (havailableCapacity : ∀ c,
      highBudget + reserve c ≤ #(available c))
    (hparent : ∀ i c,
      1 + reserve c +
          (if c = lowSide then lowBudget else highBudget) ≤
        #((available c).filter (G.Adj (externalParent i))))
    (hmargin : ∀ i c,
      (F.size i : ℝ) + rho * (#(whole c) : ℝ) + 1 ≤
        (density - rho) *
          ((#(available c) : ℝ) - highBudget)) :
    ∃ orient : Fin b → Fin 2 ≃ Fin 2,
      Nonempty (DynamicAttachedForestEmbedding
        F G externalParent orient available) := by
  obtain ⟨O⟩ := exists_balancedThresholdSwitchOrientation F slack
    lowBudget highBudget lowSide highSide hsmall hsides hcapacity hlowHigh
  refine ⟨O.orient,
    exists_dynamicGroupEmbedding_of_thresholdSwitch F lowSide lowBudget
      highBudget O G externalParent whole available reserve rho density
      hlowHigh hunif havailable hwholeDisjoint hdensity hfactor hreserve
      havailableCapacity ?_ hmargin⟩
  intro i
  have hpref := O.prefix_root_le hlowHigh i
  exact (Nat.add_le_add_left hpref
    (1 + reserve (branchRootSide F O.orient i))).trans
      (hparent i (branchRootSide F O.orient i))

end Erdos547b.ZhaoLemma58ThresholdGroupEmbedding

#print axioms Erdos547b.ZhaoLemma58ThresholdGroupEmbedding.exists_thresholdDynamicGroupEmbedding
#print axioms Erdos547b.ZhaoLemma58ThresholdGroupEmbedding.exists_actualThresholdDynamicGroupEmbedding
#print axioms Erdos547b.ZhaoLemma58ThresholdGroupEmbedding.exists_fullPrefixBalancedDynamicGroupEmbedding
