/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRecursiveDecoratedProfileCode
import ErdosProblems.Erdos1165.AnnularProfileNestedEdge

/-!
# Ordered refinement trees associated with a profile gap chain

A weak-composition chain already contains the complete ordered genealogy of
the radial returns.  This module converts that genealogy into the erased-
parent refinement trees used by the literal recursive code.  It also proves
the exact reference-cost identity.  Thus the corrected recursive row has the
same `gapChainMass` combinatorics as the familiar profile calculation,
without counting any physical child interval twice.
-/

open scoped BigOperators

namespace Erdos1165.AnnularRecursiveProfileShape

open AnnularProfileNestedEdge AnnularRecursiveDecoratedProfileCode
open AppendixFirstMoment PathInsertion ProfileGapChain

noncomputable section

/-- Turn an ordinary ordered list into the mutual forest representation. -/
def ProfileRefinementForest.ofList :
    List ProfileRefinementTree → ProfileRefinementForest
  | [] => .nil
  | tree :: rest => .cons tree (ProfileRefinementForest.ofList rest)

/-- Forget the mutual wrapper and recover the ordered list of children. -/
def ProfileRefinementForest.toList :
    ProfileRefinementForest → List ProfileRefinementTree
  | .nil => []
  | .cons tree rest => tree :: ProfileRefinementForest.toList rest

@[simp] theorem ProfileRefinementForest.toList_ofList
    (children : List ProfileRefinementTree) :
    ProfileRefinementForest.toList
        (ProfileRefinementForest.ofList children) = children := by
  induction children with
  | nil => rfl
  | cons tree rest ih =>
      simp only [ProfileRefinementForest.ofList,
        ProfileRefinementForest.toList, ih]

/- Reference cost of a corrected recursive tree and its child forest.
Each retained inward piece and the final escape contributes one common
half-row factor. -/
mutual
  /-- Reference cost of one corrected recursive tree. -/
  def profileRefinementTreeCost (halfRow : ℝ) :
      ProfileRefinementTree → ℝ
    | .leaf => 1
    | .node children => profileRefinementForestCost halfRow children

  /-- Reference cost of an ordered child forest. -/
  def profileRefinementForestCost (halfRow : ℝ) :
      ProfileRefinementForest → ℝ
    | .nil => halfRow
    | .cons child tail =>
        halfRow * profileRefinementTreeCost halfRow child *
          profileRefinementForestCost halfRow tail
end

mutual
  theorem profileRefinementTreeCost_nonneg
      {halfRow : ℝ} (hhalf : 0 ≤ halfRow) :
      ∀ tree, 0 ≤ profileRefinementTreeCost halfRow tree
    | .leaf => by simp [profileRefinementTreeCost]
    | .node children =>
        profileRefinementForestCost_nonneg hhalf children

  theorem profileRefinementForestCost_nonneg
      {halfRow : ℝ} (hhalf : 0 ≤ halfRow) :
      ∀ forest, 0 ≤ profileRefinementForestCost halfRow forest
    | .nil => by simpa [profileRefinementForestCost] using hhalf
    | .cons child tail => by
        exact mul_nonneg
          (mul_nonneg hhalf (profileRefinementTreeCost_nonneg hhalf child))
          (profileRefinementForestCost_nonneg hhalf tail)
end

/-- Closed product form for the cost of an ordered child list. -/
theorem profileRefinementForestCost_ofList (halfRow : ℝ) :
    ∀ children : List ProfileRefinementTree,
      profileRefinementForestCost halfRow
          (ProfileRefinementForest.ofList children) =
        halfRow ^ (children.length + 1) *
          (children.map (profileRefinementTreeCost halfRow)).prod
  | [] => by simp [ProfileRefinementForest.ofList,
      profileRefinementForestCost]
  | child :: tail => by
      rw [ProfileRefinementForest.ofList,
        profileRefinementForestCost,
        profileRefinementForestCost_ofList]
      simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
      ring

/-- The ordered refinement tree rooted at every parent excursion of a fixed
weak-composition chain. -/
def profileRefinementTrees :
    ∀ (a : ℕ) (rest : List ℕ),
      GapChain (a :: rest) → Fin a → ProfileRefinementTree
  | _a, [], _chain, _i => .leaf
  | _a, b :: rest, chain, i =>
      .node (ProfileRefinementForest.ofList (List.ofFn fun j :
        Fin (gapMultiplicity chain.1 i) =>
          profileRefinementTrees b rest chain.2
            (gapChildIndexEquiv chain.1 ⟨i, j⟩)))

private theorem prod_nested_children_eq
    {a b : ℕ} (g : GapPattern a b) (f : Fin b → ℝ) :
    (∏ i : Fin a, ∏ j : Fin (gapMultiplicity g i),
        f (gapChildIndexEquiv g ⟨i, j⟩)) =
      ∏ r : Fin b, f r := by
  simpa only [Fintype.prod_sigma] using
    (Fintype.prod_equiv (gapChildIndexEquiv g)
      (fun p : (i : Fin a) × Fin (gapMultiplicity g i) => f
        (gapChildIndexEquiv g p)) f (fun _ => rfl))

/-- A fixed gap chain has exactly its usual geometric reference mass after
the physical parent gaps are erased and every recursive child is inserted
once. -/
theorem prod_profileRefinementTreeCost_eq :
    ∀ (a : ℕ) (rest : List ℕ) (chain : GapChain (a :: rest))
      (halfRow : ℝ),
      (∏ i : Fin a,
          profileRefinementTreeCost halfRow
            (profileRefinementTrees a rest chain i)) =
        (2 * halfRow) ^
            (AnnularIntegratedProfileKernel.radialWordLength (a :: rest)) *
          gapChainMass (a :: rest) chain
  | _a, [], _chain, halfRow => by
      simp [profileRefinementTrees, profileRefinementTreeCost,
        AnnularIntegratedProfileKernel.radialWordLength, gapChainMass]
  | a, b :: rest, chain, halfRow => by
      let childCost : Fin b → ℝ := fun r =>
        profileRefinementTreeCost halfRow
          (profileRefinementTrees b rest chain.2 r)
      have hchildren :
          (∏ i : Fin a,
              (List.ofFn fun j : Fin (gapMultiplicity chain.1 i) =>
                childCost (gapChildIndexEquiv chain.1 ⟨i, j⟩)).prod) =
            ∏ r : Fin b, childCost r := by
        simpa only [List.prod_ofFn] using
          prod_nested_children_eq chain.1 childCost
      have hsum :
          ∑ i : Fin a, (gapMultiplicity chain.1 i + 1) = a + b := by
        rw [Finset.sum_add_distrib, sum_gapMultiplicity]
        simp
        omega
      rw [show (∏ i : Fin a,
          profileRefinementTreeCost halfRow
            (profileRefinementTrees a (b :: rest) chain i)) =
          ∏ i : Fin a,
            (halfRow ^ (gapMultiplicity chain.1 i + 1) *
              (List.ofFn fun j : Fin (gapMultiplicity chain.1 i) =>
                childCost (gapChildIndexEquiv chain.1 ⟨i, j⟩)).prod) by
        apply Finset.prod_congr rfl
        intro i _hi
        rw [profileRefinementTrees, profileRefinementTreeCost,
          profileRefinementForestCost_ofList]
        simp only [List.length_ofFn, List.map_ofFn]
        rfl]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum,
        hchildren, prod_profileRefinementTreeCost_eq b rest chain.2]
      simp only [AnnularIntegratedProfileKernel.radialWordLength,
        gapChainMass, pow_add]
      rw [← pow_add halfRow a b, ← pow_add (2 * halfRow) a b]
      rw [show halfRow ^ (a + b) =
          (2 * halfRow) ^ (a + b) *
            (∏ i : Fin a, halfGeometricMass
              (gapMultiplicity chain.1 i)) by
        rw [AppendixFirstMoment.prod_halfGeometricMass]
        rw [← mul_pow]
        congr 1
        ring]
      ring

end

end Erdos1165.AnnularRecursiveProfileShape
