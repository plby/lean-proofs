import ErdosProblems.Erdos547.SkewRoutingCapacity
import ErdosProblems.Erdos547.ShrubStateLoads

/-!
# The shrub allocation bounds imply the routing setup budgets
-/

namespace Erdos547

open Finset
open scoped BigOperators

open scoped Classical in
theorem sum_group_condition {F C : Type*} [Fintype F] [Fintype C]
    [DecidableEq C] (group : F → C) (p : F → Prop) [DecidablePred p] (w : F → ℝ) :
    (∑ c, ∑ x ∈ (Finset.univ : Finset F).filter (fun x ↦ group x = c ∧ p x), w x) =
      ∑ x, if p x then w x else 0 := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p x
  · simp only [hx, and_true, if_true]
    simp
  · simp only [hx, and_false, if_false, Finset.sum_const_zero]

end Erdos547

namespace Erdos547.FineTreePartition

open Finset SimpleGraph
open scoped BigOperators

variable {U I : Type*} [Fintype U] [DecidableEq U] [Fintype I] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} (P : FineTreePartition T r ℓ col)
  {K : SimpleGraph I} {γ : Fin 2 → ℝ}

open scoped Classical in
theorem cluster_budget_of_skew_heads (σ : ∀ c, DPRS.SkewMatching K (γ c))
    (M : ℝ) (hM : 0 ≤ M) (head : ↥P.shrubs → I)
    (hload : ∀ i, (∑ c, (σ c).load i) ≤ 1)
    (hnear : ∀ c i, (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter
      (fun S ↦ P.shrubColour S = c ∧ head S = i), ((P.nearPart S).card : ℝ)) ≤ M * (σ c).outLoad i)
    (i : I) :
    (∑ S, if head S = i then ((P.nearPart S).card : ℝ) else 0) +
      (∑ a, DPRS.familyCapacity σ M a i) ≤ M := by
  classical
  apply DPRS.familyCapacity_budget σ M _ hM i (hload i)
  rw [← sum_group_condition P.shrubColour (fun S ↦ head S = i)
    (fun S ↦ ((P.nearPart S).card : ℝ)), Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ ↦ hnear c i

open scoped Classical in
theorem group_demand_of_skew_heads (σ : ∀ c, DPRS.SkewMatching K (γ c))
    (M s : ℝ) (head : ↥P.shrubs → I)
    (hfar : ∀ c i, (∑ S ∈ (Finset.univ : Finset ↥P.shrubs).filter
      (fun S ↦ P.shrubColour S = c ∧ head S = i), ((P.farPart S).card : ℝ)) ≤
        (1 - s) * M * γ c * (σ c).outLoad i)
    (a : Fin 2 × I) :
    (∑ S, if ShrubState.shrubGroup P head S = a then ((P.farPart S).card : ℝ) else 0) ≤
      (1 - s) * ∑ i, DPRS.familyCapacity σ M a i := by
  classical
  rcases a with ⟨c, i⟩
  simp only [DPRS.familyCapacity, DPRS.SkewMatching.arcCapacity_row,
    ShrubState.shrubGroup, Prod.mk.injEq]
  have hh := hfar c i
  rw [Finset.sum_filter] at hh
  convert hh using 1 <;> ring

end Erdos547.FineTreePartition

#print axioms Erdos547.FineTreePartition.cluster_budget_of_skew_heads
#print axioms Erdos547.FineTreePartition.group_demand_of_skew_heads
