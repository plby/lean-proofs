import ErdosProblems.Erdos547.ShrubPostponement

/-!
# At most two exceptional root families in each head cluster
-/

namespace Erdos547.ShrubHostSetup

open Finset SimpleGraph
open scoped BigOperators

variable {U V I : Type*} [Fintype U] [Fintype I]
  [DecidableEq U] [DecidableEq V] [DecidableEq I]
  {T : SimpleGraph U} [DecidableRel T.Adj] {r : U} {ℓ : ℕ}
  {col : T.Coloring (Fin 2)} {P : FineTreePartition T r ℓ col}
  {G : SimpleGraph V} [DecidableRel G.Adj]
variable (H : ShrubHostSetup P G I)

theorem postponed_same_head_count (E : H.State) (F : Finset ↥P.shrubs)
    (hEF : Disjoint E.placed F) (hcap : ∀ a i, (E.farLoad a i : ℝ) ≤ H.capacity a i)
    (B : Finset ↥P.shrubs) (i : I) (hhead : ∀ A ∈ B, H.head A = i)
    (hfailed : ∀ A ∈ B, H.FailedAt E F A) : (B.card : ℝ) ≤ 2 * H.ε * H.m := by
  classical
  have hpart (c : Fin 2) : ((B.filter (fun A ↦ P.shrubColour A = c)).card : ℝ) ≤ H.ε * H.m := by
    rcases Finset.eq_empty_or_nonempty (B.filter (fun A ↦ P.shrubColour A = c)) with he | ⟨S, hS⟩
    · rw [he, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg H.ε_pos.le (Nat.cast_nonneg _)
    · apply H.postponed_group_count E F hEF hcap _ S
      · intro A hA
        apply Prod.ext
        · exact (Finset.mem_filter.mp hA).2.trans (Finset.mem_filter.mp hS).2.symm
        · exact (hhead A (Finset.mem_filter.mp hA).1).trans
            (hhead S (Finset.mem_filter.mp hS).1).symm
      · intro A hA
        exact hfailed A (Finset.mem_filter.mp hA).1
  have hsplit : B.card = ∑ c : Fin 2, (B.filter (fun A ↦ P.shrubColour A = c)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_univ _)
  have hsplitR : (B.card : ℝ) = ∑ c : Fin 2, ((B.filter (fun A ↦ P.shrubColour A = c)).card : ℝ) := by
    exact_mod_cast hsplit
  rw [hsplitR]
  calc
    _ ≤ ∑ _c : Fin 2, H.ε * H.m := Finset.sum_le_sum fun c _ ↦ hpart c
    _ = 2 * H.ε * H.m := by simp; ring

end Erdos547.ShrubHostSetup

#print axioms Erdos547.ShrubHostSetup.postponed_same_head_count
