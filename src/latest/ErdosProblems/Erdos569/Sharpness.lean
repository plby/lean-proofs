/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleCode

/-!
# The sharpness obstruction for Erdős Problem 569

For every finite graph `F`, `R(F,K₂) = |F|`. In particular no coefficient
smaller than `2r + 1` can bound `R(C_(2r+1),H)` by the number of edges of `H`.
This is the sharpness observation in Cambie--Freschi, arXiv:2606.11174v1.
-/

open scoped SimpleGraph

namespace Erdos569

open Erdos79 Erdos570

/-- An edge as one Ramsey target makes the Ramsey number equal to the
order of the other target. Copies here are not required to be induced. -/
theorem graphRamseyNumber_completeTwo (F : GraphCode) :
    graphRamseyNumber F (completeCode 2) = F.vertexCount := by
  classical
  apply le_antisymm
  · apply graphRamseyNumber_le_of_ramseyAt
    intro C
    by_cases h : Cᶜ.CliqueFree 2
    · left
      have hc : C = ⊤ := by
        have he := congrArg compl (SimpleGraph.cliqueFree_two.mp h)
        simpa only [compl_compl, compl_bot] using he
      rw [hc]
      exact SimpleGraph.IsContained.of_le le_top
    · right
      exact (SimpleGraph.not_cliqueFree_iff_top_isContained 2).mp h
  · rcases graphRamseyNumber_spec F (completeCode 2) ⊤ with hF | hE
    · exact IsContained.vertexCount_le
        (G := ⟨graphRamseyNumber F (completeCode 2), ⊤⟩) hF
    · have he : (⊤ : SimpleGraph (Fin 2)) ⊑
          (⊥ : SimpleGraph (Fin (graphRamseyNumber F (completeCode 2)))) := by
        change (⊤ : SimpleGraph (Fin 2)) ⊑
          (⊤ : SimpleGraph (Fin (graphRamseyNumber F (completeCode 2))))ᶜ at hE
        simpa only [compl_top] using hE
      exact (he.not_cliqueFree (SimpleGraph.cliqueFree_two.mpr rfl)).elim

theorem completeTwo_edgeCount : (completeCode 2).edgeCount = 1 := by
  classical
  change Nat.card (⊤ : SimpleGraph (Fin 2)).edgeSet = 1
  rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  decide

theorem completeTwo_noIsolated : NoIsolated (completeCode 2) := by
  change ∀ v : Fin 2, ¬ (⊤ : SimpleGraph (Fin 2)).IsIsolated v
  intro v
  apply SimpleGraph.exists_adj_iff_not_isIsolated.mp
  fin_cases v
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩

/-- The exact one-edge test case, including all odd cycle lengths. -/
theorem cycle_completeTwo (k : ℕ) :
    graphRamseyNumber (cycleCode k) (completeCode 2) = k :=
  graphRamseyNumber_completeTwo (cycleCode k)

/-- Any real coefficient valid uniformly over all graphs without isolated
vertices must be at least the length of the cycle. -/
theorem coefficient_lower_bound {k : ℕ} {c : ℝ}
    (h : ∀ H : GraphCode, NoIsolated H →
      (graphRamseyNumber (cycleCode k) H : ℝ) ≤ c * H.edgeCount) :
    (k : ℝ) ≤ c := by
  have hb := h (completeCode 2) completeTwo_noIsolated
  simpa only [cycle_completeTwo, completeTwo_edgeCount, Nat.cast_one, mul_one] using hb

end Erdos569
