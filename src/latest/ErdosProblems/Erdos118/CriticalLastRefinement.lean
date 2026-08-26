import ErdosProblems.Erdos118.IntrinsicAnnotations
import ErdosProblems.Erdos118.StrictInitialOpening

/-! Fix the critical last-leaf alternative globally before the strict
construction and recover it at actual pending critical endpoints. -/

namespace Erdos118.CriticalLastRefinement

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns FirstBodyRefinement LastBodyRefinement InsideCounts

theorem exists_refined {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (hfirst : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (firstLabel S).length ≠ 1)
    (hstrict : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T) :
    ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      RamseyGame.Outcome K (GraphPayoff.game C .inside (.initial, .initial)) true ∧
      ∃ value : Bool, ∀ S T : Completed, GraphPayoff.payoff C .inside S T = true →
        (firstLabel S).length ≠ 1 ∧ beforeLast S < beforeLast T ∧
          CriticalPair.last T.stem (lastLabel S).length = value := by
  classical
  obtain ⟨K, hKH, hK, C, hCB, hC, hbC, value, htest⟩ := IntrinsicAnnotations.refine_test
    hH B hB .inside hinit (fun S T ↦ CriticalPair.last T.stem (lastLabel S).length = true)
  refine ⟨K, hKH, hK, C, hCB, hC, hbC, value, ?_⟩
  intro S T hp
  have hpB := LastMarkerRefinement.payoff_true_mono hCB .inside S T hp
  refine ⟨hfirst S T hpB, hstrict S T hpB, ?_⟩
  have hd : @decide (CriticalPair.last T.stem (lastLabel S).length = true)
      (Classical.propDecidable _) =
      CriticalPair.last T.stem (lastLabel S).length := by
    cases CriticalPair.last T.stem (lastLabel S).length <;> simp
  exact hd.symm.trans (htest S T hp)

theorem at_critical {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (value : Bool)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      CriticalPair.last T.stem (lastLabel S).length = value)
    (P Q : Pending) (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (hcritical : ∃ c : ℕ, P.roots = [c] ∧ P.leaves = [])
    (horder : P.position.ordinary.getLastD 0 < Q.position.ordinary.getLastD 0)
    (hb : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true) :
    Q.leaves = [] ↔ value = true := by
  obtain ⟨S, T, hp, _, _, _, _, _, hlast⟩ :=
    CriticalCursor.at_left_endpoint hH B P Q hP hQ hcritical horder hb
  rw [hall S T hp] at hlast
  exact hlast.symm

theorem initial_opening {H : Set ℕ} {B : SimpleGraph G} (O : StrictInitialOpening.Opening H B)
    (value : Bool) (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      CriticalPair.last T.stem (lastLabel S).length = value) :
    O.prepared.leafRank = O.prepared.size + 1 ↔ value = true := by
  have hcolor : ∀ S T : Completed, GraphPayoff.payoff O.prepared.graph .inside S T = true →
      CriticalPair.last T.stem (lastLabel S).length = value :=
    fun S T hp ↦ hall S T (LastMarkerRefinement.payoff_true_mono
      (O.prepared.subgraph.trans O.subgraph) .inside S T hp)
  have hlast := at_critical O.prepared.infinite O.prepared.graph value hcolor
    O.opening.checkpoint.left O.opening.checkpoint.right
    O.opening.checkpoint.leftExact O.opening.checkpoint.rightExact
    O.opening.checkpoint.criticalLeft O.opening.checkpoint.order O.opening.checkpoint.blue
  exact O.opening.lastIff.symm.trans hlast

end Erdos118.CriticalLastRefinement
