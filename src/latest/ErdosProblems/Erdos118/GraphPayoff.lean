import ErdosProblems.Erdos118.AdaptiveGame
import ErdosProblems.Erdos118.ClearPairs

/-!
The explicit inside/outside graph payoffs on completed clear pairs.
Terminal red certificates imply a red edge. No assertion is made that such
certificates are inherited from initial states without a conservative run,
or that an initial blue certificate forces a triangle.
-/

namespace Erdos118.GraphPayoff

open Negative Negative.Exact LabelledExtensions DecisionStates ClearPairs

def vertex (S : Completed) : G := S.stem.toGood S.full

theorem vertex_eq_of_ordinary_eq {S T : Completed}
    (h : S.stem.ordinary = T.stem.ordinary) : vertex S = vertex T := by
  have hw : word (vertex S).1 = word (vertex T).1 :=
    (S.stem.toGood_word S.full).trans (h.trans (T.stem.toGood_word T.full).symm)
  exact Subtype.ext (WordResponses.word_prefix_rigid (hw ▸ List.prefix_rfl))

def endpoint (S : Stem) : ℕ := S.ordinary.getLast (by simp [Stem.ordinary])

theorem endpoint_mem (S : Stem) : endpoint S ∈ S.ordinary := List.getLast_mem _

theorem endpoints_ne {S T : Stem} (h : ClearPair S T) : endpoint S ≠ endpoint T := by
  exact (foreign_ne h.disjoint (endpoint_mem T)
    (S.ordinary_sublist.subset (endpoint_mem S))).symm

inductive Orientation
  | inside
  | outside

def Oriented : Orientation → Stem → Stem → Prop
  | .inside, S, T => endpoint T < endpoint S
  | .outside, S, T => endpoint S < endpoint T

theorem oriented_exists {S T : Stem} (h : ClearPair S T) : ∃ o, Oriented o S T := by
  rcases lt_or_gt_of_ne (endpoints_ne h) with hlt | hgt
  · exact ⟨.outside, hlt⟩
  · exact ⟨.inside, hgt⟩

noncomputable def payoff (B : SimpleGraph G) (o : Orientation) (S T : Completed) : Bool := by
  classical
  exact decide (S.stem.root < T.stem.root ∧ ClearPair S.stem T.stem ∧
    Oriented o S.stem T.stem ∧ B.Adj (vertex S) (vertex T))

theorem payoff_true_iff (B : SimpleGraph G) (o : Orientation) (S T : Completed) :
    payoff B o S T = true ↔ S.stem.root < T.stem.root ∧ ClearPair S.stem T.stem ∧
      Oriented o S.stem T.stem ∧ B.Adj (vertex S) (vertex T) := by
  classical
  simp only [payoff, decide_eq_true_eq]

noncomputable def game (B : SimpleGraph G) (o : Orientation) :
    (State × State) → RamseyGame.Game := AdaptiveGame.game (payoff B o)

theorem terminal_red (B : SimpleGraph G) (o : Orientation) (S T : Completed)
    {H : Set ℕ} (h : RamseyGame.Outcome H (game B o (.complete S, .complete T)) false)
    (hroot : S.stem.root < T.stem.root) (hclear : ClearPair S.stem T.stem)
    (horient : Oriented o S.stem T.stem) : ¬ B.Adj (vertex S) (vertex T) := by
  rw [game, AdaptiveGame.game_complete] at h
  have hfalse := RamseyGame.outcome_leaf_iff.mp h
  intro hedge
  have htrue := (payoff_true_iff B o S T).mpr ⟨hroot, hclear, horient, hedge⟩
  exact Bool.noConfusion (htrue.symm.trans hfalse)

theorem terminal_red_of_both (B : SimpleGraph G) (S T : Completed) {H : Set ℕ}
    (hinside : RamseyGame.Outcome H (game B .inside (.complete S, .complete T)) false)
    (houtside : RamseyGame.Outcome H (game B .outside (.complete S, .complete T)) false)
    (hroot : S.stem.root < T.stem.root) (hclear : ClearPair S.stem T.stem) :
    ¬ B.Adj (vertex S) (vertex T) := by
  obtain ⟨o, ho⟩ := oriented_exists hclear
  cases o with
  | inside => exact terminal_red B .inside S T hinside hroot hclear ho
  | outside => exact terminal_red B .outside S T houtside hroot hclear ho

theorem outcome_thinning (B : SimpleGraph G) (o : Orientation) (S : State × State)
    {N : Set ℕ} (hN : N.Infinite) :
    ∃ H ⊆ N, H.Infinite ∧ ∃ value, RamseyGame.Outcome H (game B o S) value :=
  AdaptiveGame.outcome_thinning (payoff B o) S hN

end Erdos118.GraphPayoff
