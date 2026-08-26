import ErdosProblems.Erdos118.TwoMiddlePositive

/-! In a triangle-free graph the remaining third-game body is singleton.
Its actual next request is a later body, not final completion. -/

namespace Erdos118.SingletonMiddleRequest

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays

theorem singleton {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (hB : B.CliqueFree 3)
    {O : LateOpening.Opening H B} (D : FirstMiddle.Diagram O) :
    O.second.target.position.label = [O.insertedRight.position.entries.length] := by
  rcases O.second.shape with hs | ⟨_, hm, hn⟩
  · exact hs
  · obtain ⟨s, t, u, hst, hsu, htu⟩ := TwoMiddlePositive.triangle hH B D hm hn
    exact (hB {s, t, u} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hst, hsu, htu⟩)).elim

theorem slots {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (hB : B.CliqueFree 3)
    {O : LateOpening.Opening H B} (D : FirstMiddle.Diagram O) :
    O.second.target.leaves = [] ∧ O.second.target.roots ≠ [] := by
  have hs := singleton hH B hB D
  have hL : O.second.target.leaves = [] := by
    rw [O.second.exactSlots.2]
    simp [ExactSlots.above, hs, O.second.entries]
  have hfirst : O.first.target.roots ≠ [] :=
    NextSelectedLeaf.first_roots_nonempty O.first.target O.first.exactSlots O.first.firstBody
      (by rw [O.first.rootLength]; have hp := O.initialPositive; omega)
  refine ⟨hL, ?_⟩
  intro hR
  have he := InsideEndgame.last_right_command_left_last hH B D.replay.target
    O.second.target hR hL D.replay.handoff
  exact hfirst (D.replay.roots.symm.trans he.1)

structure Request {H : Set ℕ} {B : SimpleGraph G} {O : LateOpening.Opening H B}
    (D : FirstMiddle.Diagram O) where
  index : ℕ
  rest : List ℕ
  roots : O.second.target.roots = index :: rest
  leaves : O.second.target.leaves = []
  bound : ℕ
  certificate : ∀ Q : Stem, ∀ v : List ℕ,
    Q.root = O.second.target.position.stem.root → Q.done.length = index - 1 →
    Q.ordinary = O.second.target.position.ordinary ++ v →
    (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, bound < x) →
    ∃ A : StemResponses.Setup O.second.target.position (index - 1), A.newWord = v ∧
      A.stem.ordinary = Q.ordinary ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
        (.leaf D.replay.target, .leaf O.second.target)
        (.leaf D.replay.target, .body (ofStem O.second.target index rest roots A)) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside
        (.leaf D.replay.target, .body (ofStem O.second.target index rest roots A))) true

theorem exists_request {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (hB : B.CliqueFree 3)
    {O : LateOpening.Opening H B} (D : FirstMiddle.Diagram O) : Nonempty (Request D) := by
  obtain ⟨hL, hR⟩ := slots hH B hB D
  obtain ⟨c, rest, hRc⟩ := List.exists_cons_of_ne_nil hR
  obtain ⟨b, hb⟩ := StemReplay.right_body_words_step (GraphPayoff.payoff B .inside)
    (.leaf D.replay.target) O.second.target c rest hRc hL D.replay.handoff
  exact ⟨⟨c, rest, hRc, hL, b, hb⟩⟩

end Erdos118.SingletonMiddleRequest
