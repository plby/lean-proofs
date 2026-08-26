import ErdosProblems.Erdos118.StrictBodyLocalization
import ErdosProblems.Erdos118.LabelRanks
import ErdosProblems.Erdos118.RootBodyCheckpoint

/-! An actual stopped run reaches the right body selected by the
localized critical rank; terminal extensions identify that exact body. -/

namespace Erdos118.StrictBodyCheckpoint

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns InsideCounts LastBodyRefinement CriticalPair

theorem right {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T)
    (P : Pending) (hP : ExactSlots.Exact (.leaf P)) (hPlen : 1 < P.position.stem.rootLabel.length)
    (k value : ℕ) (hv : 0 < value) (hvle : value ≤ k + 1)
    (hcolor : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      1 < S.stem.rootLabel.length → T.stem.rootLabel.length = k + 1 →
      bodyRank T.stem (lastLabel S).length = value)
    (A : RootResponses.Setup k)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .body (ofRoot A))) true)
    (d : ℕ) :
    ∃ Q : Pending, ∃ D : BodyDecision,
      ExactSlots.Exact (.leaf Q) ∧ ExactSlots.Exact (.body D) ∧
      ConservativeRuns.Run H (GraphPayoff.payoff B .inside)
        (.leaf P, .body (ofRoot A)) (.leaf Q, .body D) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf Q, .body D)) true ∧
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf Q, .body D) ∧
      FreshCheckpoints.FreshExtension H d (.leaf P, .body (ofRoot A)) (.leaf Q, .body D) ∧
      Q.position.stem.rootLabel = P.position.stem.rootLabel ∧ D.stem.rootLabel = A.stem.rootLabel ∧
      LabelRanks.rank D.stem.rootLabel (D.stem.done.length + 1) = value ∧
      (∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
        SkippedCuts.StateExtension (.leaf Q) (.complete S) →
        SkippedCuts.StateExtension (.body D) (.complete T) →
        (CriticalPair.pair T.stem (lastLabel S).length).1 = D.stem.done.length) := by
  obtain ⟨r, hr, hrv⟩ := LabelRanks.exists_label A.stem.rootLabel A.stem.label_pairwise.nodup
    value hv (A.label_length ▸ hvle)
  obtain ⟨D, Y, hi, hD, hnobody, hrun, hb, hh, hf⟩ := RootBodyCheckpoint.right
    hH Set.Subset.rfl B .inside r d (.body (ofRoot A)) (.leaf P)
    (RootBodyCheckpoint.root_before A hr)
    (ExactSlots.step_exact (DecisionStates.Step.root A) trivial) (by simp) hblue
  have hY : ∃ Q : Pending, Y = .leaf Q := by
    cases Y with
    | initial =>
      have hpre := (SkippedCuts.run_extensions hrun).1.ordinary
      have hlen := hpre.length_le
      simp [State.ordinary, Position.ordinary, Stem.ordinary] at hlen
    | body E => exact (hnobody E rfl).elim
    | complete S =>
      exact (InsideEndgame.complete_incomplete_not_blue hH B S (.body D) (by simp) hb).elim
    | leaf Q => exact ⟨Q, rfl⟩
  obtain ⟨Q, rfl⟩ := hY
  have hQ := ExactSlots.run_exact_left hrun hP
  obtain ⟨heP, heA⟩ := SkippedCuts.run_extensions hrun
  have hQroot : Q.position.stem.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (heP.labels.root _ rfl)
  have hDroot : D.stem.rootLabel = A.stem.rootLabel := Option.some.inj (heA.labels.root _ rfl)
  have hDrank : LabelRanks.rank D.stem.rootLabel (D.stem.done.length + 1) = value := by
    rw [hDroot, hi]
    exact hrv
  refine ⟨Q, D, hQ, hD, hrun, hb, hh, hf, hQroot, hDroot, hDrank, ?_⟩
  intro S T hp heQ heD
  have hSroot : S.stem.rootLabel = P.position.stem.rootLabel :=
    (Option.some.inj (heQ.labels.root _ rfl)).trans hQroot
  have hTroot : T.stem.rootLabel = D.stem.rootLabel := Option.some.inj (heD.labels.root _ rfl)
  have hSL : 1 < S.stem.rootLabel.length := hSroot ▸ hPlen
  have hTL : T.stem.rootLabel.length = k + 1 := by rw [hTroot, hDroot, A.label_length]
  have hval := hcolor S T hp hSL hTL
  obtain ⟨_, hspec, _, _, _, _⟩ := StrictCriticalBounds.terminal B S T hp hSL (hall S T hp)
  have hc := ((GraphPayoff.payoff_true_iff B .inside S T).mp hp).2.1
  have hcrit := StrictCriticalBounds.selected_root T.stem S.stem hc.exactRight
    (CriticalPair.pair T.stem (lastLabel S).length) hspec.1
  have hcur : D.stem.done.length + 1 ∈ T.stem.rootLabel := hTroot ▸ D.rootSelected
  have hrank : LabelRanks.rank T.stem.rootLabel (D.stem.done.length + 1) = value :=
    hTroot ▸ hDrank
  have heq := LabelRanks.rank_injective hcrit hcur (hval.trans hrank.symm)
  omega

end Erdos118.StrictBodyCheckpoint
