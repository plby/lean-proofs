import ErdosProblems.Erdos118.StrictSecondOpening
import ErdosProblems.Erdos118.FreshCriticalCheckpoint

/-! Reach the actual target critical pair on the smallest source
alphabet, with both saved suffix bounds and the original target graph. -/

namespace Erdos118.StrictTargetCheckpoint

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns InsideCounts LastBodyRefinement

def rightTarget {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value}
    (W : StrictSecondOpening.Opening J) :
    Pending := applyBody (ofRoot W.target.rootSetup) W.opening.target

structure Checkpoint {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value}
    (W : StrictSecondOpening.Opening J) (d : ℕ) where
  left : Pending
  right : Pending
  leftExact : ExactSlots.Exact (.leaf left)
  rightExact : ExactSlots.Exact (.leaf right)
  critical : ∃ c : ℕ, left.roots = [c] ∧ left.leaves = []
  run : ConservativeRuns.Run W.prepared.alphabet (GraphPayoff.payoff J.graph .inside)
    (.leaf (StrictTwoRootRequests.target O), .leaf (rightTarget W)) (.leaf left, .leaf right)
  blue : RamseyGame.Outcome J.alphabet (GraphPayoff.game J.graph .inside
    (.leaf left, .leaf right)) true
  command : LeftBlue J.alphabet (GraphPayoff.payoff J.graph .inside) (.leaf left, .leaf right)
  fresh : FreshCheckpoints.FreshExtension W.prepared.alphabet d
    (.leaf (StrictTwoRootRequests.target O), .leaf (rightTarget W)) (.leaf left, .leaf right)
  before : ∀ x ∈ left.position.decorated, x < right.position.ordinary.getLastD 0
  order : left.position.ordinary.getLastD 0 < right.position.ordinary.getLastD 0
  leftRoot : left.position.stem.rootLabel = O.reserve.labels.upper
  rightRoot : right.position.stem.rootLabel = W.reserve.labels.upper
  rank : LabelRanks.rank right.position.stem.rootLabel
    (right.position.stem.done.length + 1) = J.rank
  last : right.leaves = [] ↔ value = true

theorem exists_checkpoint {H : Set ℕ} {B : SimpleGraph G} {O : StrictInitialOpening.Opening H B}
    {value : Bool} {J : StrictTwoRootRequests.Requests O value} (W : StrictSecondOpening.Opening J)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      CriticalPair.last T.stem (lastLabel S).length = value) (d : ℕ) :
    Nonempty (Checkpoint W d) := by
  let P₀ := StrictTwoRootRequests.target O
  let Q₀ := rightTarget W
  have hP₀ : ExactSlots.Exact (.leaf P₀) :=
    ExactSlots.step_exact (DecisionStates.Step.body (ofRoot O.target.rootSetup) O.opening.target)
      (ExactSlots.step_exact (DecisionStates.Step.root O.target.rootSetup) trivial)
  have hQ₀ : ExactSlots.Exact (.leaf Q₀) := W.opening.targetExact
  have hProots : P₀.roots ≠ [] := by
    intro he
    have hc := congrArg List.length he
    change O.target.rootSetup.stem.rootLabel.tail.length = 0 at hc
    rw [List.length_tail, O.target.rootSetup.label_length] at hc
    have hp := O.positive
    omega
  have hPleaves : P₀.leaves ≠ [] := by
    intro he
    have hc := congrArg List.length he
    change O.opening.target.position.label.tail.length = 0 at hc
    rw [List.length_tail, O.opening.target.label_length] at hc
    have hp := O.target.positive
    omega
  have hKH : W.prepared.alphabet ⊆ J.alphabet := W.prepared.subset.trans J.inserted.subset
  obtain ⟨P, Q, hcritical, hP, hQ, hr, hb, hh, hf, hbefore, horder⟩ :=
    FreshCriticalCheckpoint.critical_pair W.prepared.infinite hKH J.graph (.leaf P₀) (.leaf Q₀)
      hProots hP₀ hQ₀ W.opening.targetBlue (fun h ↦ (hPleaves h.choose_spec.2).elim) d
  have hP₀root : P₀.position.stem.rootLabel = O.reserve.labels.upper := by
    change O.opening.target.position.stem.rootLabel = _
    rw [O.opening.target.stem_eq]
    exact O.target.rootLabel
  have hQ₀root : Q₀.position.stem.rootLabel = W.reserve.labels.upper := by
    change W.opening.target.position.stem.rootLabel = _
    rw [W.opening.target.stem_eq]
    exact W.target.rootLabel
  have hPLabel : P.position.stem.rootLabel = O.reserve.labels.upper :=
    (Option.some.inj ((SkippedCuts.run_extensions hr).1.labels.root _ rfl)).trans hP₀root
  have hQLabel : Q.position.stem.rootLabel = W.reserve.labels.upper :=
    (Option.some.inj ((SkippedCuts.run_extensions hr).2.labels.root _ rfl)).trans hQ₀root
  obtain ⟨S, T, hp, heP, heQ, _, hbodyRank, _, hlast⟩ :=
    CriticalCursor.at_left_endpoint J.infinite J.graph P Q hP hQ hcritical horder hb
  have hSLabel : S.stem.rootLabel = O.reserve.labels.upper :=
    (Option.some.inj (heP.labels.root _ rfl)).trans hPLabel
  have hTLabel : T.stem.rootLabel = W.reserve.labels.upper :=
    (Option.some.inj (heQ.labels.root _ rfl)).trans hQLabel
  have hSlen : 1 < S.stem.rootLabel.length := by
    rw [hSLabel, O.reserve.labels.upperCard]
    have h := O.positive
    omega
  have hTlen : T.stem.rootLabel.length = J.upper.size + 1 := by
    rw [hTLabel, W.reserve.labels.upperCard]
  have hfixed := (J.exactRank S T hp hSlen hTlen).1
  have hrank : LabelRanks.rank Q.position.stem.rootLabel
      (Q.position.stem.done.length + 1) = J.rank := hbodyRank.symm.trans hfixed
  have hlastEq := hall S T (LastMarkerRefinement.payoff_true_mono J.subgraph .inside S T hp)
  rw [hlastEq] at hlast
  exact ⟨{
    left := P, right := Q, leftExact := hP, rightExact := hQ, critical := hcritical
    run := hr, blue := hb, command := hh, fresh := hf, before := hbefore, order := horder
    leftRoot := hPLabel, rightRoot := hQLabel, rank := hrank, last := hlast.symm }⟩

end Erdos118.StrictTargetCheckpoint
