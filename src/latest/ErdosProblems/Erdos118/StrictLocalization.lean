import ErdosProblems.Erdos118.StrictBodyCheckpoint
import ErdosProblems.Erdos118.StrictLeafLocalization

/-! Compose the actual body checkpoint with leaf-rank refinement,
retaining a caller's root setup and the two different graph stages. -/

namespace Erdos118.StrictLocalization

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns InsideCounts LastBodyRefinement CriticalPair

structure Prepared (H : Set ℕ) (B : SimpleGraph G) (P : Pending) {k : ℕ}
    (A : RootResponses.Setup k) (value d : ℕ) where
  left : Pending
  body : BodyDecision
  leftExact : ExactSlots.Exact (.leaf left)
  bodyExact : ExactSlots.Exact (.body body)
  run : ConservativeRuns.Run H (GraphPayoff.payoff B .inside)
    (.leaf P, .body (ofRoot A)) (.leaf left, .body body)
  blue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf left, .body body)) true
  fresh : FreshCheckpoints.FreshExtension H d
    (.leaf P, .body (ofRoot A)) (.leaf left, .body body)
  leftRoot : left.position.stem.rootLabel = P.position.stem.rootLabel
  bodyRoot : body.stem.rootLabel = A.stem.rootLabel
  bodyRank : LabelRanks.rank body.stem.rootLabel (body.stem.done.length + 1) = value
  alphabet : Set ℕ
  subset : alphabet ⊆ H
  infinite : alphabet.Infinite
  graph : SimpleGraph G
  subgraph : graph ≤ B
  triangleFree : graph.CliqueFree 3
  command : RightBlue alphabet (GraphPayoff.payoff graph .inside) (.leaf left, .body body)
  size : ℕ
  leafRank : ℕ
  positive : 0 < leafRank
  bounded : leafRank ≤ size + 1
  bound : ℕ
  certificate : ∀ E : BodyResponses.Setup body.stem size,
    (∀ x ∈ BodyResponses.newWord E.position, x ∈ alphabet) →
    (∀ x ∈ BodyResponses.newWord E.position, bound < x) →
    RamseyGame.Outcome alphabet (GraphPayoff.game graph .inside
      (.leaf left, .leaf (applyBody body E))) true
  criticalBody : ∀ S T : Completed, GraphPayoff.payoff graph .inside S T = true →
    SkippedCuts.StateExtension (.leaf left) (.complete S) →
    SkippedCuts.StateExtension (.body body) (.complete T) →
    (CriticalPair.pair T.stem (lastLabel S).length).1 = body.stem.done.length
  color : ∀ S T : Completed, GraphPayoff.payoff graph .inside S T = true →
    min (CriticalPair.leafRank T.stem (lastLabel S).length) (size + 1) = leafRank
  exactRank : ∀ S T : Completed, GraphPayoff.payoff graph .inside S T = true →
    1 < S.stem.rootLabel.length →
    (T.stem.bodyLabels.getD (CriticalPair.pair T.stem (lastLabel S).length).1 []).length =
      size + 1 →
    CriticalPair.leafRank T.stem (lastLabel S).length = leafRank ∧
      (last T.stem (lastLabel S).length = true ↔ leafRank = size + 1)

theorem at_root {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T)
    (P : Pending) (hP : ExactSlots.Exact (.leaf P)) (hPlen : 1 < P.position.stem.rootLabel.length)
    (k value : ℕ) (hv : 0 < value) (hvle : value ≤ k + 1)
    (hcolor : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      1 < S.stem.rootLabel.length → T.stem.rootLabel.length = k + 1 →
      CriticalPair.bodyRank T.stem (lastLabel S).length = value)
    (A : RootResponses.Setup k)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .body (ofRoot A))) true)
    (d : ℕ) : Nonempty (Prepared H B P A value d) := by
  obtain ⟨Q, D, hQ, hD, hr, hb, hc, hf, hQr, hDr, hrank, hcritical⟩ :=
    StrictBodyCheckpoint.right hH B hall P hP hPlen k value hv hvle hcolor A hblue d
  obtain ⟨l, K, hKH, hK, C, hCB, hC, hcC, s, hs, hsl, b, hcert, htest, hexact⟩ :=
    StrictLeafLocalization.exists_body hH B hB hall Q (hQr ▸ hPlen) D hc hcritical
  exact ⟨{
    left := Q, body := D, leftExact := hQ, bodyExact := hD, run := hr, blue := hb, fresh := hf
    leftRoot := hQr, bodyRoot := hDr, bodyRank := hrank
    alphabet := K, subset := hKH, infinite := hK, graph := C, subgraph := hCB, triangleFree := hC
    command := hcC, size := l, leafRank := s, positive := hs, bounded := hsl, bound := b
    certificate := hcert
    criticalBody := fun S T hp ↦ hcritical S T
      (LastMarkerRefinement.payoff_true_mono hCB .inside S T hp)
    color := htest, exactRank := hexact }⟩

end Erdos118.StrictLocalization
