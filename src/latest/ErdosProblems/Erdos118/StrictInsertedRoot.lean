import ErdosProblems.Erdos118.StrictInitialOpening
import ErdosProblems.Erdos118.RootBufferOn

/-! Insert the third game's left prefix above the saved old bound and
localize its right-root request without choosing the root label. -/

namespace Erdos118.StrictInsertedRoot

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays InsideCounts LastBodyRefinement CriticalPair
open ManagedRelays (Initial)

structure Opening (H K : Set ℕ) (B : SimpleGraph G) (I : Initial H B .inside)
    (P : Pending) (Z : RootBuffer.Reserve H I.bound I.size P.position.stem) (d : ℕ) where
  left : Pending
  exactSlots : ExactSlots.Exact (.leaf left)
  root : left.position.stem.root = P.position.stem.root
  rootLabel : left.position.stem.rootLabel = Z.label
  extension : ∃ w : List ℕ, left.position.ordinary = P.position.ordinary ++ w ∧
    ∀ x ∈ w, x ∈ K ∧ d < x
  blue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf left, .initial)) true
  handoff : RightBlue H (GraphPayoff.payoff B .inside) (.leaf left, .initial)
  alphabet : Set ℕ
  subset : alphabet ⊆ K
  infinite : alphabet.Infinite
  graph : SimpleGraph G
  subgraph : graph ≤ B
  triangleFree : graph.CliqueFree 3
  command : RightBlue alphabet (GraphPayoff.payoff graph .inside) (.leaf left, .initial)
  size : ℕ
  rank : ℕ
  positive : 0 < rank
  bounded : rank < size + 1
  bound : ℕ
  certificate : ∀ A : RootResponses.Setup size,
    (∀ x ∈ A.stem.decorated, x ∈ alphabet) → (∀ x ∈ A.stem.decorated, bound < x) →
    RamseyGame.Outcome alphabet (GraphPayoff.game graph .inside (.leaf left, .body (ofRoot A))) true
  exactRank : ∀ S T : Completed, GraphPayoff.payoff graph .inside S T = true →
    1 < S.stem.rootLabel.length → T.stem.rootLabel.length = size + 1 →
    bodyRank T.stem (lastLabel S).length = rank ∧
      (last T.stem (lastLabel S).length = true → rank + 1 < size + 1)

theorem exists_opening {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T)
    (I : Initial H B .inside) (hk : 0 < I.size) (P : Pending) (c : ℕ)
    (hPR : P.roots = [c]) (hP : ExactSlots.Exact (.leaf P))
    (Z : RootBuffer.Reserve H I.bound I.size P.position.stem)
    (hOrd : ∀ x ∈ P.position.ordinary, x ∈ H ∧ I.bound < x) (d : ℕ) :
    Nonempty (Opening H K B I P Z d) := by
  obtain ⟨A, w, hAord, hAroot, hAlabel, hw, hAfresh⟩ :=
    RootBufferOn.buffer hK hKH P Z hP hPR hOrd d
  let D := ofRoot A
  have hD : ExactSlots.Exact (.body D) :=
    ExactSlots.step_exact (DecisionStates.Step.root A) trivial
  have hbD := I.rootBlue A (fun x hx ↦ (hAfresh x hx).1) (fun x hx ↦ (hAfresh x hx).2)
  have hcD : LeftBlue H (GraphPayoff.payoff B .inside) (.body D, .initial) := by
    rcases blue_command (GraphPayoff.payoff B .inside) (.body D, .initial) rfl hbD with hl | hr
    · exact hl
    · obtain ⟨n, R, hs, _⟩ := hr
      simp [allowedSide] at hs
  obtain ⟨m, E, _, hbE, hhE, hE⟩ := respond_body_on hK hKH B .inside false D .initial hcD d
  let S := applyBody D E
  have hS := ExactSlots.step_exact (DecisionStates.Step.body D E) hD
  have hSroot : S.position.stem.root = P.position.stem.root := by
    change E.position.stem.root = _
    rw [E.stem_eq]
    exact hAroot
  have hSlabel : S.position.stem.rootLabel = Z.label := by
    change E.position.stem.rootLabel = _
    rw [E.stem_eq]
    exact hAlabel
  have hSlen : 1 < S.position.stem.rootLabel.length := by
    rw [hSlabel, Z.card]
    omega
  have hfS : ∃ z : List ℕ, S.position.ordinary = P.position.ordinary ++ z ∧
      ∀ x ∈ z, x ∈ K ∧ d < x := by
    refine ⟨w ++ E.position.size :: E.position.entries, ?_, ?_⟩
    · change E.position.ordinary = _
      rw [BodyResponses.setup_ordinary]
      change A.stem.ordinary ++ E.position.size :: E.position.entries = _
      rw [hAord, List.append_assoc]
    · intro x hx
      exact (List.mem_append.mp hx).elim (hw x)
        (fun hx ↦ ⟨(hE x (List.mem_append_right _ hx)).1,
          (hE x (List.mem_append_right _ hx)).2⟩)
  have hcK : RightBlue K (GraphPayoff.payoff B .inside) (.leaf S, .initial) := by
    obtain ⟨n, R, hs, hR, b, hc⟩ := hhE
    exact ⟨n, R, hs, hR, b, fun a ha hlarge ↦
      (hc a (ha.trans hKH) hlarge).almost_mono (RamseyGame.almostSubset_of_subset hKH)⟩
  obtain ⟨l, J, hJK, hJ, C, hCB, hC, hcC, v, hv, hvl, b, hcert, _, hexact⟩ :=
    StrictBodyLocalization.exists_root hK B hB
      (hinit.almost_mono (RamseyGame.almostSubset_of_subset hKH)) hall S hSlen hcK
  exact ⟨{
    left := S, exactSlots := hS, root := hSroot, rootLabel := hSlabel, extension := hfS
    blue := hbE, handoff := hhE, alphabet := J, subset := hJK, infinite := hJ
    graph := C, subgraph := hCB, triangleFree := hC, command := hcC, size := l, rank := v
    positive := hv, bounded := hvl, bound := b, certificate := hcert, exactRank := hexact }⟩

end Erdos118.StrictInsertedRoot
