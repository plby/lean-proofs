import ErdosProblems.Erdos118.SingletonMiddleRequest
import ErdosProblems.Erdos118.InsideRightCompletion

/-! The old singleton next-body request is fired after the two source
completion bounds. Only the extra suffix beyond the final source word
must satisfy those later bounds. -/

namespace Erdos118.SingletonMiddleCompletion

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays BoundaryRelays

theorem extension {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    {O : LateOpening.Opening H B} (D : FirstMiddle.Diagram O)
    (R : SingletonMiddleRequest.Request D) (L : SecondMiddle.LastPair D R.bound) (d : ℕ) :
    ∃ E : BodyDecision, ∃ w : List ℕ,
      E.stem.ordinary = L.right.position.ordinary ++ w ∧
      (∀ x ∈ w, x ∈ H ∧ d < x) ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
        (.leaf D.replay.target, .leaf O.second.target) (.leaf D.replay.target, .body E) ∧
      RamseyGame.Outcome H
        (GraphPayoff.game B .inside (.leaf D.replay.target, .body E)) true := by
  obtain ⟨hs, hm, he⟩ := NextSelectedLeaf.ordinary_parts
    O.insertedRight.position O.second.target.position O.second.ordinary
      (congrArg List.length O.second.entries)
  have hstem : L.right.position.stem.ordinary = O.second.target.position.stem.ordinary := by
    rw [L.rightBody.2.1]
    exact hs.symm
  have hmarker : L.right.position.size = O.second.target.position.size :=
    L.rightBody.2.2.1.trans hm.symm
  have hentries : L.right.position.entries = O.second.target.position.entries ++ L.suffix := by
    have hw := L.ordinary
    simp only [Position.ordinary, L.rightBody.2.1, L.rightBody.2.2.1, List.append_assoc] at hw
    have ht := List.append_cancel_left hw
    have ht' : O.insertedRight.position.size :: L.right.position.entries =
        O.insertedRight.position.size :: (O.insertedRight.position.entries ++ L.suffix) := by
      simpa only [List.cons_append] using ht
    rw [he]
    exact (List.cons.inj ht').2
  have hlast : L.right.position.entries.length = O.insertedRight.position.label.getLastD 0 := by
    rw [← ExactSlots.pending_last_leaf L.right L.rightExact L.rightLast.2,
      L.rightBody.2.2.2.1]
  have hmore : O.second.target.position.entries.length < L.right.position.entries.length := by
    rw [O.second.entries, hlast]
    exact DeferredBodyReplay.current_lt_last O.insertedRight O.insertedRightNonlast
  have hless : L.right.position.entries.length < O.second.target.position.size :=
    L.right.position.unfinished.trans_eq hmarker
  obtain ⟨A, _, hAQ⟩ := LeafReplay.setup_of_position O.second.target.position
    L.right.position L.right.position.entries.length hstem hmarker rfl L.suffix hentries
  let Q := LeafResponses.position A hmore hless
  have hQord : Q.ordinary = L.right.position.ordinary :=
    (LeafResponses.position_ordinary A hmore hless).trans hAQ
  have hbounds := next_body_bounds O.second.target R.index R.rest R.roots
  obtain ⟨F, hf⟩ := StemResponses.setup_above Q (R.index - 1) hbounds.1 hbounds.2.1
    hH (max R.bound d)
  have hword : F.stem.ordinary = O.second.target.position.ordinary ++
      (L.suffix ++ F.newWord) := by
    rw [F.ordinary, hQord, L.ordinary, ← O.second.ordinary, List.append_assoc]
  have hwhole : ∀ x ∈ L.suffix ++ F.newWord, x ∈ H ∧ R.bound < x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact L.fresh x hx
    · exact ⟨(hf x hx).1, (le_max_left _ _).trans_lt (hf x hx).2⟩
  obtain ⟨A', _, hA', hs', hb'⟩ := R.certificate F.stem (L.suffix ++ F.newWord)
    F.root_eq F.count hword (fun x hx ↦ (hwhole x hx).1)
    (fun x hx ↦ (hwhole x hx).2)
  refine ⟨ofStem O.second.target R.index R.rest R.roots A', F.newWord, ?_,
    fun x hx ↦ ⟨(hf x hx).1, (le_max_right _ _).trans_lt (hf x hx).2⟩, hs', hb'⟩
  exact hA'.trans (F.ordinary.trans (by rw [hQord]))

theorem triangle {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    {O : LateOpening.Opening H B} (D : FirstMiddle.Diagram O)
    (R : SingletonMiddleRequest.Request D) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  obtain ⟨L⟩ := SecondMiddle.exists_last_pair hH B D R.bound
  apply InsideRightCompletion.triangle hH B L.oldLeft L.fineLeft D.right L.right
    D.replay.target L.oldLast L.fineLast ⟨D.rightRoot, D.rightLeaf⟩ L.rightLast
    L.sameOrdinary D.replay.ordinary L.oldBlue L.fineBlue
  intro d
  obtain ⟨E, w, hw, hf, _, hb⟩ := extension hH B D R L d
  exact ⟨.body E, w, hw, hf, hb⟩

end Erdos118.SingletonMiddleCompletion
