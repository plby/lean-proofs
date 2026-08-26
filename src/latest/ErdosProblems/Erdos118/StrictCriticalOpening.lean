import ErdosProblems.Erdos118.StrictLocalization
import ErdosProblems.Erdos118.StrictLeafCheckpoint

/-! Submit a caller's localized body response and reach the actual strict
critical pair, preserving its label and the later graph's literal run. -/

namespace Erdos118.StrictCriticalOpening

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns InsideCounts LastBodyRefinement CriticalPair ReservedResponses

theorem at_body {H : Set ℕ} {B : SimpleGraph G} {P : Pending} {k value d₀ : ℕ}
    {A : RootResponses.Setup k} (Z : StrictLocalization.Prepared H B P A value d₀)
    (hPlen : 1 < P.position.stem.rootLabel.length)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S < beforeLast T)
    (E : BodyResponses.Setup Z.body.stem Z.size) (d : ℕ)
    (hEK : ∀ x ∈ BodyResponses.newWord E.position, x ∈ Z.alphabet)
    (hEb : ∀ x ∈ BodyResponses.newWord E.position, Z.bound < x)
    (hEc : ∀ x ∈ BodyResponses.newWord E.position,
      pairBound (.leaf Z.left, .body Z.body) < x)
    (hEg : ∀ x ∈ BodyResponses.newWord E.position,
      PreparedRelays.guard Z.alphabet Z.graph .inside true Z.body (.leaf Z.left) Z.size < x)
    (hEd : ∀ x ∈ BodyResponses.newWord E.position, d < x) :
    ∃ j : ℕ, j ∈ E.position.label ∧ LabelRanks.rank E.position.label j = Z.leafRank ∧
      ∃ W : StrictLeafCheckpoint.Reached Z.alphabet Z.alphabet Z.graph
          Z.left (applyBody Z.body E) j d,
        ConservativeRuns.Run Z.alphabet (GraphPayoff.payoff Z.graph .inside)
          (.leaf Z.left, .body Z.body) (.leaf W.left, .leaf W.right) ∧
        FreshCheckpoints.FreshExtension Z.alphabet d
          (.leaf Z.left, .body Z.body) (.leaf W.left, .leaf W.right) ∧
        (W.right.leaves = [] ↔ Z.leafRank = Z.size + 1) := by
  let Q := applyBody Z.body E
  have hstrict : ∀ S T, GraphPayoff.payoff Z.graph .inside S T = true →
      beforeLast S < beforeLast T :=
    fun S T hp ↦ hall S T (LastMarkerRefinement.payoff_true_mono Z.subgraph .inside S T hp)
  have hb := Z.certificate E hEK hEb
  have hh := PreparedRelays.body_handoff Z.infinite Z.graph .inside true Z.body
    (.leaf Z.left) E hEc hb
  have hs := PreparedRelays.body_step Z.graph .inside true Z.body (.leaf Z.left) E
    (PreparedRelays.command_allowed Z.graph .inside true Z.body (.leaf Z.left) Z.command)
    hEK hEc hEg
  have hQ := ExactSlots.step_exact (DecisionStates.Step.body Z.body E) Z.bodyExact
  have heD := SkippedCuts.stateExtension_of_step (DecisionStates.Step.body Z.body E)
  have hbefore : ∀ x ∈ Z.left.position.decorated, x < Q.position.ordinary.getLastD 0 := by
    let c := pairBound (.leaf Z.left, .body Z.body)
    let R := bodyResponse Z.body Z.size c
    let a := bodyMember Z.body c E hEc
    have he : R.result a = .leaf Q := bodyMember_result Z.body c E hEc
    obtain ⟨v, hv, hvne, hvlarge⟩ := SkippedCuts.response_ordinary_suffix R a
    rw [he] at hv
    have hm : Q.position.ordinary.getLastD 0 ∈ v := by
      change (State.leaf Q).ordinary.getLastD 0 ∈ v
      rw [hv, List.getLastD_eq_getLast?, List.getLast?_append_of_ne_nil _ hvne,
        List.getLast?_eq_some_getLast hvne]
      exact List.getLast_mem hvne
    intro x hx
    exact (pairBound_left (.leaf Z.left, .body Z.body) hx).trans_lt (hvlarge _ hm)
  obtain ⟨j, hj, hjrank⟩ := LabelRanks.exists_label E.position.label E.position.label_pairwise.nodup
    Z.leafRank Z.positive (E.label_length ▸ Z.bounded)
  have hij : Q.position.entries.length ≤ j := by
    change E.position.entries.length ≤ j
    rw [E.entries_length]
    have h := (E.position.label_pairwise.imp Nat.le_of_lt).rel_head hj
    cases he : E.position.label with
    | nil => simp [he] at hj
    | cons a rest => simpa only [he, List.head_cons, List.headD_cons] using h
  have hbody : ∀ S T : Completed, GraphPayoff.payoff Z.graph .inside S T = true →
      SkippedCuts.StateExtension (.leaf Z.left) (.complete S) →
      SkippedCuts.StateExtension (.leaf Q) (.complete T) →
      (CriticalPair.pair T.stem (lastLabel S).length).1 = Q.position.stem.done.length := by
    intro S T hp heS heT
    change _ = E.position.stem.done.length
    rw [E.stem_eq]
    exact Z.criticalBody S T hp heS (heD.trans heT)
  have hcolor : ∀ S T : Completed, GraphPayoff.payoff Z.graph .inside S T = true →
      SkippedCuts.StateExtension (.leaf Z.left) (.complete S) →
      SkippedCuts.StateExtension (.leaf Q) (.complete T) →
      leafRank T.stem (lastLabel S).length = Z.leafRank := by
    intro S T hp heS heT
    have hSroot : S.stem.rootLabel = P.position.stem.rootLabel :=
      (Option.some.inj (heS.labels.root _ rfl)).trans Z.leftRoot
    have hindex := hbody S T hp heS heT
    have hlabel := CriticalCursor.current_label Q T heT
    have hcard : (T.stem.bodyLabels.getD
        (CriticalPair.pair T.stem (lastLabel S).length).1 []).length = Z.size + 1 := by
      rw [hindex, hlabel]
      exact E.label_length
    exact (Z.exactRank S T hp (hSroot ▸ hPlen) hcard).1
  obtain ⟨W⟩ := StrictLeafCheckpoint.right Z.infinite Set.Subset.rfl Z.graph hstrict
    Z.left Q Z.leftExact hQ (Z.leftRoot ▸ hPlen) j Z.leafRank d hj hij hjrank hb hh
    hbefore hbody hcolor
  have hrun : ConservativeRuns.Run Z.alphabet (GraphPayoff.payoff Z.graph .inside)
      (.leaf Z.left, .body Z.body) (.leaf W.left, .leaf W.right) :=
    Relation.ReflTransGen.head hs W.run
  have hf₀ : FreshCheckpoints.FreshExtension Z.alphabet d
      (.leaf Z.left, .body Z.body) (.leaf Z.left, .leaf Q) := by
    refine ⟨[], E.position.size :: E.position.entries, by simp, BodyResponses.setup_ordinary E,
      by simp, ?_⟩
    intro x hx
    have hm : x ∈ BodyResponses.newWord E.position := List.mem_append_right _ hx
    exact ⟨hEK x hm, hEd x hm⟩
  have hlast : W.right.leaves = [] ↔ Z.leafRank = Z.size + 1 := by
    obtain ⟨S, T, hr, hp⟩ := blue_completion Z.infinite (GraphPayoff.payoff Z.graph .inside)
      (.leaf W.left, .leaf W.right) W.blue
    obtain ⟨heU, heV⟩ := SkippedCuts.run_extensions hr
    have heS := (SkippedCuts.run_extensions W.run).1.trans heU
    have hSroot : S.stem.rootLabel = P.position.stem.rootLabel :=
      (Option.some.inj (heS.labels.root _ rfl)).trans Z.leftRoot
    have hSL : 1 < S.stem.rootLabel.length := hSroot ▸ hPlen
    obtain ⟨_, hspec, _, _, _, _⟩ := StrictCriticalBounds.terminal Z.graph S T hp hSL
      (hstrict S T hp)
    have hepair := W.criticalPair S T hp heU heV
    rw [hepair] at hspec
    have hcount : (LeafSuffixCounts.remaining T.stem W.right.position.stem.done.length
        W.right.position.entries.length).card = (lastLabel S).length := hspec.2
    have hobs := (CriticalCursor.observables W.right T W.rightExact heV _ hcount).2.2
    have hcard : (T.stem.bodyLabels.getD
        (CriticalPair.pair T.stem (lastLabel S).length).1 []).length = Z.size + 1 := by
      rw [hepair, CriticalCursor.current_label W.right T heV, W.sameBody.label]
      exact E.label_length
    exact hobs.symm.trans (Z.exactRank S T hp hSL hcard).2
  exact ⟨j, hj, hjrank, W, hrun, FreshCheckpoints.fresh_trans hf₀ W.fresh, hlast⟩

end Erdos118.StrictCriticalOpening
