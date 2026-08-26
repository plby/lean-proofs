import ErdosProblems.Erdos118.EndpointOrder
import ErdosProblems.Erdos118.ReservedResponses
import ErdosProblems.Erdos118.WholeBlue

/-!
An initial blue certificate and a whole-second branch give a triangle by
using one common completion of the pending first word against a far blue
pair. The remaining blue branches have positive root labels on both words.
-/

namespace Erdos118.SecondWhole

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses

theorem finish_selector (P : Pending) (hR : P.roots = []) (hL : P.leaves = []) (b n : ℕ) :
    responseFor (.leaf P) b n = some (finishResponse P hR hL b) := by
  dsimp only [responseFor]
  split
  · rename_i j rest he
    have hbad : ([] : List ℕ) = j :: rest := hL.symm.trans he
    cases hbad
  · split
    · rename_i j rest he
      have hbad : ([] : List ℕ) = j :: rest := hR.symm.trans he
      cases hbad
    · rfl

theorem completion_edges {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (P : Pending) (T : Completed)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf P, .complete T)) true) :
    ∃ b : ℕ, ∀ A : StemResponses.Setup P.position P.position.stem.root,
      (∀ x ∈ A.newWord, x ∈ H) → (∀ x ∈ A.newWord, b < x) →
      B.Adj (GraphPayoff.vertex (ofCompletion P A)) (GraphPayoff.vertex T) := by
  obtain ⟨hR, hL⟩ := EndpointOrder.leaf_complete_slots_empty hH B o P T hblue
  rcases blue_command (GraphPayoff.payoff B o) (.leaf P, .complete T) rfl hblue with hl | hr
  · obtain ⟨n, R, _, hresp, b, hb⟩ := hl
    let c := pairBound (.leaf P, .complete T)
    have he : R = finishResponse P hR hL c :=
      Option.some.inj (hresp.symm.trans (finish_selector P hR hL c n))
    subst R
    refine ⟨max b c, ?_⟩
    intro A hAH hAlarge
    have hAc : ∀ x ∈ A.newWord, c < x :=
      fun x hx ↦ (le_max_right _ _).trans_lt (hAlarge x hx)
    let a := finishMember P hR hL c A hAc
    have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ hAH x (List.mem_toFinset.mp hx)
    have hab : ∀ x ∈ a.1, b < x := fun x hx ↦
      (le_max_left _ _).trans_lt (hAlarge x (List.mem_toFinset.mp hx))
    have hnext := hb a haH hab
    change RamseyGame.Outcome H (GraphPayoff.game B o
      ((finishResponse P hR hL c).result (finishMember P hR hL c A hAc), .complete T)) true at hnext
    rw [finishMember_result, GraphPayoff.game, AdaptiveGame.game_complete] at hnext
    exact ((GraphPayoff.payoff_true_iff B o (ofCompletion P A) T).mp
      (RamseyGame.outcome_leaf_iff.mp hnext)).2.2.2
  · exact (not_rightBlue_complete H (GraphPayoff.payoff B o) (.leaf P) T hr).elim

theorem blue_pair_above {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.initial, .initial)) true) (b : ℕ) :
    ∃ s t : G, B.Adj s t ∧ (∀ x ∈ word s.1, x ∈ H ∧ b < x) ∧
      ∀ x ∈ word t.1, x ∈ H ∧ b < x := by
  let K := H \ Set.Iic b
  have hK : K.Infinite := hH.sdiff (Set.finite_Iic b)
  have hKH : K ⊆ H := fun _ hx ↦ hx.1
  have hblueK := hblue.almost_mono (RamseyGame.almostSubset_of_subset hKH)
  obtain ⟨S, T, hrun, hpay⟩ := blue_completion hK (GraphPayoff.payoff B o)
    (.initial, .initial) hblueK
  have hsupport := EndpointOrder.run_supported hrun
    (by simp [State.decorated])
  refine ⟨GraphPayoff.vertex S, GraphPayoff.vertex T,
    ((GraphPayoff.payoff_true_iff B o S T).mp hpay).2.2.2, ?_, ?_⟩
  · intro x hx
    rw [GraphPayoff.vertex, Stem.toGood_word] at hx
    have hmem := hsupport.1 x (S.stem.ordinary_sublist.subset hx)
    exact ⟨hmem.1, Nat.lt_of_not_ge hmem.2⟩
  · intro x hx
    rw [GraphPayoff.vertex, Stem.toGood_word] at hx
    have hmem := hsupport.2 x (T.stem.ordinary_sublist.subset hx)
    exact ⟨hmem.1, Nat.lt_of_not_ge hmem.2⟩

def WholeSecondBlue (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (P : Pending) : Prop :=
  ∃ b : ℕ, ∀ a : (wholeResponse (pairBound (.leaf P, .initial))).family.members,
    (↑a.1 : Set ℕ) ⊆ H → (∀ x ∈ a.1, b < x) →
    RamseyGame.Outcome H (GraphPayoff.game B o
      (.leaf P, (wholeResponse (pairBound (.leaf P, .initial))).result a)) true

theorem whole_second_triangle {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.initial, .initial)) true)
    (P : Pending) (hsecond : WholeSecondBlue H B o P) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  obtain ⟨b, hb⟩ := hsecond
  let c := pairBound (.leaf P, .initial)
  obtain ⟨t, u, htu, ht, hu⟩ := blue_pair_above hH B o hblue (max b c)
  have insert_whole : ∀ v : G, (∀ x ∈ word v.1, x ∈ H ∧ max b c < x) →
      RamseyGame.Outcome H (GraphPayoff.game B o (.leaf P, .complete (ofGood v))) true := by
    intro v hv
    let s := WordResponses.supportEquiv v
    have hsc : ∀ x ∈ s.1, c < x := fun x hx ↦
      (le_max_right _ _).trans_lt (hv x (List.mem_toFinset.mp hx)).2
    let a := WholeBlue.wholeMember c s hsc
    have haH : (↑a.1 : Set ℕ) ⊆ H := fun x hx ↦ (hv x (List.mem_toFinset.mp hx)).1
    have hab : ∀ x ∈ a.1, b < x := fun x hx ↦
      (le_max_left _ _).trans_lt (hv x (List.mem_toFinset.mp hx)).2
    have hnext := hb a haH hab
    change RamseyGame.Outcome H (GraphPayoff.game B o
      (.leaf P, (wholeResponse c).result (WholeBlue.wholeMember c s hsc))) true at hnext
    rw [WholeBlue.wholeMember_result c s hsc] at hnext
    simpa only [s, Equiv.symm_apply_apply] using hnext
  obtain ⟨bt, hbt⟩ := completion_edges hH B o P (ofGood t) (insert_whole t ht)
  obtain ⟨bu, hbu⟩ := completion_edges hH B o P (ofGood u) (insert_whole u hu)
  have hroom : P.position.stem.done.length < P.position.stem.root := by
    have h := P.position.room
    omega
  obtain ⟨A, hA⟩ := StemResponses.setup_above P.position P.position.stem.root hroom le_rfl
    hH (max bt bu)
  have hAH : ∀ x ∈ A.newWord, x ∈ H := fun x hx ↦ (hA x hx).1
  have hst := hbt A hAH (fun x hx ↦ (le_max_left _ _).trans_lt (hA x hx).2)
  have hsu := hbu A hAH (fun x hx ↦ (le_max_right _ _).trans_lt (hA x hx).2)
  exact ⟨GraphPayoff.vertex (ofCompletion P A), t, u,
    by simpa only [WholeBlue.plain_vertex] using hst,
    by simpa only [WholeBlue.plain_vertex] using hsu, htu⟩

theorem second_root_blue {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3) (o : GraphPayoff.Orientation)
    (hblue : RamseyGame.Outcome H (GraphPayoff.game B o (.initial, .initial)) true)
    (P : Pending) (hright : RightBlue H (GraphPayoff.payoff B o) (.leaf P, .initial)) :
    ∃ k b : ℕ, ∀ a : (rootResponse k (pairBound (.leaf P, .initial))).family.members,
      (↑a.1 : Set ℕ) ⊆ H → (∀ x ∈ a.1, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B o
        (.leaf P, (rootResponse k (pairBound (.leaf P, .initial))).result a)) true := by
  obtain ⟨n, R, _, hR, b, hb⟩ := hright
  cases n with
  | zero =>
    have he : R = wholeResponse (pairBound (.leaf P, .initial)) := Option.some.inj hR.symm
    subst R
    obtain ⟨s, t, u, hst, hsu, htu⟩ := whole_second_triangle hH B o hblue P ⟨b, hb⟩
    exact (hB {s, t, u} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hst, hsu, htu⟩)).elim
  | succ k =>
    have he : R = rootResponse k (pairBound (.leaf P, .initial)) := Option.some.inj hR.symm
    subst R
    exact ⟨k, b, hb⟩

end Erdos118.SecondWhole
