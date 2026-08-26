import ErdosProblems.Erdos118.InsideEndgame

/-!
Complete the right two words together, then one common left word. The
initial two blue pairs have last pending words and the third pair has
matching ordinary prefixes. All final bounds precede their new suffixes.
-/

namespace Erdos118.InsideCompletion

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns

theorem triangle {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (S₀ S₁ T₀ U₀ T₁ U₁ : Pending)
    (hS₀ : S₀.roots = [] ∧ S₀.leaves = []) (hS₁ : S₁.roots = [] ∧ S₁.leaves = [])
    (hT : T₀.roots = [] ∧ T₀.leaves = []) (hU : U₀.roots = [] ∧ U₀.leaves = [])
    (hSord : S₀.position.ordinary = S₁.position.ordinary)
    (hTord : T₁.position.ordinary = T₀.position.ordinary)
    (hUord : U₁.position.ordinary = U₀.position.ordinary)
    (hST : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf S₀, .leaf T₀)) true)
    (hSU : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf S₁, .leaf U₀)) true)
    (hTU : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf T₁, .leaf U₁)) true) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  let payoff := GraphPayoff.payoff B .inside
  have hcT := InsideEndgame.last_left_rightBlue hH B S₀ T₀ hS₀.1 hS₀.2 hST
  have hcU := InsideEndgame.last_left_rightBlue hH B S₁ U₀ hS₁.1 hS₁.2 hSU
  obtain ⟨bT, hbT⟩ := CompletionReplay.right_finish_words payoff (.leaf S₀) T₀ hT.1 hT.2 hcT
  obtain ⟨bU, hbU⟩ := CompletionReplay.right_finish_words payoff (.leaf S₁) U₀ hU.1 hU.2 hcU
  let J := H \ Set.Iic (max bT bU)
  have hJ : J.Infinite := hH.sdiff (Set.finite_Iic (max bT bU))
  have hJH : J ⊆ H := fun _ hx ↦ hx.1
  have hblueJ := hTU.almost_mono (RamseyGame.almostSubset_of_subset hJH)
  obtain ⟨T, U, hrun, hpay⟩ := blue_completion hJ payoff (.leaf T₁, .leaf U₁) hblueJ
  obtain ⟨vT, vU, hTw, hUw, hvT, hvU⟩ := CompletionReplay.run_supported_suffixes hrun
  have ht : word (GraphPayoff.vertex T).1 = T₀.position.ordinary ++ vT := by
    rw [GraphPayoff.vertex, Stem.toGood_word]
    change T.stem.ordinary = T₁.position.ordinary ++ vT at hTw
    rwa [hTord] at hTw
  have hu : word (GraphPayoff.vertex U).1 = U₀.position.ordinary ++ vU := by
    rw [GraphPayoff.vertex, Stem.toGood_word]
    change U.stem.ordinary = U₁.position.ordinary ++ vU at hUw
    rwa [hUord] at hUw
  obtain ⟨T', hT', hblueT⟩ := hbT (GraphPayoff.vertex T) vT ht
    (fun x hx ↦ hJH (hvT x hx))
    (fun x hx ↦ (le_max_left _ _).trans_lt (Nat.lt_of_not_ge (hvT x hx).2))
  obtain ⟨U', hU', hblueU⟩ := hbU (GraphPayoff.vertex U) vU hu
    (fun x hx ↦ hJH (hvU x hx))
    (fun x hx ↦ (le_max_right _ _).trans_lt (Nat.lt_of_not_ge (hvU x hx).2))
  obtain ⟨b₀, hb₀⟩ := CompletionReplay.completion_edges_of_word hH B .inside S₀ T' hblueT
  obtain ⟨b₁, hb₁⟩ := CompletionReplay.completion_edges_of_word hH B .inside S₁ U' hblueU
  have hroom : S₀.position.stem.done.length < S₀.position.stem.root := by
    have h := S₀.position.room
    omega
  obtain ⟨A, hA⟩ := StemResponses.setup_above S₀.position S₀.position.stem.root hroom le_rfl
    hH (max b₀ b₁)
  let s := GraphPayoff.vertex (ofCompletion S₀ A)
  have hs₀ : word s.1 = S₀.position.ordinary ++ A.newWord := by
    change word ((ofCompletion S₀ A).stem.toGood (ofCompletion S₀ A).full).1 = _
    rw [Stem.toGood_word]
    exact A.ordinary
  have hs₁ : word s.1 = S₁.position.ordinary ++ A.newWord := hs₀.trans (by rw [hSord])
  have hst := hb₀ s A.newWord hs₀ (fun x hx ↦ (hA x hx).1)
    (fun x hx ↦ (le_max_left _ _).trans_lt (hA x hx).2)
  have hsu := hb₁ s A.newWord hs₁ (fun x hx ↦ (hA x hx).1)
    (fun x hx ↦ (le_max_right _ _).trans_lt (hA x hx).2)
  rw [hT'] at hst
  rw [hU'] at hsu
  exact ⟨s, GraphPayoff.vertex T, GraphPayoff.vertex U, hst, hsu,
    ((GraphPayoff.payoff_true_iff B .inside T U).mp hpay).2.2.2⟩

end Erdos118.InsideCompletion
