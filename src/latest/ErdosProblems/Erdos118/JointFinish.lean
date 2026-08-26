import ErdosProblems.Erdos118.JointMoves

/-!
Finish a common rightmost vertex first, then complete the remaining blue
pair above both neighborhood bounds. This does not require the remaining
two shared words to have identical unused lists or be at last leaves.
-/

namespace Erdos118.JointFinish

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns

theorem triangle_of_completed_right {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (S₀ S₁ T₀ T₁ : Pending) (U₀ U₁ : Completed)
    (hS : S₀.position.ordinary = S₁.position.ordinary)
    (hT : T₀.position.ordinary = T₁.position.ordinary)
    (hU : GraphPayoff.vertex U₀ = GraphPayoff.vertex U₁)
    (hST : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf S₀, .leaf T₀)) true)
    (hSU : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf S₁, .complete U₀)) true)
    (hTU : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf T₁, .complete U₁)) true) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  obtain ⟨bS, hbS⟩ := CompletionReplay.completion_edges_of_word hH B o S₁ U₀ hSU
  obtain ⟨bT, hbT⟩ := CompletionReplay.completion_edges_of_word hH B o T₁ U₁ hTU
  let K := H \ Set.Iic (max bS bT)
  have hK : K.Infinite := hH.sdiff (Set.finite_Iic (max bS bT))
  have hKH : K ⊆ H := fun _ hx ↦ hx.1
  have hbK := hST.almost_mono (RamseyGame.almostSubset_of_subset hKH)
  obtain ⟨S, T, hrun, hpay⟩ := blue_completion hK (GraphPayoff.payoff B o) (.leaf S₀, .leaf T₀) hbK
  obtain ⟨vS, vT, hSw, hTw, hvS, hvT⟩ := CompletionReplay.run_supported_suffixes hrun
  have hSword : word (GraphPayoff.vertex S).1 = S₁.position.ordinary ++ vS := by
    rw [GraphPayoff.vertex, Stem.toGood_word]
    change S.stem.ordinary = S₀.position.ordinary ++ vS at hSw
    rwa [hS] at hSw
  have hTword : word (GraphPayoff.vertex T).1 = T₁.position.ordinary ++ vT := by
    rw [GraphPayoff.vertex, Stem.toGood_word]
    change T.stem.ordinary = T₀.position.ordinary ++ vT at hTw
    rwa [hT] at hTw
  have hsu := hbS (GraphPayoff.vertex S) vS hSword (fun x hx ↦ hKH (hvS x hx))
    (fun x hx ↦ (le_max_left _ _).trans_lt (Nat.lt_of_not_ge (hvS x hx).2))
  have htu := hbT (GraphPayoff.vertex T) vT hTword (fun x hx ↦ hKH (hvT x hx))
    (fun x hx ↦ (le_max_right _ _).trans_lt (Nat.lt_of_not_ge (hvT x hx).2))
  rw [← hU] at htu
  exact ⟨GraphPayoff.vertex S, GraphPayoff.vertex T, GraphPayoff.vertex U₀,
    ((GraphPayoff.payoff_true_iff B o S T).mp hpay).2.2.2, hsu, htu⟩

theorem triangle_of_last_right {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (S₀ S₁ T₀ T₁ U₀ U₁ : Pending)
    (hS : S₀.position.ordinary = S₁.position.ordinary)
    (hT : T₀.position.ordinary = T₁.position.ordinary)
    (hU : U₀.position.ordinary = U₁.position.ordinary)
    (hU₀ : U₀.roots = [] ∧ U₀.leaves = []) (hU₁ : U₁.roots = [] ∧ U₁.leaves = [])
    (hST : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf S₀, .leaf T₀)) true)
    (hSU : RightBlue H (GraphPayoff.payoff B o) (.leaf S₁, .leaf U₀))
    (hTU : RightBlue H (GraphPayoff.payoff B o) (.leaf T₁, .leaf U₁)) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  obtain ⟨b₀, hb₀⟩ := CompletionReplay.right_finish_words (GraphPayoff.payoff B o)
    (.leaf S₁) U₀ hU₀.1 hU₀.2 hSU
  obtain ⟨b₁, hb₁⟩ := CompletionReplay.right_finish_words (GraphPayoff.payoff B o)
    (.leaf T₁) U₁ hU₁.1 hU₁.2 hTU
  have hroom : U₀.position.stem.done.length < U₀.position.stem.root := by
    have hr := U₀.position.room
    omega
  obtain ⟨A, hA⟩ := StemResponses.setup_above U₀.position U₀.position.stem.root hroom le_rfl
    hH (max b₀ b₁)
  let u := StemResponses.completed A
  have hu₀ : word u.1 = U₀.position.ordinary ++ A.newWord := StemResponses.completed_word A
  have hu₁ : word u.1 = U₁.position.ordinary ++ A.newWord := by rwa [hU] at hu₀
  obtain ⟨C₀, hC₀, hblue₀⟩ := hb₀ u A.newWord hu₀ (fun x hx ↦ (hA x hx).1)
    (fun x hx ↦ (le_max_left _ _).trans_lt (hA x hx).2)
  obtain ⟨C₁, hC₁, hblue₁⟩ := hb₁ u A.newWord hu₁ (fun x hx ↦ (hA x hx).1)
    (fun x hx ↦ (le_max_right _ _).trans_lt (hA x hx).2)
  exact triangle_of_completed_right hH B o S₀ S₁ T₀ T₁ C₀ C₁ hS hT
    (hC₀.trans hC₁.symm) hST hblue₀ hblue₁

end Erdos118.JointFinish
