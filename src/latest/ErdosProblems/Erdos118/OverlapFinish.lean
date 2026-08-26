import ErdosProblems.Erdos118.JointFinish
import ErdosProblems.Erdos118.InsideEndgame

/-!
Announce the old U completion bound before a newer SU extension. One final
U suffix replays in both games, after which the common-right triangle applies.
-/

namespace Erdos118.OverlapFinish

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns

theorem right_extension_triangle {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (T U : Pending) (hU : U.roots = [] ∧ U.leaves = [])
    (hTU : RightBlue H (GraphPayoff.payoff B .inside) (.leaf T, .leaf U)) :
    ∃ b : ℕ, ∀ S₀ S₁ T₀ U₁ : Pending, ∀ v : List ℕ,
      S₁.roots = [] → S₁.leaves = [] →
      S₀.position.ordinary = S₁.position.ordinary → T₀.position.ordinary = T.position.ordinary →
      U₁.position.ordinary = U.position.ordinary ++ v →
      (∀ x ∈ v, x ∈ H ∧ b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf S₀, .leaf T₀)) true →
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf S₁, .leaf U₁)) true →
      ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  obtain ⟨b, hb⟩ := CompletionReplay.right_finish_words (GraphPayoff.payoff B .inside)
    (.leaf T) U hU.1 hU.2 hTU
  refine ⟨b, ?_⟩
  intro S₀ S₁ T₀ U₁ v hSR hSL hSord hTord hUword hv hST hSU
  have hright := InsideEndgame.last_left_rightBlue hH B S₁ U₁ hSR hSL hSU
  obtain ⟨V, he, hVR, hVL⟩ := InsideEndgame.last_left_right_command hH B S₁ (.leaf U₁)
    hSR hSL (by simp) hright
  have hUV : U₁ = V := State.leaf.inj he
  subst V
  obtain ⟨c, hc⟩ := CompletionReplay.right_finish_words (GraphPayoff.payoff B .inside)
    (.leaf S₁) U₁ hVR hVL hright
  have hroom : U₁.position.stem.done.length < U₁.position.stem.root := by
    have h := U₁.position.room
    omega
  obtain ⟨A, hA⟩ := StemResponses.setup_above U₁.position U₁.position.stem.root
    hroom le_rfl hH (max b c)
  let u := StemResponses.completed A
  have hu₁ : word u.1 = U₁.position.ordinary ++ A.newWord := StemResponses.completed_word A
  have hu : word u.1 = U.position.ordinary ++ (v ++ A.newWord) := by
    rw [hu₁, hUword, List.append_assoc]
  have hf : ∀ x ∈ v ++ A.newWord, x ∈ H ∧ b < x := by
    intro x hx
    exact (List.mem_append.mp hx).elim (hv x)
      (fun hx ↦ ⟨(hA x hx).1, (le_max_left _ _).trans_lt (hA x hx).2⟩)
  obtain ⟨C, hCu, hbC⟩ := hb u (v ++ A.newWord) hu
    (fun x hx ↦ (hf x hx).1) (fun x hx ↦ (hf x hx).2)
  obtain ⟨C₁, hC₁u, hbC₁⟩ := hc u A.newWord hu₁
    (fun x hx ↦ (hA x hx).1) (fun x hx ↦ (le_max_right _ _).trans_lt (hA x hx).2)
  exact JointFinish.triangle_of_completed_right hH B .inside S₀ S₁ T₀ T C₁ C
    hSord hTord (hC₁u.trans hCu.symm) hST hbC₁ hbC

end Erdos118.OverlapFinish
