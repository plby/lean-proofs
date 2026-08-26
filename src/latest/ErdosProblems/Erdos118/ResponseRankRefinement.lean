import ErdosProblems.Erdos118.ResponseRefinement
import ErdosProblems.Erdos118.PreparedRelays

/-! Fix a bounded test after the actual root/body parameter is issued,
but before sampling any label in that response family. -/

namespace Erdos118.ResponseRankRefinement

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays ReservedResponses RamseyGame

theorem right_root {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (hinit : Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (P : Pending) (hc : RightBlue H (GraphPayoff.payoff B .inside) (.leaf P, .initial))
    (test : ℕ → Completed → Completed → ℕ) (bound : ℕ → ℕ)
    (hb : ∀ k S T, GraphPayoff.payoff B .inside S T = true → test k S T ≤ bound k) :
    ∃ k : ℕ, ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      RightBlue K (GraphPayoff.payoff C .inside) (.leaf P, .initial) ∧
      ∃ value ≤ bound k, ∃ b : ℕ,
        (∀ A : RootResponses.Setup k,
          (∀ x ∈ A.stem.decorated, x ∈ K) → (∀ x ∈ A.stem.decorated, b < x) →
          Outcome K (GraphPayoff.game C .inside (.leaf P, .body (ofRoot A))) true) ∧
        (∀ S T, GraphPayoff.payoff C .inside S T = true → test k S T = value) := by
  obtain ⟨k, b, hcert⟩ := SecondWhole.second_root_blue hH B hB .inside hinit P hc
  let c := pairBound (.leaf P, .initial)
  let R := rootResponse k c
  obtain ⟨K, hKH, hK, C, hCB, hC, v, hv, d, hd, htest⟩ :=
    ResponseRefinement.refine_nat (bound k) hH B hB .inside R.family
      (fun a ↦ (.leaf P, R.result a)) b hcert (test k) (hb k)
  have hside : allowedSide (.leaf P, .initial) true = true := by
    obtain ⟨_, _, hs, _⟩ := hc
    exact hs
  have hcC : RightBlue K (GraphPayoff.payoff C .inside) (.leaf P, .initial) :=
    ⟨k + 1, R, hside, rfl, d, hd⟩
  refine ⟨k, K, hKH, hK, C, hCB, hC, hcC, v, hv, max d c, ?_, htest⟩
  intro A hAK hAd
  have hAc : ∀ x ∈ A.stem.decorated, c < x :=
    fun x hx ↦ (le_max_right _ _).trans_lt (hAd x hx)
  let a := rootMember c A hAc
  have haK : (↑a.1 : Set ℕ) ⊆ K := fun x hx ↦ hAK x (List.mem_toFinset.mp hx)
  have had : ∀ x ∈ a.1, d < x := fun x hx ↦
    (le_max_left _ _).trans_lt (hAd x (List.mem_toFinset.mp hx))
  have hnext := hd a haK had
  change Outcome K (GraphPayoff.game C .inside
    (.leaf P, (rootResponse k c).result (rootMember c A hAc))) true at hnext
  rw [rootMember_result] at hnext
  exact hnext

private theorem body_family {H : Set ℕ} (B : SimpleGraph G) (right : Bool)
    (D : BodyDecision) (T : State) (hc : CommandBlue H B .inside right (.body D) T) :
    ∃ k b : ℕ,
      ∀ a : (bodyResponse D k (pairBound (pair right (.body D) T))).family.members,
      (↑a.1 : Set ℕ) ⊆ H → (∀ x ∈ a.1, b < x) →
      Outcome H (GraphPayoff.game B .inside
        (pair right
          ((bodyResponse D k (pairBound (pair right (.body D) T))).result a) T)) true := by
  cases right with
  | false =>
    obtain ⟨k, R, _, hR, b, hb⟩ := hc
    have he : R = bodyResponse D k (pairBound (.body D, T)) := Option.some.inj hR.symm
    subst R
    exact ⟨k, b, hb⟩
  | true =>
    obtain ⟨k, R, _, hR, b, hb⟩ := hc
    have he : R = bodyResponse D k (pairBound (T, .body D)) := Option.some.inj hR.symm
    subst R
    exact ⟨k, b, hb⟩

theorem body {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (right : Bool) (D : BodyDecision) (T : State)
    (hc : CommandBlue H B .inside right (.body D) T)
    (test : ℕ → Completed → Completed → ℕ) (bound : ℕ → ℕ)
    (hb : ∀ k S T, GraphPayoff.payoff B .inside S T = true → test k S T ≤ bound k) :
    ∃ k : ℕ, ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      CommandBlue K C .inside right (.body D) T ∧
      ∃ value ≤ bound k, ∃ b : ℕ,
        (∀ A : BodyResponses.Setup D.stem k,
          (∀ x ∈ BodyResponses.newWord A.position, x ∈ K) →
          (∀ x ∈ BodyResponses.newWord A.position, b < x) →
          Blue K C .inside right (.leaf (applyBody D A)) T) ∧
        (∀ S T, GraphPayoff.payoff C .inside S T = true → test k S T = value) := by
  obtain ⟨k, b, hcert⟩ := body_family B right D T hc
  let c := pairBound (pair right (.body D) T)
  let R := bodyResponse D k c
  obtain ⟨K, hKH, hK, C, hCB, hC, v, hv, d, hd, htest⟩ :=
    ResponseRefinement.refine_nat (bound k) hH B hB .inside R.family
      (fun a ↦ pair right (R.result a) T) b hcert (test k) (hb k)
  have hside := command_allowed B .inside right D T hc
  have hcC : CommandBlue K C .inside right (.body D) T := by
    cases right with
    | false => exact ⟨k, R, hside, rfl, d, hd⟩
    | true => exact ⟨k, R, hside, rfl, d, hd⟩
  refine ⟨k, K, hKH, hK, C, hCB, hC, hcC, v, hv, max d c, ?_, htest⟩
  intro A hAK hAd
  have hAc : ∀ x ∈ BodyResponses.newWord A.position, c < x :=
    fun x hx ↦ (le_max_right _ _).trans_lt (hAd x hx)
  let a := bodyMember D c A hAc
  have haK : (↑a.1 : Set ℕ) ⊆ K := fun x hx ↦ hAK x (List.mem_toFinset.mp hx)
  have had : ∀ x ∈ a.1, d < x := fun x hx ↦
    (le_max_left _ _).trans_lt (hAd x (List.mem_toFinset.mp hx))
  have hnext := hd a haK had
  change Outcome K (GraphPayoff.game C .inside
    (pair right ((bodyResponse D k c).result (bodyMember D c A hAc)) T)) true at hnext
  rw [bodyMember_result] at hnext
  exact hnext

end Erdos118.ResponseRankRefinement
