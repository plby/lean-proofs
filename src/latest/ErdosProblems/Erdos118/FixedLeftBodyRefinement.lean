import ErdosProblems.Erdos118.ResponseRefinement
import ErdosProblems.Erdos118.PreparedRelays

/-! Refine a caller's already issued literal body certificate,
preserving its exact parameter rather than choosing a new command. -/

namespace Erdos118.FixedLeftBodyRefinement

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns RamseyGame

theorem refine {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (D : BodyDecision) (P : Pending) (k b : ℕ)
    (hcert : ∀ A : BodyResponses.Setup D.stem k,
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
      (∀ x ∈ BodyResponses.newWord A.position, b < x) →
      Outcome H (GraphPayoff.game B .inside (.leaf (applyBody D A), .leaf P)) true)
    (m : ℕ) (test : Completed → Completed → ℕ)
    (hbound : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true → test S T ≤ m) :
    ∃ K ⊆ H, K.Infinite ∧ ∃ C : SimpleGraph G, C ≤ B ∧ C.CliqueFree 3 ∧
      LeftBlue K (GraphPayoff.payoff C .inside) (.body D, .leaf P) ∧
      ∃ value ≤ m, ∃ d : ℕ,
        (∀ A : BodyResponses.Setup D.stem k,
          (∀ x ∈ BodyResponses.newWord A.position, x ∈ K) →
          (∀ x ∈ BodyResponses.newWord A.position, d < x) →
          Outcome K (GraphPayoff.game C .inside (.leaf (applyBody D A), .leaf P)) true) ∧
        (∀ S T : Completed, GraphPayoff.payoff C .inside S T = true → test S T = value) := by
  let F := BodyResponses.responseFamily D.stem k D.room
  let e := BodyResponses.supportEquiv D.stem k
  let X : F.members → State × State := fun a ↦ (.leaf (applyBody D (e.symm a)), .leaf P)
  have hf : ∀ a : F.members, (↑a.1 : Set ℕ) ⊆ H → (∀ x ∈ a.1, b < x) →
      Outcome H (GraphPayoff.game B .inside (X a)) true := by
    intro a ha hlarge
    apply hcert (e.symm a)
    · intro x hx
      apply ha
      exact BodyResponses.support_symm a ▸ List.mem_toFinset.mpr hx
    · intro x hx
      apply hlarge
      exact BodyResponses.support_symm a ▸ List.mem_toFinset.mpr hx
  obtain ⟨K, hKH, hK, C, hCB, hC, value, hv, d, hd, htest⟩ :=
    ResponseRefinement.refine_nat m hH B hB .inside F X b hf test hbound
  let c := pairBound (.body D, .leaf P)
  have hc : LeftBlue K (GraphPayoff.payoff C .inside) (.body D, .leaf P) := by
    refine ⟨k, bodyResponse D k c, rfl, rfl, d, ?_⟩
    intro a ha hlarge
    exact hd (forgetBound F c a) ha hlarge
  refine ⟨K, hKH, hK, C, hCB, hC, hc, value, hv, d, ?_, htest⟩
  intro A hAK hAd
  have haK : (↑(e A).1 : Set ℕ) ⊆ K := fun x hx ↦ hAK x (List.mem_toFinset.mp hx)
  have had : ∀ x ∈ (e A).1, d < x := fun x hx ↦ hAd x (List.mem_toFinset.mp hx)
  have hnext := hd (e A) haK had
  simpa only [X, Equiv.symm_apply_apply] using hnext

end Erdos118.FixedLeftBodyRefinement
