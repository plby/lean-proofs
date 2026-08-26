import ErdosProblems.Erdos118.PendingCounts
import ErdosProblems.Erdos118.PreparedRelays

/-! Exact aligned last-body label counts, including the parameter of an
actual right body certificate against an already fixed left last body. -/

namespace Erdos118.AlignedBodyCounts

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open InsideCounts LastBodyRefinement BlueRuns

theorem pending {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S = beforeLast T)
    (P Q : Pending) (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (hPR : P.roots = []) (hQR : Q.roots = [])
    (hb : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf Q)) true) :
    P.position.label.length = Q.position.label.length + 1 := by
  obtain ⟨S, T, hrun, hp⟩ := blue_completion hH (GraphPayoff.payoff B .inside) (.leaf P, .leaf Q) hb
  obtain ⟨hr, hc, ho, _⟩ := (GraphPayoff.payoff_true_iff B .inside S T).mp hp
  obtain ⟨heP, heQ⟩ := SkippedCuts.run_extensions hrun
  have h := last_counts_of_before_eq S T hc hr ho
    (PendingCounts.rootLabel_ne_nil_of_extension P S heP)
    (PendingCounts.rootLabel_ne_nil_of_extension Q T heQ) (hall S T hp)
  rwa [lastLabel_of_extension P S hP hPR heP.labels,
    lastLabel_of_extension Q T hQ hQR heQ.labels] at h

theorem right_certificate {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hall : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      beforeLast S = beforeLast T)
    (P : Pending) (D : BodyDecision) (hP : ExactSlots.Exact (.leaf P))
    (hD : ExactSlots.Exact (.body D)) (hPR : P.roots = []) (hDR : D.roots = [])
    (t b : ℕ) (hcert : ∀ A : BodyResponses.Setup D.stem t,
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
      (∀ x ∈ BodyResponses.newWord A.position, b < x) →
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf (applyBody D A))) true) :
    P.position.label.length = t + 2 := by
  obtain ⟨A, hA⟩ := BodyResponses.setup_above D.stem t D.room hH b
  have hb := hcert A (fun x hx ↦ (hA x hx).1) (fun x hx ↦ (hA x hx).2)
  have h := pending hH B hall P (applyBody D A) hP
    (ExactSlots.step_exact (DecisionStates.Step.body D A) hD) hPR hDR hb
  change P.position.label.length = A.position.label.length + 1 at h
  rw [A.label_length] at h
  exact h

end Erdos118.AlignedBodyCounts
