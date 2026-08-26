import ErdosProblems.Erdos118.AlignedMarkerBridge

/-! Apply two actual right next-body decoders to one literal stem.
The earlier extension remains above the original saved bound. -/

namespace Erdos118.AlignedSecondMarker

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays AlignedFirstBodies

theorem align {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (S P T Q : Pending) (c : ℕ) (hPR : P.roots = [c]) (hPL : P.leaves = [])
    (hQR : Q.roots = [c]) (hQL : Q.leaves = [])
    (hP : ExactSlots.Exact (.leaf P)) (hQ : ExactSlots.Exact (.leaf Q))
    (hroot : Q.position.stem.root = P.position.stem.root)
    (R : RightRequest H B S P c hPR)
    (v : List ℕ) (hv : Q.position.ordinary = P.position.ordinary ++ v)
    (hvf : ∀ x ∈ v, x ∈ H ∧ R.bound < x)
    (hblue : RightBlue H (GraphPayoff.payoff B .inside) (.leaf T, .leaf Q)) :
    ∃ D E : BodyDecision, D.roots = [] ∧ E.roots = [] ∧
      ExactSlots.Exact (.body D) ∧ ExactSlots.Exact (.body E) ∧
      D.stem.ordinary = E.stem.ordinary ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
        (.leaf S, .leaf P) (.leaf S, .body D) ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
        (.leaf T, .leaf Q) (.leaf T, .body E) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf S, .body D)) true ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf T, .body E)) true ∧
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf S, .body D) ∧
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf T, .body E) := by
  obtain ⟨bQ, hbQ⟩ := StemReplay.right_body_words_step (GraphPayoff.payoff B .inside)
    (.leaf T) Q c [] hQR hQL hblue
  have hbounds := next_body_bounds Q c [] hQR
  obtain ⟨A, hf⟩ := StemResponses.setup_above Q.position (c - 1)
    hbounds.1 hbounds.2.1 hH (max R.bound bQ)
  have hword : A.stem.ordinary = P.position.ordinary ++ (v ++ A.newWord) := by
    rw [A.ordinary, hv, List.append_assoc]
  have hwhole : ∀ x ∈ v ++ A.newWord, x ∈ H ∧ R.bound < x := by
    intro x hx
    exact (List.mem_append.mp hx).elim (hvf x)
      (fun hx ↦ ⟨(hf x hx).1, (le_max_left _ _).trans_lt (hf x hx).2⟩)
  obtain ⟨A₀, _, hA₀, hs₀, hb₀⟩ := R.certificate A.stem (v ++ A.newWord)
    (A.root_eq.trans hroot) A.count hword
    (fun x hx ↦ (hwhole x hx).1) (fun x hx ↦ (hwhole x hx).2)
  obtain ⟨A₁, _, hA₁, hs₁, hb₁⟩ := hbQ A.stem A.newWord A.root_eq A.count A.ordinary
    (fun x hx ↦ (hf x hx).1) (fun x hx ↦ (le_max_right _ _).trans_lt (hf x hx).2)
  let D := ofStem P c [] hPR A₀
  let E := ofStem Q c [] hQR A₁
  exact ⟨D, E, rfl, rfl,
    ExactSlots.step_exact (DecisionStates.Step.nextBody P c [] hPR hPL A₀) hP,
    ExactSlots.step_exact (DecisionStates.Step.nextBody Q c [] hQR hQL A₁) hQ,
    hA₀.trans hA₁.symm, hs₀, hs₁, hb₀, hb₁,
    ReplaySources.body_command B .inside true D S hb₀,
    ReplaySources.body_command B .inside true E T hb₁⟩

end Erdos118.AlignedSecondMarker
