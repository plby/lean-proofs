import ErdosProblems.Erdos118.AlignedFirstBodies

/-! Decode one literal last-body stem in an old right next-body request
and a later third-game left request, preserving both exact decorations. -/

namespace Erdos118.AlignedMarkerBridge

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays AlignedFirstBodies

theorem align {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (S P T U : Pending) (c : ℕ) (hPR : P.roots = [c]) (hPL : P.leaves = [])
    (hTR : T.roots = [c]) (hTL : T.leaves = [])
    (hP : ExactSlots.Exact (.leaf P)) (hT : ExactSlots.Exact (.leaf T))
    (hroot : T.position.stem.root = P.position.stem.root)
    (R : RightRequest H B S P c hPR)
    (v : List ℕ) (hv : T.position.ordinary = P.position.ordinary ++ v)
    (hvf : ∀ x ∈ v, x ∈ H ∧ R.bound < x)
    (hblue : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf T, .leaf U)) :
    ∃ D E : BodyDecision, D.roots = [] ∧ E.roots = [] ∧
      ExactSlots.Exact (.body D) ∧ ExactSlots.Exact (.body E) ∧
      D.stem.ordinary = E.stem.ordinary ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
        (.leaf S, .leaf P) (.leaf S, .body D) ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
        (.leaf T, .leaf U) (.body E, .leaf U) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf S, .body D)) true ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.body E, .leaf U)) true ∧
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf S, .body D) ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.body E, .leaf U) := by
  obtain ⟨bT, hbT⟩ := InsertedAlignment.certificate B T U c hTR hTL hblue
  have hbounds := next_body_bounds T c [] hTR
  obtain ⟨A, hf⟩ := StemResponses.setup_above T.position (c - 1)
    hbounds.1 hbounds.2.1 hH (max R.bound bT)
  have hword : A.stem.ordinary = P.position.ordinary ++ (v ++ A.newWord) := by
    rw [A.ordinary, hv, List.append_assoc]
  have hwhole : ∀ x ∈ v ++ A.newWord, x ∈ H ∧ R.bound < x := by
    intro x hx
    exact (List.mem_append.mp hx).elim (hvf x)
      (fun hx ↦ ⟨(hf x hx).1, (le_max_left _ _).trans_lt (hf x hx).2⟩)
  obtain ⟨A₀, _, hA₀, hs₀, hb₀⟩ := R.certificate A.stem (v ++ A.newWord)
    (A.root_eq.trans hroot) A.count hword
    (fun x hx ↦ (hwhole x hx).1) (fun x hx ↦ (hwhole x hx).2)
  obtain ⟨A₁, _, hA₁, hs₁, hb₁⟩ := hbT A.stem A.newWord A.root_eq A.count A.ordinary
    (fun x hx ↦ (hf x hx).1) (fun x hx ↦ (le_max_right _ _).trans_lt (hf x hx).2)
  let D := ofStem P c [] hPR A₀
  let E := ofStem T c [] hTR A₁
  exact ⟨D, E, rfl, rfl,
    ExactSlots.step_exact (DecisionStates.Step.nextBody P c [] hPR hPL A₀) hP,
    ExactSlots.step_exact (DecisionStates.Step.nextBody T c [] hTR hTL A₁) hT,
    hA₀.trans hA₁.symm, hs₀, hs₁, hb₀, hb₁,
    ReplaySources.body_command B .inside true D S hb₀,
    ReplaySources.body_command B .inside false E U hb₁⟩

end Erdos118.AlignedMarkerBridge
