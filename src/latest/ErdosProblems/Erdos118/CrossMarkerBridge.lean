import ErdosProblems.Erdos118.StrictMarkerRequests

/-! One literal ordinary marker stem for a paused right source and
a left target on another graph, retaining the source's later roots. -/

namespace Erdos118.CrossMarkerBridge

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates
open BlueRuns

structure Aligned (H K : Set ℕ) (B C : SimpleGraph G) (S P T U : Pending)
    (rest : List ℕ) (d : ℕ) where
  source : BodyDecision
  target : BodyDecision
  sourceRoots : source.roots = rest
  targetRoots : target.roots = []
  sourceExact : ExactSlots.Exact (.body source)
  targetExact : ExactSlots.Exact (.body target)
  ordinary : source.stem.ordinary = target.stem.ordinary
  sourceStep : ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
    (.leaf S, .leaf P) (.leaf S, .body source)
  targetStep : ConservativeRuns.Step K (GraphPayoff.payoff C .inside)
    (.leaf T, .leaf U) (.body target, .leaf U)
  sourceBlue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf S, .body source)) true
  targetBlue : RamseyGame.Outcome K (GraphPayoff.game C .inside (.body target, .leaf U)) true
  sourceCommand : RightBlue H (GraphPayoff.payoff B .inside) (.leaf S, .body source)
  targetCommand : LeftBlue K (GraphPayoff.payoff C .inside) (.body target, .leaf U)
  fresh : FreshCheckpoints.FreshExtension K d (.leaf T, .leaf U) (.body target, .leaf U)

theorem align {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H) (B C : SimpleGraph G)
    (S P T U : Pending) (c : ℕ) (rest : List ℕ)
    (hPR : P.roots = c :: rest) (hPL : P.leaves = [])
    (hTR : T.roots = [c]) (hTL : T.leaves = [])
    (hP : ExactSlots.Exact (.leaf P)) (hT : ExactSlots.Exact (.leaf T))
    (hroot : T.position.stem.root = P.position.stem.root)
    (R : StrictMarkerRequests.RightCertificate H B S P c rest hPR)
    (v : List ℕ) (hv : T.position.ordinary = P.position.ordinary ++ v)
    (hvf : ∀ x ∈ v, x ∈ H ∧ R.bound < x)
    (hblue : LeftBlue K (GraphPayoff.payoff C .inside) (.leaf T, .leaf U)) (d : ℕ) :
    Nonempty (Aligned H K B C S P T U rest d) := by
  obtain ⟨bT, hbT⟩ := InsertedAlignment.certificate C T U c hTR hTL hblue
  have hbounds := next_body_bounds T c [] hTR
  let b := max R.bound (max bT d)
  have hRb : R.bound ≤ b := le_max_left _ _
  have hTb : bT ≤ b := by dsimp [b]; omega
  have hdb : d ≤ b := by dsimp [b]; omega
  obtain ⟨A, hf⟩ := StemResponses.setup_above T.position (c - 1)
    hbounds.1 hbounds.2.1 hK b
  have hword : A.stem.ordinary = P.position.ordinary ++ (v ++ A.newWord) := by
    rw [A.ordinary, hv, List.append_assoc]
  have hwhole : ∀ x ∈ v ++ A.newWord, x ∈ H ∧ R.bound < x := by
    intro x hx
    exact (List.mem_append.mp hx).elim (hvf x)
      (fun hx ↦ ⟨hKH (hf x hx).1, hRb.trans_lt (hf x hx).2⟩)
  obtain ⟨A₀, _, hA₀, hs₀, hb₀⟩ := R.certificate A.stem (v ++ A.newWord)
    (A.root_eq.trans hroot) A.count hword
    (fun x hx ↦ (hwhole x hx).1) (fun x hx ↦ (hwhole x hx).2)
  obtain ⟨A₁, _, hA₁, hs₁, hb₁⟩ := hbT A.stem A.newWord A.root_eq A.count A.ordinary
    (fun x hx ↦ (hf x hx).1) (fun x hx ↦ hTb.trans_lt (hf x hx).2)
  let D := ofStem P c rest hPR A₀
  let E := ofStem T c [] hTR A₁
  exact ⟨{
    source := D, target := E, sourceRoots := rfl, targetRoots := rfl
    sourceExact := ExactSlots.step_exact (DecisionStates.Step.nextBody P c rest hPR hPL A₀) hP
    targetExact := ExactSlots.step_exact (DecisionStates.Step.nextBody T c [] hTR hTL A₁) hT
    ordinary := hA₀.trans hA₁.symm, sourceStep := hs₀, targetStep := hs₁
    sourceBlue := hb₀, targetBlue := hb₁
    sourceCommand := ReplaySources.body_command B .inside true D S hb₀
    targetCommand := ReplaySources.body_command C .inside false E U hb₁
    fresh := ⟨A.newWord, [], hA₁.trans A.ordinary, by simp,
      fun x hx ↦ ⟨(hf x hx).1, hdb.trans_lt (hf x hx).2⟩, by simp⟩ }⟩

end Erdos118.CrossMarkerBridge
