import ErdosProblems.Erdos118.InsertedAlignment

/-! Align the old and inserted last-body stems without conflating
their graphs, alphabets, conservative steps, or blue certificates. -/

namespace Erdos118.InsertedCrossAlignment

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays ReplaySources
open InsertedAlignment (NextCertificate)

structure Aligned (H K : Set ℕ) (B C : SimpleGraph G) (P R T U : Pending) where
  old : BodyDecision
  inserted : BodyDecision
  oldRoots : old.roots = []
  insertedRoots : inserted.roots = []
  oldExact : ExactSlots.Exact (.body old)
  insertedExact : ExactSlots.Exact (.body inserted)
  ordinary : old.stem.ordinary = inserted.stem.ordinary
  oldStep : ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
    (.leaf P, .leaf T) (.body old, .leaf T)
  insertedStep : ConservativeRuns.Step K (GraphPayoff.payoff C .inside)
    (.leaf R, .leaf U) (.body inserted, .leaf U)
  oldBlue : RamseyGame.Outcome H (GraphPayoff.game B .inside (.body old, .leaf T)) true
  insertedBlue : RamseyGame.Outcome K (GraphPayoff.game C .inside (.body inserted, .leaf U)) true
  oldCommand : LeftBlue H (GraphPayoff.payoff B .inside) (.body old, .leaf T)
  insertedCommand : LeftBlue K (GraphPayoff.payoff C .inside) (.body inserted, .leaf U)

theorem align {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H) (B C : SimpleGraph G)
    (P R T U : Pending) (c : ℕ) (hPR : P.roots = [c]) (hPL : P.leaves = [])
    (hRR : R.roots = [c]) (hRL : R.leaves = [])
    (hP : ExactSlots.Exact (.leaf P)) (hR : ExactSlots.Exact (.leaf R))
    (hroot : R.position.stem.root = P.position.stem.root)
    (b : ℕ) (hcert : NextCertificate H B P T c hPR b)
    (v : List ℕ) (hv : R.position.ordinary = P.position.ordinary ++ v)
    (hvf : ∀ x ∈ v, x ∈ H ∧ b < x)
    (hblue : LeftBlue K (GraphPayoff.payoff C .inside) (.leaf R, .leaf U)) :
    Nonempty (Aligned H K B C P R T U) := by
  obtain ⟨bR, hbR⟩ := InsertedAlignment.certificate C R U c hRR hRL hblue
  have hbounds := next_body_bounds R c [] hRR
  obtain ⟨A, hf⟩ := StemResponses.setup_above R.position (c - 1)
    hbounds.1 hbounds.2.1 hK (max b bR)
  have hword : A.stem.ordinary = P.position.ordinary ++ (v ++ A.newWord) := by
    rw [A.ordinary, hv, List.append_assoc]
  have hwhole : ∀ x ∈ v ++ A.newWord, x ∈ H ∧ b < x := by
    intro x hx
    exact (List.mem_append.mp hx).elim (hvf x)
      (fun hx ↦ ⟨hKH (hf x hx).1, (le_max_left _ _).trans_lt (hf x hx).2⟩)
  obtain ⟨A₀, _, hA₀, hs₀, hb₀⟩ := hcert A.stem (v ++ A.newWord)
    (A.root_eq.trans hroot) A.count hword
    (fun x hx ↦ (hwhole x hx).1) (fun x hx ↦ (hwhole x hx).2)
  obtain ⟨A₁, _, hA₁, hs₁, hb₁⟩ := hbR A.stem A.newWord A.root_eq A.count A.ordinary
    (fun x hx ↦ (hf x hx).1) (fun x hx ↦ (le_max_right _ _).trans_lt (hf x hx).2)
  let D := ofStem P c [] hPR A₀
  let E := ofStem R c [] hRR A₁
  exact ⟨{
    old := D, inserted := E, oldRoots := rfl, insertedRoots := rfl
    oldExact := ExactSlots.step_exact (DecisionStates.Step.nextBody P c [] hPR hPL A₀) hP
    insertedExact := ExactSlots.step_exact (DecisionStates.Step.nextBody R c [] hRR hRL A₁) hR
    ordinary := hA₀.trans hA₁.symm, oldStep := hs₀, insertedStep := hs₁
    oldBlue := hb₀, insertedBlue := hb₁
    oldCommand := body_command B .inside false D T hb₀
    insertedCommand := body_command C .inside false E U hb₁ }⟩

end Erdos118.InsertedCrossAlignment
