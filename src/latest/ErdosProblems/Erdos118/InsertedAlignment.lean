import ErdosProblems.Erdos118.RootInsertion

/-!
Both old next-body certificates are applied to the same literal ordinary
stem, with the inserted prefix already above the old bound. The resulting
actual conservative steps retain their different exact decorations.
-/

namespace Erdos118.InsertedAlignment

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays ReplaySources

def NextCertificate (H : Set ℕ) (B : SimpleGraph G) (P T : Pending)
    (c : ℕ) (hR : P.roots = [c]) (b : ℕ) : Prop :=
  ∀ Q : Stem, ∀ v : List ℕ,
    Q.root = P.position.stem.root → Q.done.length = c - 1 →
    Q.ordinary = P.position.ordinary ++ v →
    (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, b < x) →
    ∃ A : StemResponses.Setup P.position (c - 1), A.newWord = v ∧
      A.stem.ordinary = Q.ordinary ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
        (.leaf P, .leaf T) (.body (ofStem P c [] hR A), .leaf T) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside
        (.body (ofStem P c [] hR A), .leaf T)) true

theorem certificate {H : Set ℕ} (B : SimpleGraph G) (P T : Pending)
    (c : ℕ) (hR : P.roots = [c]) (hL : P.leaves = [])
    (hblue : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf T)) :
    ∃ b : ℕ, NextCertificate H B P T c hR b :=
  StemReplay.left_body_words_step (GraphPayoff.payoff B .inside) P (.leaf T) c [] hR hL hblue

theorem align {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (P R T U : Pending) (c : ℕ) (hPR : P.roots = [c]) (hPL : P.leaves = [])
    (hRR : R.roots = [c]) (hRL : R.leaves = [])
    (hP : ExactSlots.Exact (.leaf P)) (hR : ExactSlots.Exact (.leaf R))
    (hroot : R.position.stem.root = P.position.stem.root)
    (b : ℕ) (hcert : NextCertificate H B P T c hPR b)
    (v : List ℕ) (hv : R.position.ordinary = P.position.ordinary ++ v)
    (hvf : ∀ x ∈ v, x ∈ H ∧ b < x)
    (hblue : LeftBlue H (GraphPayoff.payoff B .inside) (.leaf R, .leaf U)) :
    ∃ D E : BodyDecision, D.roots = [] ∧ E.roots = [] ∧
      ExactSlots.Exact (.body D) ∧ ExactSlots.Exact (.body E) ∧
      D.stem.ordinary = E.stem.ordinary ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
        (.leaf P, .leaf T) (.body D, .leaf T) ∧
      ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
        (.leaf R, .leaf U) (.body E, .leaf U) ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.body D, .leaf T)) true ∧
      RamseyGame.Outcome H (GraphPayoff.game B .inside (.body E, .leaf U)) true ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.body D, .leaf T) ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.body E, .leaf U) := by
  obtain ⟨bR, hbR⟩ := certificate B R U c hRR hRL hblue
  have hbounds := next_body_bounds R c [] hRR
  obtain ⟨A, hf⟩ := StemResponses.setup_above R.position (c - 1)
    hbounds.1 hbounds.2.1 hH (max b bR)
  have hword : A.stem.ordinary = P.position.ordinary ++ (v ++ A.newWord) := by
    rw [A.ordinary, hv, List.append_assoc]
  have hwhole : ∀ x ∈ v ++ A.newWord, x ∈ H ∧ b < x := by
    intro x hx
    exact (List.mem_append.mp hx).elim (hvf x)
      (fun hx ↦ ⟨(hf x hx).1, (le_max_left _ _).trans_lt (hf x hx).2⟩)
  obtain ⟨A₀, _, hA₀, hs₀, hb₀⟩ := hcert A.stem (v ++ A.newWord)
    (A.root_eq.trans hroot) A.count hword
    (fun x hx ↦ (hwhole x hx).1) (fun x hx ↦ (hwhole x hx).2)
  obtain ⟨A₁, _, hA₁, hs₁, hb₁⟩ := hbR A.stem A.newWord A.root_eq A.count A.ordinary
    (fun x hx ↦ (hf x hx).1) (fun x hx ↦ (le_max_right _ _).trans_lt (hf x hx).2)
  let D := ofStem P c [] hPR A₀
  let E := ofStem R c [] hRR A₁
  exact ⟨D, E, rfl, rfl,
    ExactSlots.step_exact (DecisionStates.Step.nextBody P c [] hPR hPL A₀) hP,
    ExactSlots.step_exact (DecisionStates.Step.nextBody R c [] hRR hRL A₁) hR,
    hA₀.trans hA₁.symm, hs₀, hs₁, hb₀, hb₁,
    body_command B .inside false D T hb₀, body_command B .inside false E U hb₁⟩

structure PositiveBody (H : Set ℕ) (B : SimpleGraph G) (D : BodyDecision) (T : Pending) where
  size : ℕ
  positive : 0 < size
  bound : ℕ
  certificate : ∀ A : BodyResponses.Setup D.stem size,
    (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
    (∀ x ∈ BodyResponses.newWord A.position, bound < x) →
    RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf (applyBody D A), .leaf T)) true

theorem positive_body {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hlast : ∀ S T : Completed, GraphPayoff.payoff B .inside S T = true →
      (LastBodyRefinement.lastLabel S).length ≠ 1)
    (D : BodyDecision) (T : Pending) (hD : ExactSlots.Exact (.body D)) (hR : D.roots = [])
    (hblue : LeftBlue H (GraphPayoff.payoff B .inside) (.body D, .leaf T)) :
    Nonempty (PositiveBody H B D T) := by
  obtain ⟨k, b, hk, hb⟩ := LastBodyRefinement.positive_last_body hH B hlast D (.leaf T) hD hR hblue
  exact ⟨⟨k, hk, b, hb⟩⟩

end Erdos118.InsertedAlignment
