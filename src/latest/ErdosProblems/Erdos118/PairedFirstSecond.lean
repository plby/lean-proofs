import ErdosProblems.Erdos118.SharedFirstSecond
import ErdosProblems.Erdos118.PreparedRelays
import ErdosProblems.Erdos118.NextSelectedLeaf

/-! Actual paired body responses on independently specified game sides.
Each response uses its own original blue certificate and conservative guard. -/

namespace Erdos118.PairedFirstSecond

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays

structure Pair (H : Set ℕ) (B : SimpleGraph G) (rightA rightE : Bool)
    (D E : BodyDecision) (T U : State) (k l : ℕ) where
  lowerSetup : BodyResponses.Setup D.stem k
  upperSetup : BodyResponses.Setup E.stem l
  sameOrdinary : lowerSetup.position.ordinary = upperSetup.position.ordinary
  sameMarker : lowerSetup.position.size = upperSetup.position.size
  sameEntries : lowerSetup.position.entries = upperSetup.position.entries
  sameFirst : lowerSetup.position.label.headD 0 = upperSetup.position.label.headD 0
  aligned : SharedFirstSecond.Aligned lowerSetup.position.label upperSetup.position.label
  lowerStep : ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
    (pair rightA (.body D) T) (pair rightA (.leaf (applyBody D lowerSetup)) T)
  upperStep : ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
    (pair rightE (.body E) U) (pair rightE (.leaf (applyBody E upperSetup)) U)
  lowerBlue : Blue H B .inside rightA (.leaf (applyBody D lowerSetup)) T
  upperBlue : Blue H B .inside rightE (.leaf (applyBody E upperSetup)) U
  lowerHandoff : OtherBlue H B .inside rightA (.leaf (applyBody D lowerSetup)) T
  upperHandoff : OtherBlue H B .inside rightE (.leaf (applyBody E upperSetup)) U

def Pair.lower {H : Set ℕ} {B : SimpleGraph G} {ra re : Bool}
    {D E : BodyDecision} {T U : State} {k l : ℕ} (F : Pair H B ra re D E T U k l) : Pending :=
  applyBody D F.lowerSetup

def Pair.upper {H : Set ℕ} {B : SimpleGraph G} {ra re : Bool}
    {D E : BodyDecision} {T U : State} {k l : ℕ} (F : Pair H B ra re D E T U k l) : Pending :=
  applyBody E F.upperSetup

theorem Pair.exactSlots {H : Set ℕ} {B : SimpleGraph G} {ra re : Bool}
    {D E : BodyDecision} {T U : State} {k l : ℕ} (F : Pair H B ra re D E T U k l)
    (hD : ExactSlots.Exact (.body D)) (hE : ExactSlots.Exact (.body E)) :
    ExactSlots.Exact (.leaf F.lower) ∧ ExactSlots.Exact (.leaf F.upper) :=
  ⟨ExactSlots.step_exact (DecisionStates.Step.body D F.lowerSetup) hD,
    ExactSlots.step_exact (DecisionStates.Step.body E F.upperSetup) hE⟩

theorem Pair.next_upper {H : Set ℕ} {B : SimpleGraph G} {ra re : Bool}
    {D E : BodyDecision} {T U : State} {k l : ℕ} (F : Pair H B ra re D E T U k l)
    (hE : ExactSlots.Exact (.body E)) (hk : 0 < k) :
    ∃ rest : List ℕ, F.upper.leaves = F.lower.position.label.getLastD 0 :: rest := by
  have ha := F.aligned
  rcases ha with ha | ⟨hlt, hmem, hmin⟩
  · rw [F.lowerSetup.label_length] at ha
    omega
  · have hcount : F.upper.position.entries.length = F.lower.position.label.headD 0 :=
      F.upperSetup.entries_length.trans F.sameFirst.symm
    exact NextSelectedLeaf.next_leaf F.upper
      (ExactSlots.step_exact (DecisionStates.Step.body E F.upperSetup) hE)
      _ hmem (hcount ▸ hlt) (fun j hj hij ↦ hmin j hj (hcount ▸ hij))

theorem exists_pair {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (ra re : Bool) (D E : BodyDecision) (T U : State) (hord : D.stem.ordinary = E.stem.ordinary)
    (k l b₁ b₂ : ℕ) (hcompat : 0 < k → 0 < l)
    (hc₁ : CommandBlue H B .inside ra (.body D) T)
    (hc₂ : CommandBlue H B .inside re (.body E) U)
    (hcert₁ : ∀ A : BodyResponses.Setup D.stem k,
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
      (∀ x ∈ BodyResponses.newWord A.position, b₁ < x) →
      Blue H B .inside ra (.leaf (applyBody D A)) T)
    (hcert₂ : ∀ A : BodyResponses.Setup E.stem l,
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
      (∀ x ∈ BodyResponses.newWord A.position, b₂ < x) →
      Blue H B .inside re (.leaf (applyBody E A)) U)
    (d : ℕ) :
    ∃ F : Pair H B ra re D E T U k l,
      (∀ x ∈ BodyResponses.newWord F.lowerSetup.position, x ∈ H ∧ d < x) ∧
      (∀ x ∈ BodyResponses.newWord F.upperSetup.position, x ∈ H ∧ d < x) := by
  let c₁ := pairBound (pair ra (.body D) T)
  let c₂ := pairBound (pair re (.body E) U)
  let g₁ := guard H B .inside ra D T k
  let g₂ := guard H B .inside re E U l
  let M := max b₁ (max b₂ (max c₁ (max c₂ (max g₁ (max g₂ d)))))
  have hb₁M : b₁ ≤ M := by dsimp [M]; omega
  have hb₂M : b₂ ≤ M := by dsimp [M]; omega
  have hc₁M : c₁ ≤ M := by dsimp [M]; omega
  have hc₂M : c₂ ≤ M := by dsimp [M]; omega
  have hg₁M : g₁ ≤ M := by dsimp [M]; omega
  have hg₂M : g₂ ≤ M := by dsimp [M]; omega
  have hdM : d ≤ M := by dsimp [M]; omega
  obtain ⟨A, F, hord, hm, he, hf, ha, hA, hF⟩ := SharedFirstSecond.body_pair
    hH D.stem E.stem D.room E.room hord M k l hcompat
  have hAc : ∀ x ∈ BodyResponses.newWord A.position, c₁ < x :=
    fun x hx ↦ hc₁M.trans_lt (hA x hx).2
  have hFc : ∀ x ∈ BodyResponses.newWord F.position, c₂ < x :=
    fun x hx ↦ hc₂M.trans_lt (hF x hx).2
  have hbA := hcert₁ A (fun x hx ↦ (hA x hx).1)
    (fun x hx ↦ hb₁M.trans_lt (hA x hx).2)
  have hbF := hcert₂ F (fun x hx ↦ (hF x hx).1)
    (fun x hx ↦ hb₂M.trans_lt (hF x hx).2)
  let P : Pair H B ra re D E T U k l :=
    { lowerSetup := A, upperSetup := F, sameOrdinary := hord, sameMarker := hm
      sameEntries := he, sameFirst := hf, aligned := ha
      lowerStep := body_step B .inside ra D T A (command_allowed B .inside ra D T hc₁)
        (fun x hx ↦ (hA x hx).1) hAc (fun x hx ↦ hg₁M.trans_lt (hA x hx).2)
      upperStep := body_step B .inside re E U F (command_allowed B .inside re E U hc₂)
        (fun x hx ↦ (hF x hx).1) hFc (fun x hx ↦ hg₂M.trans_lt (hF x hx).2)
      lowerBlue := hbA, upperBlue := hbF
      lowerHandoff := body_handoff hH B .inside ra D T A hAc hbA
      upperHandoff := body_handoff hH B .inside re E U F hFc hbF }
  exact ⟨P, fun x hx ↦ ⟨(hA x hx).1, hdM.trans_lt (hA x hx).2⟩,
    fun x hx ↦ ⟨(hF x hx).1, hdM.trans_lt (hF x hx).2⟩⟩

end Erdos118.PairedFirstSecond
