import ErdosProblems.Erdos118.FirstMiddle
import ErdosProblems.Erdos118.BodyRebase

/-! The retained fine label is submitted on the exact second-game stem,
after a literal fresh buffer above any later requested suffix bound. -/

namespace Erdos118.FineBody

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays BoundaryRelays

structure Response {H : Set ℕ} {B : SimpleGraph G} {O : LateOpening.Opening H B}
    (D : FirstMiddle.Diagram O) (d : ℕ) where
  setup : BodyResponses.Setup O.insertedBody.stem O.insertedPositive.size
  suffix : List ℕ
  ordinary : setup.position.ordinary = D.left.position.ordinary ++ suffix
  entries : setup.position.entries = D.left.position.entries ++ suffix
  marker : setup.position.size = D.left.position.size
  label : setup.position.label = D.reserve.label
  fresh : ∀ x ∈ suffix, x ∈ H ∧ d < x
  supported : ∀ x ∈ BodyResponses.newWord setup.position, x ∈ H ∧ D.bound < x
  step : ConservativeRuns.Step H (GraphPayoff.payoff B .inside)
    (.body O.insertedBody, .leaf O.insertedRight)
    (.leaf (applyBody O.insertedBody setup), .leaf O.insertedRight)
  blue : RamseyGame.Outcome H (GraphPayoff.game B .inside
    (.leaf (applyBody O.insertedBody setup), .leaf O.insertedRight)) true
  handoff : RightBlue H (GraphPayoff.payoff B .inside)
    (.leaf (applyBody O.insertedBody setup), .leaf O.insertedRight)
  exactSlots : ExactSlots.Exact (.leaf (applyBody O.insertedBody setup))
  roots : (applyBody O.insertedBody setup).roots = []
  leaves : (applyBody O.insertedBody setup).leaves ≠ []

theorem exists_response {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    {O : LateOpening.Opening H B} (D : FirstMiddle.Diagram O) (d : ℕ) :
    Nonempty (Response D d) := by
  obtain ⟨A, v, hv, he, hm, hl, hf, hnew⟩ := D.reserve.buffer hH D.left D.leftExact
    D.leftLeaf D.entriesSupported d
  have hbefore : ∀ x ∈ O.insertedBody.stem.decorated,
      ∀ y ∈ BodyResponses.newWord A.position, x < y := by
    intro x hx y hy
    exact ((nat_le_sum_of_mem hx).trans D.fineStem).trans_lt (hnew y hy).2
  let A' := BodyRebase.setup A O.insertedBody.stem O.insertedBody.room hbefore
  have hord : A'.position.ordinary = A.position.ordinary :=
    BodyRebase.setup_ordinary A O.insertedBody.stem O.insertedBody.room hbefore
      (O.sameOrdinary.symm.trans (congrArg Stem.ordinary D.leftStem).symm)
  have hnew' : ∀ x ∈ BodyResponses.newWord A'.position, x ∈ H ∧ D.bound < x := hnew
  have hb := O.insertedPositive.certificate A' (fun x hx ↦ (hnew' x hx).1)
    (fun x hx ↦ D.fineBound.trans_lt (hnew' x hx).2)
  have hs := body_step B .inside false O.insertedBody (.leaf O.insertedRight) A'
    (command_allowed B .inside false O.insertedBody (.leaf O.insertedRight) O.insertedCommand)
    (fun x hx ↦ (hnew' x hx).1) (fun x hx ↦ D.finePair.trans_lt (hnew' x hx).2)
    (fun x hx ↦ D.fineGuard.trans_lt (hnew' x hx).2)
  have hh := body_handoff hH B .inside false O.insertedBody (.leaf O.insertedRight) A'
    (fun x hx ↦ D.finePair.trans_lt (hnew' x hx).2) hb
  have hL : (applyBody O.insertedBody A').leaves ≠ [] := by
    intro he
    have he' : A'.position.label.tail = [] := he
    have hlen := congrArg List.length he'
    rw [List.length_tail, A'.label_length] at hlen
    simp only [List.length_nil] at hlen
    have hk := O.insertedPositive.positive
    omega
  exact ⟨{
    setup := A', suffix := v, ordinary := hord.trans hv, entries := he, marker := hm
    label := hl, fresh := hf, supported := hnew', step := hs, blue := hb, handoff := hh
    exactSlots := ExactSlots.step_exact (DecisionStates.Step.body O.insertedBody A') O.insertedExact
    roots := O.insertedLast, leaves := hL }⟩

end Erdos118.FineBody
