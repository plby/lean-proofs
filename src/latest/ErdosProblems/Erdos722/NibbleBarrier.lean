/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.CriticalFreedman
import ErdosProblems.Erdos722.NibbleObservables
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Simultaneous clique-removal barriers

This module packages the two edge-degree barriers, the two total-clique
barriers, and every lower-face barrier into the single finite index type
consumed by `CriticalFreedman`.  Its endpoint is already the deterministic
bounded-leave clique packing required by the cover stage.
-/

namespace Erdos722.NibbleBarrier

open Finset
open Erdos722.NibbleBasics
open Erdos722.NibbleProcess
open Erdos722.NibbleCounters
open Erdos722.NibbleObservables
open Erdos722.CriticalFreedman
open Erdos722.StoppedFreedman
open Erdos722.FiniteFreedman
open Erdos722.RandomGreedy
open Erdos722.AdaptiveChernoff
open Erdos722.Typicality

noncomputable section

variable {n q r : ℕ}

abbrev HostEdge (host : Finset (Finset (Fin n))) :=
  {e : Finset (Fin n) // e ∈ host}

abbrev LowerFace (n r : ℕ) :=
  {f : Finset (Fin n) // f ∈ uniformEdges n (r - 1)}

/-- Edge upper/lower, total-clique upper/lower, and weighted face targets. -/
abbrev BarrierIndex (host : Finset (Finset (Fin n))) (r : ℕ) :=
  ((HostEdge host × Bool) ⊕ Bool) ⊕ LowerFace n r

/-- The complete family of clique-removal deviations.  Boolean `false`
means upper and `true` means lower for the first two summands. -/
def barrierObservable
    (host H : Finset (Finset (Fin n))) (r : ℕ)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ) :
    BarrierIndex host r → List (Finset (Fin n)) → ℝ
  | Sum.inl (Sum.inl (⟨e, _he⟩, false)), history =>
      upperDegreeObservable host H r degreeUpper e history
  | Sum.inl (Sum.inl (⟨e, _he⟩, true)), history =>
      lowerDegreeObservable host H r degreeLower e history
  | Sum.inl (Sum.inr false), history =>
      cliqueObservable H r cliqueUpper history
  | Sum.inl (Sum.inr true), history =>
      -cliqueObservable H r cliqueLower history
  | Sum.inr ⟨f, _hf⟩, history =>
      weightedFaceObservable host r faceWeight faceCap f history

lemma barrierObservable_edgeUpper_eq
    (host H : Finset (Finset (Fin n))) (r : ℕ)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ)
    (e : HostEdge host) (history : List (Finset (Fin n))) :
    barrierObservable host H r degreeUpper degreeLower cliqueUpper cliqueLower
      faceWeight faceCap (Sum.inl (Sum.inl (e, false))) history =
      upperDegreeObservable host H r degreeUpper e.1 history := by rfl

lemma barrierObservable_edgeLower_eq
    (host H : Finset (Finset (Fin n))) (r : ℕ)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ)
    (e : HostEdge host) (history : List (Finset (Fin n))) :
    barrierObservable host H r degreeUpper degreeLower cliqueUpper cliqueLower
      faceWeight faceCap (Sum.inl (Sum.inl (e, true))) history =
      lowerDegreeObservable host H r degreeLower e.1 history := by rfl

lemma barrierObservable_cliqueLower_eq
    (host H : Finset (Finset (Fin n))) (r : ℕ)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ)
    (history : List (Finset (Fin n))) :
    barrierObservable host H r degreeUpper degreeLower cliqueUpper cliqueLower
      faceWeight faceCap (Sum.inl (Sum.inr true)) history =
      cliqueLower history.length -
        (availableCliques H r history).card := by
  simp [barrierObservable, cliqueObservable]

lemma barrierObservable_face_eq
    (host H : Finset (Finset (Fin n))) (r : ℕ)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ)
    (f : LowerFace n r) (history : List (Finset (Fin n))) :
    barrierObservable host H r degreeUpper degreeLower cliqueUpper cliqueLower
      faceWeight faceCap (Sum.inr f) history =
      weightedFaceObservable host r faceWeight faceCap f.1 history := by rfl

/-- Abstract but fully proved barrier endpoint.  The remaining hypotheses
are exactly the scalar drift, jump, variance, and exponential estimates for
the displayed concrete observables. -/
theorem exists_packing_faceDegree_le_of_critical
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ)
    (window jump : BarrierIndex host r → ℝ)
    (variance : BarrierIndex host r → ℕ → ℝ)
    (hvariance : ∀ z i, 0 ≤ variance z i)
    (rate : BarrierIndex host r → ℝ) (hrate : ∀ z, 0 < rate z)
    (hjumpNonneg : ∀ z, 0 ≤ jump z)
    (hjumpLt : ∀ z, jump z < window z)
    (hinitial : ∀ z,
      barrierObservable host H r degreeUpper degreeLower
        cliqueUpper cliqueLower faceWeight faceCap z [] < 0 ∧
      barrierObservable host H r degreeUpper degreeLower
        cliqueUpper cliqueLower faceWeight faceCap z [] ≤
          -window z + jump z)
    {depth : ℕ}
    (hcliqueLowerNonneg : ∀ i < depth, 0 ≤ cliqueLower i)
    (hjump : ∀ z history Q,
      history.length < depth →
      FollowsAvailable H r [] history →
      AllGood (fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap c h < 0) history →
      Q ∈ availableCliques H r history →
      |observableIncrement
        (barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap) z history Q| ≤ jump z)
    (hbound : ∀ z history Q,
      history.length < depth →
      FollowsAvailable H r [] history →
      AllGood (fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap c h < 0) history →
      Q ∈ availableCliques H r history →
      -window z ≤ barrierObservable host H r degreeUpper degreeLower
        cliqueUpper cliqueLower faceWeight faceCap z history →
      |rate z * observableIncrement
        (barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap) z history Q| ≤ 1)
    (hmean : ∀ z history,
      history.length < depth →
      FollowsAvailable H r [] history →
      AllGood (fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap c h < 0) history →
      -window z ≤ barrierObservable host H r degreeUpper degreeLower
        cliqueUpper cliqueLower faceWeight faceCap z history →
      (∑ Q : Finset (Fin n),
        uniformStep (availableCliques H r) history Q *
          observableIncrement
            (barrierObservable host H r degreeUpper degreeLower
              cliqueUpper cliqueLower faceWeight faceCap) z history Q) ≤ 0)
    (hvar : ∀ z history,
      history.length < depth →
      FollowsAvailable H r [] history →
      AllGood (fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower faceWeight faceCap c h < 0) history →
      -window z ≤ barrierObservable host H r degreeUpper degreeLower
        cliqueUpper cliqueLower faceWeight faceCap z history →
      (∑ Q : Finset (Fin n),
        uniformStep (availableCliques H r) history Q *
          (observableIncrement
            (barrierObservable host H r degreeUpper degreeLower
              cliqueUpper cliqueLower faceWeight faceCap) z history Q) ^ 2) ≤
        variance z history.length)
    {B : ℕ}
    (hsmall : (∑ z : BarrierIndex host r × Fin (depth + 1),
      Real.exp (-rate z.1 * (window z.1 - jump z.1)) *
        Real.exp ((rate z.1) ^ 2 * varianceBudget (variance z.1) 0 depth)) < 1)
    (hfaceWeight : 0 < faceWeight depth)
    (hfaceTerminal : faceCap depth ≤ faceWeight depth * B) :
    ∃ blocks : Finset (Finset (Fin n)),
      IsCliquePacking host blocks q r ∧
      ∀ f : Finset (Fin n), f.card = r - 1 →
        Erdos722.Reserve.localDegree (leave host blocks r) f ≤ B := by
  let Y := barrierObservable host H r degreeUpper degreeLower
    cliqueUpper cliqueLower faceWeight faceCap
  have hnonempty : ∀ history,
      history.length < depth →
      FollowsAvailable H r [] history →
      AllGood (fun h ↦ ∀ z, Y z h < 0) history →
        (availableCliques H r history).Nonempty := by
    intro history _hlen _hfollow hall
    have hlo := hall.current (good := fun h ↦ ∀ z, Y z h < 0)
      (Sum.inl (Sum.inr true))
    have hprofile := hcliqueLowerNonneg history.length _hlen
    rw [show Y (Sum.inl (Sum.inr true)) history =
        cliqueLower history.length -
          (availableCliques H r history).card by
            simpa [Y] using barrierObservable_cliqueLower_eq
              host H r degreeUpper degreeLower cliqueUpper cliqueLower
                faceWeight faceCap history] at hlo
    have hcard : 0 < (availableCliques H r history).card := by
      exact_mod_cast (show (0 : ℝ) < (availableCliques H r history).card by
        linarith)
    exact Finset.card_pos.mp hcard
  obtain ⟨path, hlen, hfollow, hall⟩ :=
    exists_legal_path_staying_below_zero_critical_indexed
      (availableCliques H r) Y window jump rate variance hvariance hrate
      hjumpNonneg hjumpLt hinitial hnonempty hjump hbound hmean hvar hsmall
  let blocks := path.toFinset
  have hpack : IsCliquePacking host blocks q r :=
    followsAvailable_isCliquePacking hH hfollow
  refine ⟨blocks, hpack, ?_⟩
  intro f hfcard
  let fi : LowerFace n r := ⟨f, mem_uniformEdges.mpr hfcard⟩
  have hface := hall.current
    (good := fun h ↦ ∀ z, Y z h < 0) (Sum.inr fi)
  have hleave : leave host blocks r = residualHost host r path := by
    symm
    exact host_sdiff_usedEdges_eq_leave host path
  change faceWeight path.length *
      (residualFaceDegree host r path f : ℝ) - faceCap path.length < 0 at hface
  have hcast : (residualFaceDegree host r path f : ℝ) < B + 1 := by
    rw [hlen] at hface
    have hmul : faceWeight depth *
        (residualFaceDegree host r path f : ℝ) < faceWeight depth * (B + 1) := by
      calc
        faceWeight depth * (residualFaceDegree host r path f : ℝ) <
            faceCap depth := by linarith
        _ ≤ faceWeight depth * B := hfaceTerminal
        _ < faceWeight depth * (B + 1) := by
          nlinarith
    exact lt_of_mul_lt_mul_left hmul hfaceWeight.le
  have hnat : residualFaceDegree host r path f ≤ B := by
    have hnatlt : residualFaceDegree host r path f < B + 1 := by
      exact_mod_cast hcast
    exact Nat.lt_succ_iff.mp (by simpa [Nat.add_comm] using hnatlt)
  simpa [Erdos722.Reserve.localDegree, residualFaceDegree, hleave,
    blocks] using hnat

end

end Erdos722.NibbleBarrier
