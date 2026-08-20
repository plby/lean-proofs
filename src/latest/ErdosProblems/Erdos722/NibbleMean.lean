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
import ErdosProblems.Erdos722.NibbleEdgeDrift
import Mathlib

/-!
# Simultaneous mean barriers for explicit clique-removal profiles

This module connects the concrete deletion estimates to the finite indexed
barrier.  The only hypotheses not proved here are scalar inequalities between
successive profile values.  In particular, legality is used to identify the
residual host size exactly with `g-Ki`, which makes the reciprocal-density
face drift identity exact rather than asymptotic.
-/

namespace Erdos722.NibbleMean

open Finset
open Erdos722.NibbleBasics
open Erdos722.NibbleProcess
open Erdos722.NibbleCounters
open Erdos722.NibbleObservables
open Erdos722.NibbleBarrier
open Erdos722.NibbleProfiles
open Erdos722.NibbleEdgeDrift
open Erdos722.NibbleFaceDrift
open Erdos722.StoppedFreedman
open Erdos722.AdaptiveChernoff

noncomputable section

variable {n q r : ℕ}

/-- All combinatorics and conditional-expectation identities are discharged
by this theorem.  The four `h...Scalar` hypotheses are one-dimensional
polynomial inequalities, suitable for `ring`/`nlinarith` after the concrete
profiles are unfolded. -/
theorem barrierObservable_mean_nonpos_of_scalar
    (hr : 0 < r) (hrq : r < q)
    {host H : Finset (Finset (Fin n))}
    (hhost : host ⊆ Erdos722.Typicality.uniformEdges n r)
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (U L : ℕ → ℕ)
    (slack eps : ℝ)
    (window : BarrierIndex host r → ℝ)
    {depth : ℕ}
    (hK : 0 < Nat.choose q r)
    (hg : 0 < host.card)
    (hdepth : ∀ i < depth,
      Nat.choose q r * (i + 1) < host.card)
    (hUpos : ∀ i < depth, 0 < U i)
    (hUEnvelope : ∀ i < depth, degreeUpper i ≤ U i)
    (hLEnvelope : ∀ i < depth, (L i : ℝ) ≤ degreeLower i)
    (hLU : ∀ i < depth, L i ≤ U i)
    (hcliqueLower : ∀ i < depth, 0 ≤ cliqueLower i)
    (hratio : ∀ i < depth, 1 - (L i : ℝ) / U i ≤ eps)
    (hUpperScalar : ∀ i < depth, ∀ (e : HostEdge host) (x M : ℕ),
      L i ≤ x → x ≤ U i → x ≤ M →
      cliqueLower i ≤ (M : ℝ) → (M : ℝ) ≤ cliqueUpper i →
      -window (Sum.inl (Sum.inl (e, false))) ≤
          (x : ℝ) - degreeUpper i →
      (0 : ℝ) ≤
        ((x * (Nat.choose q r - 1) *
          (L i - n ^ (q - r - 1)) : ℕ) : ℝ) -
        ((x * (Nat.choose q r - 1) ^ 2 *
          n ^ (q - r - 1) : ℕ) : ℝ) +
        ((M - x : ℕ) : ℝ) *
          (degreeUpper (i + 1) - degreeUpper i))
    (hLowerScalar : ∀ i < depth, ∀ (e : HostEdge host) (x M : ℕ),
      L i ≤ x → x ≤ U i → x ≤ M →
      cliqueLower i ≤ (M : ℝ) → (M : ℝ) ≤ cliqueUpper i →
      -window (Sum.inl (Sum.inl (e, true))) ≤
          degreeLower i - (x : ℝ) →
      (((x * (Nat.choose q r - 1) * U i : ℕ) : ℝ) +
        ((M - x : ℕ) : ℝ) *
          (degreeLower (i + 1) - degreeLower i)) ≤ 0)
    (hCliqueUpperScalar : ∀ i < depth,
      (0 : ℝ) ≤
        ((Nat.choose q r * L i : ℕ) : ℝ) -
        (((Nat.choose q r) ^ 2 * n ^ (q - r - 1) : ℕ) : ℝ) +
        (cliqueUpper (i + 1) - cliqueUpper i))
    (hCliqueLowerScalar : ∀ i < depth,
      ((Nat.choose q r * U i : ℕ) : ℝ) +
        (cliqueLower (i + 1) - cliqueLower i) ≤ 0) :
    ∀ z history,
      history.length < depth →
      FollowsAvailable H r [] history →
      AllGood (fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower
          (faceWeight host.card (Nat.choose q r))
          (faceCap n slack eps host.card (Nat.choose q r)) c h < 0) history →
      -window z ≤
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower
          (faceWeight host.card (Nat.choose q r))
          (faceCap n slack eps host.card (Nat.choose q r)) z history →
      (∑ Q : Finset (Fin n),
        uniformStep (availableCliques H r) history Q *
          observableIncrement
            (barrierObservable host H r degreeUpper degreeLower
              cliqueUpper cliqueLower
              (faceWeight host.card (Nat.choose q r))
              (faceCap n slack eps host.card (Nat.choose q r))) z history Q) ≤ 0 := by
  intro z history hlen hfollow hall hcritical
  let i := history.length
  have hi : i < depth := hlen
  have hne : (availableCliques H r history).Nonempty := by
    have hlo := hall.current
      (good := fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower
          (faceWeight host.card (Nat.choose q r))
          (faceCap n slack eps host.card (Nat.choose q r)) c h < 0)
      (Sum.inl (Sum.inr true))
    rw [barrierObservable_cliqueLower_eq] at hlo
    have hc := hcliqueLower i hi
    have hcard : 0 < (availableCliques H r history).card := by
      exact_mod_cast (show (0 : ℝ) < (availableCliques H r history).card by
        linarith)
    exact Finset.card_pos.mp hcard
  have hupperState : ∀ e ∈ residualHost host r history,
      availableDegree H r history e ≤ U i := by
    intro e he
    let ei : HostEdge host := ⟨e, (Finset.mem_sdiff.mp he).1⟩
    have hu := hall.current
      (good := fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower
          (faceWeight host.card (Nat.choose q r))
          (faceCap n slack eps host.card (Nat.choose q r)) c h < 0)
      (Sum.inl (Sum.inl (ei, false)))
    rw [barrierObservable_edgeUpper_eq,
      upperDegreeObservable_eq_of_relevant he] at hu
    change (availableDegree H r history e : ℝ) - degreeUpper i < 0 at hu
    have hreal : (availableDegree H r history e : ℝ) < U i :=
      (by linarith : (availableDegree H r history e : ℝ) < degreeUpper i).trans_le
        (hUEnvelope i hi)
    have hnat : availableDegree H r history e < U i := by exact_mod_cast hreal
    omega
  have hlowerState : ∀ e ∈ residualHost host r history,
      L i ≤ availableDegree H r history e := by
    intro e he
    let ei : HostEdge host := ⟨e, (Finset.mem_sdiff.mp he).1⟩
    have hlo := hall.current
      (good := fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower
          (faceWeight host.card (Nat.choose q r))
          (faceCap n slack eps host.card (Nat.choose q r)) c h < 0)
      (Sum.inl (Sum.inl (ei, true)))
    rw [barrierObservable_edgeLower_eq,
      lowerDegreeObservable_eq_of_relevant he] at hlo
    change degreeLower i - (availableDegree H r history e : ℝ) < 0 at hlo
    have hreal : (L i : ℝ) < availableDegree H r history e :=
      lt_of_le_of_lt (hLEnvelope i hi) (by linarith)
    have hnat : L i < availableDegree H r history e := by exact_mod_cast hreal
    omega
  have hMUpper : ((availableCliques H r history).card : ℝ) ≤
      cliqueUpper i := by
    have hu := hall.current
      (good := fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower
          (faceWeight host.card (Nat.choose q r))
          (faceCap n slack eps host.card (Nat.choose q r)) c h < 0)
      (Sum.inl (Sum.inr false))
    change ((availableCliques H r history).card : ℝ) - cliqueUpper i < 0 at hu
    linarith
  have hdegreeLeM : ∀ e,
      availableDegree H r history e ≤ (availableCliques H r history).card := by
    intro e
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hMLower : cliqueLower i ≤
      ((availableCliques H r history).card : ℝ) := by
    have hlo := hall.current
      (good := fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower
          (faceWeight host.card (Nat.choose q r))
          (faceCap n slack eps host.card (Nat.choose q r)) c h < 0)
      (Sum.inl (Sum.inr true))
    rw [barrierObservable_cliqueLower_eq] at hlo
    linarith
  rcases z with (⟨⟨e, heHost⟩, isLower⟩ | isClique) | ⟨f, hf⟩
  · cases isLower with
    | false =>
        by_cases he : e ∈ residualHost host r history
        · have hecard : e.card = r :=
            Erdos722.Typicality.mem_uniformEdges.mp
              (hhost (Finset.mem_sdiff.mp he).1)
          apply sum_uniformStep_mul_upperDegreeIncrement_nonpos
            hr hrq hH he hecard hne degreeUpper (L i) hlowerState
          have hc := hcritical
          rw [barrierObservable_edgeUpper_eq,
            upperDegreeObservable_eq_of_relevant he] at hc
          change -window (Sum.inl (Sum.inl (⟨e, heHost⟩, false))) ≤
            (availableDegree H r history e : ℝ) - degreeUpper i at hc
          exact hUpperScalar i hi ⟨e, heHost⟩
            (availableDegree H r history e)
            (availableCliques H r history).card
            (hlowerState e he) (hupperState e he)
            (hdegreeLeM e)
            hMLower hMUpper hc
        · apply Finset.sum_nonpos
          intro Q hQ
          simp only [observableIncrement, barrierObservable_edgeUpper_eq]
          rw [upperDegreeObservable_increment]
          simp [he]
    | true =>
        by_cases he : e ∈ residualHost host r history
        · apply sum_uniformStep_mul_lowerDegreeIncrement_nonpos
            hH he hne degreeLower (U i) hupperState
          have hc := hcritical
          rw [barrierObservable_edgeLower_eq,
            lowerDegreeObservable_eq_of_relevant he] at hc
          change -window (Sum.inl (Sum.inl (⟨e, heHost⟩, true))) ≤
            degreeLower i - (availableDegree H r history e : ℝ) at hc
          exact hLowerScalar i hi ⟨e, heHost⟩
            (availableDegree H r history e)
            (availableCliques H r history).card
            (hlowerState e he) (hupperState e he)
            (hdegreeLeM e)
            hMLower hMUpper hc
        · apply Finset.sum_nonpos
          intro Q hQ
          simp only [observableIncrement, barrierObservable_edgeLower_eq]
          rw [lowerDegreeObservable_increment]
          simp [he]
  · cases isClique with
    | false =>
        simpa [observableIncrement, barrierObservable, i] using
          sum_uniformStep_mul_cliqueUpperIncrement_nonpos hr hrq hH hne
            cliqueUpper (L i) hlowerState (hCliqueUpperScalar i hi)
    | true =>
        have hs : (Nat.choose q r * U i : ℝ) +
            (cliqueLower (history.length + 1) -
              cliqueLower history.length) ≤ 0 := by
          simpa [i, Nat.cast_mul] using hCliqueLowerScalar i hi
        simpa [observableIncrement, barrierObservable, i] using
          sum_uniformStep_mul_cliqueLowerIncrement_nonpos hH hne
            cliqueLower (U i) hupperState hs
  ·
    have hfcard : f.card = r - 1 :=
      Erdos722.Typicality.mem_uniformEdges.mp hf
    have hstep := hdepth i hi
    have hmul : Nat.choose q r * i < host.card := by
      exact (Nat.mul_le_mul_left (Nat.choose q r) (by omega)).trans_lt hstep
    have hcardNat := card_residualHost_append_path hH hfollow
    have hcardNat' : (residualHost host r history).card =
        host.card - history.length * Nat.choose q r := by
      simpa [residualHost, usedEdges] using hcardNat
    have hcard : ((residualHost host r history).card : ℝ) =
        remaining host.card (Nat.choose q r) i := by
      rw [hcardNat', Nat.cast_sub (show
        history.length * Nat.choose q r ≤ host.card by
          simpa [Nat.mul_comm] using hmul.le)]
      simp [i, remaining]
      ring
    apply sum_uniformStep_mul_weightedFaceIncrement_nonpos
      hH hr hhost hne
      (faceWeight host.card (Nat.choose q r))
      (faceCap n slack eps host.card (Nat.choose q r)) eps f hfcard
      (L i) (U i) hK (hUpos i hi) hlowerState hupperState (hLU i hi)
    · exact faceWeight_pos hg hstep
    · change 0 ≤ faceWeight host.card (Nat.choose q r) (i + 1) -
          faceWeight host.card (Nat.choose q r) i
      linarith [faceWeight_mono_step hK hstep]
    · rw [hcard]
      exact faceWeight_sub_div_next hg hstep
    · exact hratio i hi
    · exact faceCap_succ_sub n host.card (Nat.choose q r) i slack eps

end

end Erdos722.NibbleMean
