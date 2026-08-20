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
import ErdosProblems.Erdos722.NibbleMoments
import Mathlib

/-!
# Finite profile-to-nibble theorem

This is the final finite wrapper around the clique-removal calculation.
All hypergraph counting, stopping, and variance arguments have been
discharged.  Its remaining assumptions are scalar inequalities between the
chosen one-dimensional profiles and one explicit exponential union bound.
-/

namespace Erdos722.NibbleFinite

open Finset
open Erdos722.NibbleBasics
open Erdos722.NibbleProcess
open Erdos722.NibbleCounters
open Erdos722.NibbleBarrier
open Erdos722.NibbleProfiles
open Erdos722.NibbleMean
open Erdos722.NibbleMoments
open Erdos722.NibbleVariance
open Erdos722.StoppedFreedman
open Erdos722.FiniteFreedman
open Erdos722.AdaptiveChernoff
open Erdos722.Typicality

noncomputable section

variable {n q r : ℕ}

/-- Variance is relevant only before the prescribed terminal depth. -/
def finiteVariance
    (host : Finset (Finset (Fin n))) (q r : ℕ)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (faceWeight faceCap : ℕ → ℝ) (U : ℕ → ℕ)
    (depth : ℕ) (z : BarrierIndex host r) (i : ℕ) : ℝ :=
  if i < depth then
    barrierJump host q r degreeUpper degreeLower cliqueUpper cliqueLower
        faceWeight faceCap U z i *
      barrierAbsBudget host q r degreeUpper degreeLower cliqueUpper cliqueLower
        faceWeight faceCap U cliqueLower z i
  else 0

theorem exists_packing_faceDegree_le_of_finite_profiles
    (hr : 0 < r) (hrq : r < q)
    {host H : Finset (Finset (Fin n))}
    (hhost : host ⊆ uniformEdges n r)
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (degreeUpper degreeLower cliqueUpper cliqueLower : ℕ → ℝ)
    (U L : ℕ → ℕ) (slack eps : ℝ)
    (window jumpCap : BarrierIndex host r → ℝ)
    {depth : ℕ}
    (hK : 0 < Nat.choose q r)
    (hg : 0 < host.card)
    (hdepth : ∀ i < depth,
      Nat.choose q r * (i + 1) < host.card)
    (hUpos : ∀ i < depth, 0 < U i)
    (hUEnvelope : ∀ i < depth, degreeUpper i ≤ U i)
    (hLEnvelope : ∀ i < depth, (L i : ℝ) ≤ degreeLower i)
    (hLU : ∀ i < depth, L i ≤ U i)
    (hcliqueLowerPos : ∀ i < depth, 0 < cliqueLower i)
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
        (cliqueLower (i + 1) - cliqueLower i) ≤ 0)
    (hJumpCap : ∀ z i, i < depth →
      barrierJump host q r degreeUpper degreeLower cliqueUpper cliqueLower
        (faceWeight host.card (Nat.choose q r))
        (faceCap n slack eps host.card (Nat.choose q r)) U z i ≤ jumpCap z)
    (hjumpNonneg : ∀ z, 0 ≤ jumpCap z)
    (hjumpLt : ∀ z, jumpCap z < window z)
    (hinitial : ∀ z,
      barrierObservable host H r degreeUpper degreeLower
        cliqueUpper cliqueLower
        (faceWeight host.card (Nat.choose q r))
        (faceCap n slack eps host.card (Nat.choose q r)) z [] < 0 ∧
      barrierObservable host H r degreeUpper degreeLower
        cliqueUpper cliqueLower
        (faceWeight host.card (Nat.choose q r))
        (faceCap n slack eps host.card (Nat.choose q r)) z [] ≤
          -window z + jumpCap z)
    (rate : BarrierIndex host r → ℝ) (hrate : ∀ z, 0 < rate z)
    (hrateJump : ∀ z, rate z * jumpCap z ≤ 1)
    (hsmall : (∑ z : BarrierIndex host r × Fin (depth + 1),
      Real.exp (-rate z.1 * (window z.1 - jumpCap z.1)) *
        Real.exp ((rate z.1) ^ 2 * varianceBudget
          (finiteVariance host q r degreeUpper degreeLower
            cliqueUpper cliqueLower
            (faceWeight host.card (Nat.choose q r))
            (faceCap n slack eps host.card (Nat.choose q r)) U depth z.1)
          0 depth)) < 1)
    {B : ℕ}
    (hfaceTerminal :
      faceCap n slack eps host.card (Nat.choose q r) depth ≤
        faceWeight host.card (Nat.choose q r) depth * B) :
    ∃ blocks : Finset (Finset (Fin n)),
      IsCliquePacking host blocks q r ∧
      ∀ f : Finset (Fin n), f.card = r - 1 →
        Erdos722.Reserve.localDegree (leave host blocks r) f ≤ B := by
  let w := faceWeight host.card (Nat.choose q r)
  let cap := faceCap n slack eps host.card (Nat.choose q r)
  let J := barrierJump host q r degreeUpper degreeLower
    cliqueUpper cliqueLower w cap U
  let A := barrierAbsBudget host q r degreeUpper degreeLower
    cliqueUpper cliqueLower w cap U cliqueLower
  let V := finiteVariance host q r degreeUpper degreeLower
    cliqueUpper cliqueLower w cap U depth
  have hmean := barrierObservable_mean_nonpos_of_scalar
    hr hrq hhost hH degreeUpper degreeLower cliqueUpper cliqueLower
    U L slack eps window hK hg hdepth hUpos hUEnvelope hLEnvelope hLU
    (fun i hi ↦ (hcliqueLowerPos i hi).le) hratio
    hUpperScalar hLowerScalar hCliqueUpperScalar hCliqueLowerScalar
  have hvariance : ∀ z i, 0 ≤ V z i := by
    intro z i
    by_cases hi : i < depth
    · simp only [V, finiteVariance, if_pos hi]
      exact mul_nonneg
        (barrierJump_nonneg host q r degreeUpper degreeLower
          cliqueUpper cliqueLower w cap U z i)
        (barrierAbsBudget_nonneg host q r degreeUpper degreeLower
          cliqueUpper cliqueLower w cap U cliqueLower z i
          (hcliqueLowerPos i hi))
    · simp [V, finiteVariance, hi]
  have hmoments : ∀ history,
      history.length < depth →
      AllGood (fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower w cap c h < 0) history →
      (∀ z, ∀ Q ∈ availableCliques H r history,
        |observableIncrement
          (barrierObservable host H r degreeUpper degreeLower
            cliqueUpper cliqueLower w cap) z history Q| ≤ J z history.length) ∧
      (∀ z,
        (∑ Q : Finset (Fin n),
          uniformStep (availableCliques H r) history Q *
            |observableIncrement
              (barrierObservable host H r degreeUpper degreeLower
                cliqueUpper cliqueLower w cap) z history Q|) ≤
          A z history.length) := by
    intro history hlen hall
    simpa [w, cap, J, A] using
      barrierObservable_jump_absMoment_of_good hr hrq hhost hH
        degreeUpper degreeLower cliqueUpper cliqueLower w cap U
        hUEnvelope hcliqueLowerPos hlen hall
  have hvar : ∀ z history,
      history.length < depth →
      FollowsAvailable H r [] history →
      AllGood (fun h ↦ ∀ c,
        barrierObservable host H r degreeUpper degreeLower
          cliqueUpper cliqueLower w cap c h < 0) history →
      -window z ≤ barrierObservable host H r degreeUpper degreeLower
        cliqueUpper cliqueLower w cap z history →
      (∑ Q : Finset (Fin n),
        uniformStep (availableCliques H r) history Q *
          (observableIncrement
            (barrierObservable host H r degreeUpper degreeLower
              cliqueUpper cliqueLower w cap) z history Q) ^ 2) ≤
        V z history.length := by
    intro z history hlen hfollow hall _hcritical
    have hv := barrier_variance_of_absMoment
      degreeUpper degreeLower cliqueUpper cliqueLower w cap J A
      (depth := depth)
      (fun z i ↦ barrierJump_nonneg host q r degreeUpper degreeLower
        cliqueUpper cliqueLower w cap U z i)
      (fun z h Q hl _hf ha hQ ↦ (hmoments h hl ha).1 z Q hQ)
      (fun z h hl _hf ha ↦ (hmoments h hl ha).2 z)
      z history hlen hfollow hall
    simpa [V, finiteVariance, J, A, hlen] using hv
  apply exists_packing_faceDegree_le_of_critical hH
    degreeUpper degreeLower cliqueUpper cliqueLower w cap
    window jumpCap V hvariance rate hrate hjumpNonneg hjumpLt
    (by simpa [w, cap] using hinitial)
    (fun i hi ↦ (hcliqueLowerPos i hi).le)
  · intro z history Q hlen _hfollow hall hQ
    exact (hmoments history hlen hall).1 z Q hQ |>.trans
      (by simpa [J] using hJumpCap z history.length hlen)
  · intro z history Q hlen _hfollow hall hQ _hcritical
    rw [abs_mul, abs_of_pos (hrate z)]
    calc
      rate z * |observableIncrement
          (barrierObservable host H r degreeUpper degreeLower
            cliqueUpper cliqueLower w cap) z history Q| ≤
          rate z * jumpCap z := by
            exact mul_le_mul_of_nonneg_left
              ((hmoments history hlen hall).1 z Q hQ |>.trans
                (by simpa [J] using hJumpCap z history.length hlen))
              (hrate z).le
      _ ≤ 1 := hrateJump z
  · intro z history hlen hfollow hall hcritical
    simpa [w, cap] using hmean z history hlen hfollow hall hcritical
  · exact hvar
  · simpa [V, w, cap] using hsmall
  · apply faceWeight_pos hg
    by_cases hd : depth = 0
    · subst depth
      simpa using hg
    · have hlt : depth - 1 < depth := Nat.sub_lt
        (Nat.zero_lt_of_ne_zero hd) (by norm_num)
      have hlast := hdepth (depth - 1) hlt
      have heq : depth - 1 + 1 = depth :=
        Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)
      simpa [heq] using hlast
  · simpa [w, cap] using hfaceTerminal

end

end Erdos722.NibbleFinite
