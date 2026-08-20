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
import ErdosProblems.Erdos722.NibbleProfiles
import Mathlib

/-!
# Drift of reciprocal-density lower-face counters

This file isolates the exact algebra behind the weighted face counter.  If
all surviving edge degrees lie between `L` and `U`, then the chance that the
next clique covers one of the `F` residual edges through a fixed lower face
is at least `F*K*L/(R*U)`, where `R` is the residual host size.  The
reciprocal-density weight has relative increment `K/R`; consequently only
the relative degree error `1-L/U` must be paid into the face cap.
-/

namespace Erdos722.NibbleFaceDrift

open Finset
open Erdos722.NibbleBasics
open Erdos722.NibbleProcess
open Erdos722.NibbleCounters
open Erdos722.NibbleObservables
open Erdos722.RandomGreedy
open Erdos722.AdaptiveChernoff

noncomputable section

variable {n q r : ℕ}

/-- Pure real algebra used by the conditional-mean theorem below. -/
lemma weighted_face_algebra
    {K R L U M F S w w' eps N : ℝ}
    (hK : 0 < K) (hR : 0 < R) (hU : 0 < U) (hM : 0 < M)
    (hF : 0 ≤ F) (hS : F * L ≤ S)
    (hMupper : K * M ≤ R * U)
    (hweight : 0 < w') (hdw : 0 ≤ w' - w)
    (hrelative : (w' - w) / w' = K / R)
    (hLU0 : 0 ≤ L) (hLU : L ≤ U)
    (heps : 1 - L / U ≤ eps)
    (hFN : F ≤ N) :
    (w' - w) * F - w' * (S / M) -
        N * eps * (w' - w) ≤ 0 := by
  have hnum : 0 ≤ F * L := mul_nonneg hF hLU0
  have hden : M ≤ R * U / K := (le_div_iff₀ hK).2 (by
    simpa [mul_comm] using hMupper)
  have hdenPos : 0 < R * U / K := div_pos (mul_pos hR hU) hK
  have hquotient : F * L / (R * U / K) ≤ S / M := by
    calc
      F * L / (R * U / K) ≤ F * L / M := by
        exact div_le_div_of_nonneg_left hnum hM hden
      _ ≤ S / M := by
        exact div_le_div_of_nonneg_right hS hM.le
  have hrewrite : F * L / (R * U / K) =
      F * (K / R) * (L / U) := by
    field_simp
  rw [hrewrite] at hquotient
  have hscaled : (w' - w) * F * (L / U) ≤ w' * (S / M) := by
    have hw := mul_le_mul_of_nonneg_left hquotient hweight.le
    calc
      (w' - w) * F * (L / U) =
          w' * (F * (K / R) * (L / U)) := by
            rw [← hrelative]
            field_simp
      _ ≤ w' * (S / M) := hw
  have herror0 : 0 ≤ 1 - L / U := by
    have := (div_le_one hU).2 hLU
    linarith
  have hN0 : 0 ≤ N := hF.trans hFN
  have hfaceError :
      (w' - w) * F * (1 - L / U) ≤
        N * eps * (w' - w) := by
    calc
      (w' - w) * F * (1 - L / U) ≤
          (w' - w) * N * (1 - L / U) := by
            gcongr
      _ ≤ (w' - w) * N * eps := by
            exact mul_le_mul_of_nonneg_left heps (mul_nonneg hdw hN0)
      _ = N * eps * (w' - w) := by ring
  calc
    (w' - w) * F - w' * (S / M) -
        N * eps * (w' - w) ≤
      (w' - w) * F - (w' - w) * F * (L / U) -
        N * eps * (w' - w) := by linarith
    _ = (w' - w) * F * (1 - L / U) -
        N * eps * (w' - w) := by ring
    _ ≤ 0 := by linarith

/-- Concrete nonpositive conditional mean for a weighted residual-face
observable.  All combinatorial estimates are discharged here; only the
four scalar profile relations remain as hypotheses. -/
theorem sum_uniformStep_mul_weightedFaceIncrement_nonpos
    {host H : Finset (Finset (Fin n))}
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (hr : 0 < r)
    (hhost : host ⊆ Erdos722.Typicality.uniformEdges n r)
    {history : List (Finset (Fin n))}
    (hne : (availableCliques H r history).Nonempty)
    (weight cap : ℕ → ℝ) (eps : ℝ)
    (f : Finset (Fin n)) (hf : f.card = r - 1) (L U : ℕ)
    (hK : 0 < Nat.choose q r)
    (hU : 0 < U)
    (hlower : ∀ e ∈ residualHost host r history,
      L ≤ availableDegree H r history e)
    (hupper : ∀ e ∈ residualHost host r history,
      availableDegree H r history e ≤ U)
    (hLU : L ≤ U)
    (hweight : 0 < weight (history.length + 1))
    (hdw : 0 ≤ weight (history.length + 1) - weight history.length)
    (hrelative :
      (weight (history.length + 1) - weight history.length) /
          weight (history.length + 1) =
        (Nat.choose q r : ℝ) /
          (residualHost host r history).card)
    (heps : 1 - (L : ℝ) / U ≤ eps)
    (hcap : cap (history.length + 1) - cap history.length =
      (n : ℝ) * eps *
        (weight (history.length + 1) - weight history.length)) :
    (∑ Q : Finset (Fin n),
      uniformStep (availableCliques H r) history Q *
        (weightedFaceObservable host r weight cap f (history ++ [Q]) -
          weightedFaceObservable host r weight cap f history)) ≤ 0 := by
  rw [sum_uniformStep_mul_weightedFaceIncrement
    (fun Q hQ ↦ (hH Q hQ).2) weight cap f hne]
  let K : ℝ := Nat.choose q r
  let R : ℝ := (residualHost host r history).card
  let M : ℝ := (availableCliques H r history).card
  let F : ℝ := residualFaceDegree host r history f
  let S : ℝ := ∑ Q ∈ availableCliques H r history, faceLoss r Q f
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast Finset.card_pos.mpr hne
  have hMupperNat := choose_mul_card_available_le_residual_mul_degreeUpper
    hH history U hupper
  have hMupper : K * M ≤ R * U := by
    dsimp [K, M, R]
    exact_mod_cast hMupperNat
  have hR : 0 < R := by
    have hKreal : 0 < K := by
      dsimp [K]
      exact_mod_cast hK
    have hUreal : 0 < (U : ℝ) := by exact_mod_cast hU
    nlinarith
  have hSNat := faceDegree_mul_degreeLower_le_sum_faceLoss
    (fun Q hQ ↦ (hH Q hQ).2) history f L hlower
  have hS : F * L ≤ S := by
    dsimp [F, S]
    exact_mod_cast hSNat
  have hF0 : 0 ≤ F := by positivity
  have hFN : F ≤ n := by
    dsimp [F]
    exact_mod_cast residualFaceDegree_le_n hr hhost history hf
  have halg := weighted_face_algebra
    (K := K) (R := R) (L := L) (U := U) (M := M) (F := F) (S := S)
    (w := weight history.length) (w' := weight (history.length + 1))
    (eps := eps) (N := n)
    (by dsimp [K]; exact_mod_cast hK) hR (by exact_mod_cast hU) hM hF0 hS hMupper
    hweight hdw hrelative (by positivity) (by exact_mod_cast hLU) heps hFN
  rw [hcap]
  simpa [F, S, M] using halg

end

end Erdos722.NibbleFaceDrift
