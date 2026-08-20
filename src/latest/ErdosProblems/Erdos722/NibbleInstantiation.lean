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
import ErdosProblems.Erdos722.NibbleFinite
import ErdosProblems.Erdos722.NibbleTerminal
import Mathlib

/-!
# Instantiation of the finite nibble theorem

This file connects the concrete reciprocal-power profiles to the finite
five-barrier theorem.  The remaining tail hypotheses are isolated as
uniform jump and exponential estimates, so their asymptotic verification
does not have to repeat any combinatorial or profile algebra.
-/

namespace Erdos722.NibbleInstantiation

open Finset
open Erdos722.NibbleBasics
open Erdos722.NibbleProcess
open Erdos722.NibbleCounters
open Erdos722.NibbleObservables
open Erdos722.NibbleBarrier
open Erdos722.NibbleProfiles
open Erdos722.NibbleConcrete
open Erdos722.NibbleAsymptotic
open Erdos722.NibbleFinite
open Erdos722.NibbleMoments
open Erdos722.FiniteFreedman
open Erdos722.Typicality

noncomputable section

variable {n q r : ℕ}

def initialError (n q r : ℕ) : ℝ :=
  centerDegree n q r / (scale n q r : ℝ) ^ (5 * K q r - 1)

def profileWindow (host : Finset (Finset (Fin n))) (q r : ℕ) :
    BarrierIndex host r → ℝ
  | Sum.inl (Sum.inl _) => initialError n q r / 4
  | Sum.inl (Sum.inr _) =>
      (host.card : ℝ) * initialError n q r / (4 * K q r)
  | Sum.inr _ => faceSlack n q r / 2

def concreteVariance
    (host : Finset (Finset (Fin n))) (q r : ℕ) :
    BarrierIndex host r → ℕ → ℝ :=
  finiteVariance host q r
    (upperProfile host.card n q r) (lowerProfile host.card n q r)
    (cliqueUpperProfile host.card n q r)
    (cliqueLowerProfile host.card n q r)
    (faceWeight host.card (K q r))
    (faceCap n (faceSlack n q r) (faceEps n q r)
      host.card (K q r))
    (upperNat host.card n q r) (depth host.card n q r)

lemma degreeErrorGrowth_nonneg (g n q r i : ℕ)
    (hd₀ : 0 ≤ density g (K q r) i)
    (hd₁ : 0 ≤ density g (K q r) (i + 1)) :
    0 ≤ degreeErrorGrowth g n q r i := by
  unfold degreeErrorGrowth profileA centerDegree
  have hscale : (0 : ℝ) ≤ scale n q r := by positivity
  have hext : (0 : ℝ) ≤ Erdos722.Boost.extensionScale n q r := by positivity
  have hg : (0 : ℝ) ≤ g := by positivity
  have hK : (0 : ℝ) ≤ K q r := by positivity
  positivity

lemma product_le_four_one_add (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a * b * c ≤ 4 * (1 + a * b * (c + 1)) := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have habc : 0 ≤ a * b * c := mul_nonneg hab hc
  have habc₁ : a * b * c ≤ a * b * (c + 1) := by
    apply mul_le_mul_of_nonneg_left _ hab
    linarith
  have hone : 0 ≤ 1 + a * b * (c + 1) := by positivity
  calc
    a * b * c ≤ 1 + a * b * (c + 1) :=
      habc₁.trans (le_add_of_nonneg_left (by norm_num))
    _ = 1 * (1 + a * b * (c + 1)) := by ring
    _ ≤ 4 * (1 + a * b * (c + 1)) :=
      mul_le_mul_of_nonneg_right (by norm_num) hone

/-- Double-counting all edge--clique incidences converts pointwise initial
degree regularity into the matching total-clique estimate. -/
lemma initial_clique_count_abs_le
    {host H : Finset (Finset (Fin n))} {D b : ℝ}
    (hK : 0 < Nat.choose q r)
    (hhost : host ⊆ uniformEdges n r)
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (hdegree : ∀ e ∈ host,
      |((H.filter fun Q ↦ e ⊆ Q).card : ℝ) - D| ≤ b) :
    |(H.card : ℝ) - (host.card : ℝ) * D / Nat.choose q r| ≤
      (host.card : ℝ) * b / Nat.choose q r := by
  have hincidence :
      ∑ e ∈ host, ((H.filter fun Q ↦ e ⊆ Q).card : ℝ) =
        (Nat.choose q r : ℝ) * H.card := by
    have hsum := sum_availableDegree hH ([] : List (Finset (Fin n)))
    have hsumReal :
        (∑ e ∈ residualHost host r [],
          (availableDegree H r [] e : ℝ)) =
            (Nat.choose q r : ℝ) * (availableCliques H r []).card := by
      exact_mod_cast hsum
    calc
      (∑ e ∈ host, ((H.filter fun Q ↦ e ⊆ Q).card : ℝ)) =
          ∑ e ∈ host, (availableDegree H r [] e : ℝ) := by
            apply Finset.sum_congr rfl
            intro e he
            have hecard : e.card = r := mem_uniformEdges.mp (hhost he)
            simp [availableDegree, availableCliques, blockEdges,
              Finset.mem_powersetCard, hecard]
      _ = ∑ e ∈ residualHost host r [],
          (availableDegree H r [] e : ℝ) := by simp [residualHost]
      _ = (Nat.choose q r : ℝ) * (availableCliques H r []).card := hsumReal
      _ = _ := by simp [availableCliques]
  have hupper :
      ∑ e ∈ host, ((H.filter fun Q ↦ e ⊆ Q).card : ℝ) ≤
        (host.card : ℝ) * (D + b) := by
    calc
      _ ≤ ∑ _e ∈ host, (D + b) := by
        apply Finset.sum_le_sum
        intro e he
        have hd := hdegree e he
        have := (le_abs_self
          (((H.filter fun Q ↦ e ⊆ Q).card : ℝ) - D)).trans hd
        linarith
      _ = _ := by simp; ring
  have hlower :
      (host.card : ℝ) * (D - b) ≤
        ∑ e ∈ host, ((H.filter fun Q ↦ e ⊆ Q).card : ℝ) := by
    calc
      _ = ∑ _e ∈ host, (D - b) := by simp; ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro e he
        have hd := hdegree e he
        have := (neg_le_abs
          (((H.filter fun Q ↦ e ⊆ Q).card : ℝ) - D)).trans hd
        linarith
  rw [hincidence] at hupper hlower
  have hKR : (0 : ℝ) < Nat.choose q r := by exact_mod_cast hK
  rw [abs_le]
  constructor
  · rw [show (H.card : ℝ) - (host.card : ℝ) * D / Nat.choose q r =
        ((Nat.choose q r : ℝ) * H.card - (host.card : ℝ) * D) /
          Nat.choose q r by field_simp]
    have hn : -((host.card : ℝ) * b) ≤
        (Nat.choose q r : ℝ) * H.card - (host.card : ℝ) * D := by
      nlinarith [hlower]
    simpa [neg_div] using (div_le_div_iff_of_pos_right hKR).2 hn
  · rw [show (H.card : ℝ) - (host.card : ℝ) * D / Nat.choose q r =
        ((Nat.choose q r : ℝ) * H.card - (host.card : ℝ) * D) /
          Nat.choose q r by field_simp]
    have hn : (Nat.choose q r : ℝ) * H.card - (host.card : ℝ) * D ≤
        (host.card : ℝ) * b := by nlinarith [hupper]
    simpa using (div_le_div_iff_of_pos_right hKR).2 hn

lemma faceSlack_pos_of_pos (hn : 0 < n) (hscale : 0 < scale n q r) :
    0 < faceSlack n q r := by
  unfold faceSlack
  exact div_pos (by exact_mod_cast hn)
    (pow_pos (by exact_mod_cast hscale) _)

/-- The degree boost places all five concrete observables strictly inside
their initial windows.  This is separated from the drift calculation so the
finite instantiation stays below Lean's per-declaration elaboration budget. -/
lemma concrete_initial_barriers
    (hr : 0 < r) {host H : Finset (Finset (Fin n))}
    (hhost : host ⊆ uniformEdges n r)
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (hregular : ∀ e ∈ host,
      |((H.filter fun Q ↦ e ⊆ Q).card : ℝ) - centerDegree n q r| <
        initialError n q r / 4)
    (hgpos : 0 < host.card) (hKpos : 0 < K q r)
    (hIpos : 0 < initialError n q r)
    (hslackPos : 0 < faceSlack n q r)
    (jumpCap : BarrierIndex host r → ℝ)
    (hjumpNonneg : ∀ z, 0 ≤ jumpCap z) :
    ∀ z,
      barrierObservable host H r
          (upperProfile host.card n q r) (lowerProfile host.card n q r)
          (cliqueUpperProfile host.card n q r)
          (cliqueLowerProfile host.card n q r)
          (faceWeight host.card (K q r))
          (faceCap n (faceSlack n q r) (faceEps n q r)
            host.card (K q r)) z [] < 0 ∧
      barrierObservable host H r
          (upperProfile host.card n q r) (lowerProfile host.card n q r)
          (cliqueUpperProfile host.card n q r)
          (cliqueLowerProfile host.card n q r)
          (faceWeight host.card (K q r))
          (faceCap n (faceSlack n q r) (faceEps n q r)
            host.card (K q r)) z [] ≤
        -profileWindow host q r z + jumpCap z := by
  let g := host.card
  let I := initialError n q r
  let Y := barrierObservable host H r
    (upperProfile g n q r) (lowerProfile g n q r)
    (cliqueUpperProfile g n q r) (cliqueLowerProfile g n q r)
    (faceWeight g (K q r))
    (faceCap n (faceSlack n q r) (faceEps n q r) g (K q r))
  change ∀ z, Y z [] < 0 ∧ Y z [] ≤
    -profileWindow host q r z + jumpCap z
  have herrorZero : profileA n q r * centerDegree n q r = I := by
    dsimp [profileA, I, initialError]
    ring
  have hcliqueErrorZero :
      profileA n q r * (g : ℝ) * centerDegree n q r / K q r =
        (g : ℝ) * I / K q r := by
    rw [← herrorZero]
    ring
  have hupperZero : upperProfile g n q r 0 = centerDegree n q r + I := by
    unfold upperProfile
    rw [degreeUpper_zero hgpos, herrorZero]
  have hlowerZero : lowerProfile g n q r 0 = centerDegree n q r - I := by
    unfold lowerProfile
    rw [degreeLower_zero hgpos, herrorZero]
  have hcliqueUpperZero : cliqueUpperProfile g n q r 0 =
      (g : ℝ) * centerDegree n q r / K q r + (g : ℝ) * I / K q r := by
    unfold cliqueUpperProfile cliqueUpper
    rw [cliqueCenter_zero hgpos, cliqueError_zero hgpos, hcliqueErrorZero]
  have hcliqueLowerZero : cliqueLowerProfile g n q r 0 =
      (g : ℝ) * centerDegree n q r / K q r - (g : ℝ) * I / K q r := by
    unfold cliqueLowerProfile cliqueLower
    rw [cliqueCenter_zero hgpos, cliqueError_zero hgpos, hcliqueErrorZero]
  have hfaceZero : ∀ f : Finset (Fin n),
      faceWeight g (K q r) 0 * (residualFaceDegree host r [] f : ℝ) -
          faceCap n (faceSlack n q r) (faceEps n q r) g (K q r) 0 =
        (residualFaceDegree host r [] f : ℝ) -
          ((n : ℝ) + faceSlack n q r) := by
    intro f
    rw [faceWeight_zero hgpos, faceCap_zero hgpos]
    ring
  have hcountAbs :
      |(H.card : ℝ) - (g : ℝ) * centerDegree n q r / K q r| ≤
        (g : ℝ) * I / (4 * K q r) := by
    have hcount := initial_clique_count_abs_le
      (q := q) (r := r) (D := centerDegree n q r)
      (b := I / 4) hKpos hhost hH
      (fun e he ↦ (hregular e he).le)
    dsimp [g] at hcount ⊢
    simp only [K]
    convert hcount using 1 <;> ring
  intro z
  rcases z with (z | f)
  · rcases z with (eb | b)
    · rcases eb with ⟨e, b⟩
      have hecard : e.1.card = r := mem_uniformEdges.mp (hhost e.2)
      have hreg := hregular e.1 e.2
      change |((H.filter fun Q ↦ e.1 ⊆ Q).card : ℝ) -
        centerDegree n q r| < I / 4 at hreg
      cases b with
      | false =>
        have hobs : Y (Sum.inl (Sum.inl (e, false))) [] =
            ((H.filter fun Q ↦ e.1 ⊆ Q).card : ℝ) -
              (centerDegree n q r + I) := by
          simp [Y, barrierObservable, upperDegreeObservable,
            Erdos722.FrozenObservable.freezeValue,
            Erdos722.FrozenObservable.freezeAux, availableDegree,
            availableCliques, hupperZero,
            blockEdges, hecard]
        have hraw : ((H.filter fun Q ↦ e.1 ⊆ Q).card : ℝ) -
            centerDegree n q r < I / 4 :=
          (le_abs_self _).trans_lt hreg
        have hstrict : Y (Sum.inl (Sum.inl (e, false))) [] < 0 := by
          rw [hobs]
          linarith [hIpos]
        refine ⟨hstrict, ?_⟩
        have hwindow : Y (Sum.inl (Sum.inl (e, false))) [] ≤ -(I / 4) := by
          rw [hobs]
          linarith [hIpos]
        simpa [profileWindow, I] using
          hwindow.trans (le_add_of_nonneg_right (hjumpNonneg _))
      | true =>
        have hobs : Y (Sum.inl (Sum.inl (e, true))) [] =
            centerDegree n q r - I -
              ((H.filter fun Q ↦ e.1 ⊆ Q).card : ℝ) := by
          simp [Y, barrierObservable, lowerDegreeObservable,
            Erdos722.FrozenObservable.freezeValue,
            Erdos722.FrozenObservable.freezeAux, availableDegree,
            availableCliques, hlowerZero,
            blockEdges, hecard]
        have hraw : centerDegree n q r -
            ((H.filter fun Q ↦ e.1 ⊆ Q).card : ℝ) < I / 4 := by
          have habs := (neg_le_abs _).trans_lt hreg
          linarith
        have hstrict : Y (Sum.inl (Sum.inl (e, true))) [] < 0 := by
          rw [hobs]
          linarith [hIpos]
        refine ⟨hstrict, ?_⟩
        have hwindow : Y (Sum.inl (Sum.inl (e, true))) [] ≤ -(I / 4) := by
          rw [hobs]
          linarith [hIpos]
        simpa [profileWindow, I] using
          hwindow.trans (le_add_of_nonneg_right (hjumpNonneg _))
    · have hKreal : (0 : ℝ) < K q r := by exact_mod_cast hKpos
      let W : ℝ := (g : ℝ) * I / (4 * K q r)
      have hWpos : 0 < W := by
        dsimp [W, g, I]
        positivity
      have herrorFour : (g : ℝ) * I / K q r = 4 * W := by
        dsimp [W]
        field_simp [hKreal.ne'] <;> ring
      cases b with
      | false =>
        have hobs : Y (Sum.inl (Sum.inr false)) [] =
            (H.card : ℝ) -
              ((g : ℝ) * centerDegree n q r / K q r +
                (g : ℝ) * I / K q r) := by
          simp [Y, barrierObservable, cliqueObservable, availableCliques,
            hcliqueUpperZero]
        have hraw : (H.card : ℝ) -
            (g : ℝ) * centerDegree n q r / K q r ≤ W :=
          (le_abs_self _).trans (by simpa [W] using hcountAbs)
        have hstrict : Y (Sum.inl (Sum.inr false)) [] < 0 := by
          rw [hobs, herrorFour]
          linarith [hWpos]
        refine ⟨hstrict, ?_⟩
        have hwindow : Y (Sum.inl (Sum.inr false)) [] ≤ -W := by
          rw [hobs, herrorFour]
          linarith [hWpos]
        simpa [profileWindow, W, g, I] using
          hwindow.trans (le_add_of_nonneg_right (hjumpNonneg _))
      | true =>
        have hobs : Y (Sum.inl (Sum.inr true)) [] =
            (g : ℝ) * centerDegree n q r / K q r -
              (g : ℝ) * I / K q r - (H.card : ℝ) := by
          simp [Y, barrierObservable, cliqueObservable, availableCliques,
            hcliqueLowerZero]
        have hraw : (g : ℝ) * centerDegree n q r / K q r -
            (H.card : ℝ) ≤ W := by
          have habs := (neg_le_abs _).trans
            (by simpa [W] using hcountAbs)
          linarith
        have hstrict : Y (Sum.inl (Sum.inr true)) [] < 0 := by
          rw [hobs, herrorFour]
          linarith [hWpos]
        refine ⟨hstrict, ?_⟩
        have hwindow : Y (Sum.inl (Sum.inr true)) [] ≤ -W := by
          rw [hobs, herrorFour]
          linarith [hWpos]
        simpa [profileWindow, W, g, I] using
          hwindow.trans (le_add_of_nonneg_right (hjumpNonneg _))
  · have hfcard : f.1.card = r - 1 := mem_uniformEdges.mp f.2
    have hdeg := residualFaceDegree_le_n hr hhost
      ([] : List (Finset (Fin n))) hfcard
    have hobs : Y (Sum.inr f) [] =
        (residualFaceDegree host r [] f.1 : ℝ) -
          ((n : ℝ) + faceSlack n q r) := by
      simpa [Y, barrierObservable, weightedFaceObservable] using hfaceZero f.1
    have hwindow : Y (Sum.inr f) [] ≤ -faceSlack n q r := by
      rw [hobs]
      have hdegReal : (residualFaceDegree host r [] f.1 : ℝ) ≤ n := by
        exact_mod_cast hdeg
      linarith
    refine ⟨hwindow.trans_lt (neg_lt_zero.mpr hslackPos), ?_⟩
    have hhalf : Y (Sum.inr f) [] ≤ -(faceSlack n q r / 2) := by
      linarith
    simpa [profileWindow] using
      hhalf.trans (le_add_of_nonneg_right (hjumpNonneg _))

lemma hasBoundedNibble_of_leave_cap
    (hrq : r < q) {host : Finset (Finset (Fin n))}
    (h : ∃ blocks : Finset (Finset (Fin n)),
      IsCliquePacking host blocks q r ∧
      ∀ f : Finset (Fin n), f.card = r - 1 →
        Erdos722.Reserve.localDegree (leave host blocks r) f ≤
          Erdos722.CoverAsymptotic.coverLeaveCap q r n) :
    HasBoundedNibble host q r
      (Erdos722.CoverAsymptotic.coverDen q r)
      (Erdos722.CoverAsymptotic.coverLeaveNumerator q r) := by
  obtain ⟨blocks, hpack, hdegree⟩ := h
  refine ⟨blocks, hpack, ?_⟩
  intro J hJ
  calc
    (Erdos722.Reserve.localDegree (leave host blocks r) J) ^
        Erdos722.CoverAsymptotic.coverDen q r ≤
      (Erdos722.CoverAsymptotic.coverLeaveCap q r n) ^
        Erdos722.CoverAsymptotic.coverDen q r :=
      Nat.pow_le_pow_left (hdegree J hJ) _
    _ ≤ n ^ Erdos722.CoverAsymptotic.coverLeaveNumerator q r := by
      exact Erdos722.Asymptotics.rationalPowerThreshold_pow_le
        (Erdos722.CoverAsymptotic.coverLeaveNumerator q r)
        (Erdos722.CoverAsymptotic.coverDen q r) n
        (Erdos722.CoverAsymptotic.coverDen_pos hrq.le)

def UpperScalarCondition
    (host : Finset (Finset (Fin n))) (g q r dpth : ℕ) : Prop :=
  ∀ i < dpth, ∀ (e : HostEdge host) (x M : ℕ),
    lowerNat g n q r i ≤ x → x ≤ upperNat g n q r i → x ≤ M →
    cliqueLowerProfile g n q r i ≤ (M : ℝ) →
    (M : ℝ) ≤ cliqueUpperProfile g n q r i →
    -profileWindow host q r (Sum.inl (Sum.inl (e, false))) ≤
        (x : ℝ) - upperProfile g n q r i →
    (0 : ℝ) ≤
      ((x * (K q r - 1) *
        (lowerNat g n q r i - n ^ (q - r - 1)) : ℕ) : ℝ) -
      ((x * (K q r - 1) ^ 2 * n ^ (q - r - 1) : ℕ) : ℝ) +
      ((M - x : ℕ) : ℝ) *
        (upperProfile g n q r (i + 1) - upperProfile g n q r i)

def LowerScalarCondition
    (host : Finset (Finset (Fin n))) (g q r dpth : ℕ) : Prop :=
  ∀ i < dpth, ∀ (e : HostEdge host) (x M : ℕ),
    lowerNat g n q r i ≤ x → x ≤ upperNat g n q r i → x ≤ M →
    cliqueLowerProfile g n q r i ≤ (M : ℝ) →
    (M : ℝ) ≤ cliqueUpperProfile g n q r i →
    -profileWindow host q r (Sum.inl (Sum.inl (e, true))) ≤
        lowerProfile g n q r i - (x : ℝ) →
    (((x * (K q r - 1) * upperNat g n q r i : ℕ) : ℝ) +
      ((M - x : ℕ) : ℝ) *
        (lowerProfile g n q r (i + 1) - lowerProfile g n q r i)) ≤ 0

def CliqueUpperScalarCondition (g n q r dpth : ℕ) : Prop :=
  ∀ i < dpth,
    (0 : ℝ) ≤
      (((K q r) * lowerNat g n q r i : ℕ) : ℝ) -
      ((((K q r) ^ 2 * n ^ (q - r - 1) : ℕ)) : ℝ) +
      (cliqueUpperProfile g n q r (i + 1) -
        cliqueUpperProfile g n q r i)

def CliqueLowerScalarCondition (g n q r dpth : ℕ) : Prop :=
  ∀ i < dpth,
    (((K q r) * upperNat g n q r i : ℕ) : ℝ) +
      (cliqueLowerProfile g n q r (i + 1) -
        cliqueLowerProfile g n q r i) ≤ 0

/-- All four scalar drift inequalities for the concrete profiles. -/
lemma concrete_scalar_conditions
    {host : Finset (Finset (Fin n))} {g dpth : ℕ}
    (hgpos : 0 < g) (hKq : 2 < K q r)
    (hstep : ∀ i < dpth, K q r * (i + 1) < g)
    (hprofiles : ∀ i < dpth,
      0 ≤ lowerProfile g n q r i ∧ 0 ≤ upperProfile g n q r i)
    (hinitialCurrent : ∀ i < dpth, initialError n q r ≤
      degreeError (profileA n q r) (centerDegree n q r) g (K q r) i)
    (herrorSmall : ∀ i < dpth,
      16 * (K q r : ℝ) *
          degreeError (profileA n q r) (centerDegree n q r) g (K q r) i ≤
        degreeCenter (centerDegree n q r) g (K q r) i)
    (hKCL : ∀ i < dpth,
      K q r * n ^ (q - r - 1) ≤ lowerNat g n q r i)
    (hCpos : 0 < n ^ (q - r - 1))
    (hcenterCost : ∀ i < dpth,
      (K q r : ℝ) *
          (degreeCenter (centerDegree n q r) g (K q r) i -
            degreeCenter (centerDegree n q r) g (K q r) (i + 1)) ≤
        degreeError (profileA n q r) (centerDegree n q r) g (K q r) i / 2)
    (hround : ∀ i < dpth,
      (2 * K q r : ℕ) ≤
        degreeError (profileA n q r) (centerDegree n q r) g (K q r) i)
    (hremainingStep : ∀ i < dpth,
      (6 : ℝ) * (4 * (K q r : ℝ) - 1) * K q r *
          (2 : ℝ) ^ (4 * K q r - 2) ≤ remaining g (K q r) (i + 1))
    (hmargin : (4 : ℝ) *
      (1 + (K q r : ℝ) * (K q r + 1) *
        ((n : ℝ) ^ (q - r - 1) + 1)) ≤ initialError n q r) :
    UpperScalarCondition host g q r dpth ∧
    LowerScalarCondition host g q r dpth ∧
    CliqueUpperScalarCondition g n q r dpth ∧
    CliqueLowerScalarCondition g n q r dpth := by
  let C := n ^ (q - r - 1)
  let I := initialError n q r
  have hKpos : 0 < K q r := by omega
  have hKthree : 3 ≤ K q r := by omega
  have hUpper : UpperScalarCondition host g q r dpth := by
    intro i hi e x M hxL hxU hxM _hMlower hMupper hcritical
    let E := degreeError (profileA n q r) (centerDegree n q r) g (K q r) i
    let Z := degreeCenter (centerDegree n q r) g (K q r) i
    have hIE : I ≤ E := by simpa [E, I] using hinitialCurrent i hi
    have hEZ : E ≤ Z := by
      have hs := herrorSmall i hi
      have hE0 : 0 ≤ E := by
        have hx' := density_pos hgpos (Nat.mul_le_mul_left (K q r)
          (by omega : i ≤ i + 1) |>.trans_lt (hstep i hi))
        dsimp [E]
        unfold degreeError profileA centerDegree
        positivity
      have hKR : (3 : ℝ) ≤ K q r := by exact_mod_cast hKthree
      simpa [E, Z] using (show E ≤ Z by nlinarith)
    have hcost : 4 * (1 + (K q r : ℝ) * C) ≤ E := by
      have hm : (4 : ℝ) *
          (1 + (K q r : ℝ) * (K q r + 1) * ((C : ℝ) + 1)) ≤ I := by
        dsimp [I, C]
        simpa only [Nat.cast_pow] using hmargin
      have hKR : (3 : ℝ) ≤ K q r := by exact_mod_cast hKthree
      have hCR : (0 : ℝ) ≤ C := by positivity
      nlinarith [mul_nonneg hCR (sub_nonneg.mpr hKR)]
    have hwindow0 : 0 ≤ upperProfile g n q r i - I / 4 := by
      change 0 ≤ Z + E - I / 4
      have hZ0 : 0 ≤ Z := by
        have hd : 0 < density g (K q r) i :=
          density_pos hgpos (Nat.mul_le_mul_left (K q r)
            (by omega : i ≤ i + 1) |>.trans_lt (hstep i hi))
        dsimp [Z]
        unfold degreeCenter centerDegree
        positivity
      nlinarith
    have hI0 : 0 ≤ I := by
      have hm : (4 : ℝ) *
          (1 + (K q r : ℝ) * (K q r + 1) * ((C : ℝ) + 1)) ≤ I := by
        dsimp [I, C]
        simpa only [Nat.cast_pow] using hmargin
      exact (mul_nonneg (by norm_num) (by positivity)).trans hm
    have hwindowE : I / 4 ≤ E / 4 :=
      div_le_div_of_nonneg_right hIE (by norm_num)
    have hprof := upperEdge_profile_scalar_of_error_margin
      (n := n) (q := q) (r := r) (i := i) (C := C)
      (window := I / 4) hgpos hKq (hstep i hi)
      (div_nonneg hI0 (by norm_num))
      (by simpa [E] using hwindowE)
      (by simpa [E, Z] using hEZ) (by simpa [E] using hcost)
    rw [Nat.cast_sub (by omega : 1 ≤ K q r), Nat.cast_one] at hprof
    exact Erdos722.NibbleScalar.upper_edge_scalar_of_profile
      (K := K q r) (C := C) hKpos (hKCL i hi) hxM hwindow0
      (by simpa [UpperScalarCondition, profileWindow, I, C] using hcritical)
      hMupper hprof
  have hLowerDelta : ∀ i < dpth,
      lowerProfile g n q r (i + 1) - lowerProfile g n q r i ≤ 0 := by
    intro i hi
    have hd := lowerProfile_sub_succ_ge
      (n := n) (q := q) (r := r) (i := i) hgpos (hstep i hi)
    have hnonneg : 0 ≤
        centerDegree n q r *
            (((K q r - 1 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
              density g (K q r) (i + 1) ^ (K q r - 2)) +
          degreeErrorGrowth g n q r i := by
      have hD : 0 ≤ centerDegree n q r := by
        unfold centerDegree
        positivity
      have hnext : 0 < density g (K q r) (i + 1) :=
        density_pos hgpos (hstep i hi)
      have hcur : 0 < density g (K q r) i :=
        density_pos hgpos (Nat.mul_le_mul_left (K q r)
          (by omega : i ≤ i + 1) |>.trans_lt (hstep i hi))
      have hfactor : 0 ≤
          (((K q r - 1 : ℕ) : ℝ) * ((K q r : ℝ) / g) *
            density g (K q r) (i + 1) ^ (K q r - 2)) := by
        positivity
      exact add_nonneg (mul_nonneg hD hfactor)
        (degreeErrorGrowth_nonneg g n q r i hcur.le hnext.le)
    linarith
  have hLower : LowerScalarCondition host g q r dpth := by
    intro i hi _e x M _hxL hxU hxM hMlower _hMupper _hcritical
    have hprof := lowerEdge_profile_scalar_of_host_margin
      (n := n) (q := q) (r := r) (i := i) hgpos hKq (hstep i hi)
      (hcenterCost i hi) (herrorSmall i hi) (hround i hi)
      (hremainingStep i hi)
    rw [Nat.cast_sub (by omega : 1 ≤ K q r), Nat.cast_one] at hprof
    exact Erdos722.NibbleScalar.lower_edge_scalar_of_profile
      (K := K q r) hKpos hxU hxM hMlower (hLowerDelta i hi) hprof
  have hCliqueUpper : CliqueUpperScalarCondition g n q r dpth := by
    intro i hi
    have hIE := hinitialCurrent i hi
    let C₀ := n ^ (q - r - 1)
    have hC0 : (0 : ℝ) ≤ C₀ := by positivity
    have hreq : (K q r : ℝ) * (K q r + 1) * C₀ ≤
        degreeError (profileA n q r) (centerDegree n q r) g (K q r) i := by
      have hm : (4 : ℝ) *
          (1 + (K q r : ℝ) * (K q r + 1) * ((C₀ : ℝ) + 1)) ≤
            initialError n q r := by
        dsimp [C₀]
        simpa only [Nat.cast_pow] using hmargin
      exact (product_le_four_one_add (K q r) (K q r + 1) C₀
        (by positivity) (by positivity) hC0).trans (hm.trans hIE)
    have hprof := cliqueUpper_scalar_of_error_margin
      (n := n) (q := q) (r := r) (i := i) (C := C₀)
      hgpos hKq (by simpa [C₀] using hCpos) (hstep i hi) hreq
    exact Erdos722.NibbleScalar.clique_upper_scalar_of_profile
      (K := K q r) (C := C₀) (L := lowerNat g n q r i)
      (hprofiles i hi).1 hprof rfl
  have hCliqueLower : CliqueLowerScalarCondition g n q r dpth := by
    intro i hi
    have hprof := cliqueLower_scalar_of_error_margins
      (n := n) (q := q) (r := r) (i := i) hgpos hKq (hstep i hi)
      (hcenterCost i hi) (hround i hi)
    exact Erdos722.NibbleScalar.clique_lower_scalar_of_profile
      (K := K q r) (U := upperNat g n q r i)
      (hprofiles i hi).2 hprof rfl
  exact ⟨hUpper, hLower, hCliqueUpper, hCliqueLower⟩

/-- Concrete finite instantiation.  All profile drift and initial-state
hypotheses are discharged here; only pointwise jump domination and the
single indexed exponential sum remain as quantitative concentration input. -/
theorem exists_boundedNibble_of_quantitative
    (hr : 1 < r) (hrq : r < q)
    {host H : Finset (Finset (Fin n))}
    (hhost : host ⊆ uniformEdges n r)
    (hH : ∀ Q ∈ H, Q.card = q ∧ blockEdges r Q ⊆ host)
    (hregular : ∀ e ∈ host,
      |((H.filter fun Q ↦ e ⊆ Q).card : ℝ) - centerDegree n q r| <
        initialError n q r / 4)
    (hhalf : Nat.choose n r / 2 < host.card)
    (hT : 64 * K q r ≤ scale n q r)
    (hpower : (scale n q r : ℝ) ^ K q r ≤ centerDegree n q r)
    (htarget : stopTarget host.card n q r ≤ host.card)
    (hhostScale :
      2 * (K q r : ℝ) ^ 2 * (K q r - 1 : ℕ) *
          (scale n q r : ℝ) ^ (5 * K q r - 1) ≤ host.card)
    (hremaining :
      (6 : ℝ) * (4 * (K q r : ℝ) - 1) * K q r *
          (2 : ℝ) ^ (4 * K q r - 2) ≤ stopTarget host.card n q r)
    (hmargin :
      (4 : ℝ) *
          (1 + (K q r : ℝ) * (K q r + 1) *
            ((n : ℝ) ^ (q - r - 1) + 1)) ≤ initialError n q r)
    (jumpCap rate : BarrierIndex host r → ℝ)
    (hjumpNonneg : ∀ z, 0 ≤ jumpCap z)
    (hjumpLt : ∀ z, jumpCap z < profileWindow host q r z)
    (hjump : ∀ z i, i < depth host.card n q r →
      barrierJump host q r
          (upperProfile host.card n q r) (lowerProfile host.card n q r)
          (cliqueUpperProfile host.card n q r)
          (cliqueLowerProfile host.card n q r)
          (faceWeight host.card (K q r))
          (faceCap n (faceSlack n q r) (faceEps n q r)
            host.card (K q r))
          (upperNat host.card n q r) z i ≤ jumpCap z)
    (hrate : ∀ z, 0 < rate z)
    (hrateJump : ∀ z, rate z * jumpCap z ≤ 1)
    (hsmall :
      (∑ z : BarrierIndex host r × Fin (depth host.card n q r + 1),
        Real.exp (-rate z.1 *
            (profileWindow host q r z.1 - jumpCap z.1)) *
          Real.exp ((rate z.1) ^ 2 * varianceBudget
            (concreteVariance host q r z.1) 0
              (depth host.card n q r))) < 1)
    (hfaceTerminal :
      faceCap n (faceSlack n q r) (faceEps n q r)
          host.card (K q r) (depth host.card n q r) ≤
        faceWeight host.card (K q r) (depth host.card n q r) *
          Erdos722.CoverAsymptotic.coverLeaveCap q r n) :
    HasBoundedNibble host q r
      (Erdos722.CoverAsymptotic.coverDen q r)
      (Erdos722.CoverAsymptotic.coverLeaveNumerator q r) := by
  let g := host.card
  let T := scale n q r
  let K₀ := K q r
  let C₀ := n ^ (q - r - 1)
  let I := initialError n q r
  let dpth := depth g n q r
  have hKthree : 3 ≤ K₀ := K_ge_three hr hrq
  have hKq : 2 < K q r := by
    have := K_ge_three hr hrq
    omega
  have hKpos : 0 < K₀ := by omega
  have hgpos : 0 < g := by
    dsimp [g]
    omega
  have hTpos : 0 < T := by
    dsimp [T]
    omega
  have hTfour : 4 ≤ T := by
    dsimp [T, K₀] at hT ⊢
    omega
  have htargetPos : 0 < stopTarget g n q r := by
    dsimp [stopTarget]
    omega
  have hstep : ∀ i < dpth, K₀ * (i + 1) < g := by
    intro i hi
    exact mul_succ_lt_of_lt_depth hKpos htargetPos
      (by simpa [dpth, g, K₀, depth] using hi)
  have hlowerDensity : ∀ i < dpth,
      1 / (T : ℝ) ≤ density g K₀ i := by
    intro i hi
    apply one_div_scale_le_density hgpos hKpos hTpos
      (by simpa [g] using htarget)
    simpa [dpth, g] using (Nat.le_of_lt hi)
  have hdensityPos : ∀ i < dpth, 0 < density g K₀ i := by
    intro i hi
    have hii : K₀ * i ≤ K₀ * (i + 1) := Nat.mul_le_mul_left _ (by omega)
    exact density_pos hgpos (hii.trans_lt (hstep i hi))
  have hdensityUpper : ∀ i < dpth, density g K₀ i ≤ 1 := by
    intro i hi
    exact density_le_one_of_mul_le hgpos (Nat.le_of_lt
      ((Nat.mul_lt_mul_left hKpos).2 (by omega : i < i + 1) |>.trans (hstep i hi)))
  have hprofiles : ∀ i < dpth,
      0 ≤ lowerProfile g n q r i ∧ 0 ≤ upperProfile g n q r i := by
    intro i hi
    exact degreeProfiles_nonneg (by omega) hTfour
      (hdensityPos i hi) (hlowerDensity i hi)
  have hcenter : ∀ i < dpth,
      (T : ℝ) ≤ degreeCenter (centerDegree n q r) g K₀ i := by
    intro i hi
    exact scale_le_degreeCenter hKpos hTpos (hlowerDensity i hi)
      (by simpa [T, K₀] using hpower)
  have hratioData : ∀ i < dpth,
      0 < upperNat g n q r i ∧
        lowerNat g n q r i ≤ upperNat g n q r i ∧
        1 - (lowerNat g n q r i : ℝ) / upperNat g n q r i ≤
          faceEps n q r := by
    intro i hi
    exact lowerNat_upperNat_ratio (by omega) hTfour
      (hdensityPos i hi) (hlowerDensity i hi) (hcenter i hi)
  have hinitialCurrent : ∀ i < dpth, I ≤
      degreeError (profileA n q r) (centerDegree n q r) g K₀ i := by
    intro i hi
    simpa [I, initialError, K₀] using initial_degreeError_le hKpos hTpos
      (hdensityPos i hi) (hdensityUpper i hi)
  have herrorSmall : ∀ i < dpth,
      16 * (K₀ : ℝ) *
          degreeError (profileA n q r) (centerDegree n q r) g K₀ i ≤
        degreeCenter (centerDegree n q r) g K₀ i := by
    intro i hi
    let E := degreeError (profileA n q r) (centerDegree n q r) g K₀ i
    let Z := degreeCenter (centerDegree n q r) g K₀ i
    have hEZ := degreeError_le_center_div_scale (by omega) hTpos
      (hdensityPos i hi) (hlowerDensity i hi)
    change E ≤ Z / T at hEZ
    have hTR : (16 * (K₀ : ℝ) : ℝ) ≤ T := by
      dsimp [T, K₀]
      exact_mod_cast (show 16 * K q r ≤ scale n q r by omega)
    have hTreal : (0 : ℝ) < T := by exact_mod_cast hTpos
    have hE0 : 0 ≤ E := by
      have hx := hdensityPos i hi
      have htr : (0 : ℝ) < T := by exact_mod_cast hTpos
      dsimp [E]
      unfold degreeError profileA centerDegree
      positivity
    have := (le_div_iff₀ hTreal).mp hEZ
    nlinarith
  have hround : ∀ i < dpth,
      (2 * K₀ : ℕ) ≤
        degreeError (profileA n q r) (centerDegree n q r) g K₀ i := by
    intro i hi
    have hm := hinitialCurrent i hi
    have hmargin' : (4 : ℝ) *
        (1 + (K₀ : ℝ) * (K₀ + 1) * ((C₀ : ℝ) + 1)) ≤ I := by
      simpa [K₀, C₀, I] using hmargin
    have hreal : ((2 * K₀ : ℕ) : ℝ) ≤ I := by
      push_cast
      have hC0 : (0 : ℝ) ≤ C₀ := by positivity
      nlinarith
    exact_mod_cast hreal.trans hm
  have hnlarge : r ≤ n := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hgpos
    have hecard : e.card = r := mem_uniformEdges.mp (hhost he)
    have hcard : e.card ≤ n := by
      simpa using e.card_le_univ
    omega
  have hCpos : 0 < C₀ := by
    dsimp [C₀]
    exact pow_pos (by omega) _
  have hcenterCost : ∀ i < dpth,
      (K₀ : ℝ) *
          (degreeCenter (centerDegree n q r) g K₀ i -
            degreeCenter (centerDegree n q r) g K₀ (i + 1)) ≤
        degreeError (profileA n q r) (centerDegree n q r) g K₀ i / 2 := by
    intro i hi
    exact degreeCenter_step_cost_le_half_error hgpos (by omega) hTpos
      (hstep i hi) (hdensityUpper i hi)
      (by simpa [g, T, K₀] using hhostScale)
  have hremainingStep : ∀ i < dpth,
      (6 : ℝ) * (4 * (K₀ : ℝ) - 1) * K₀ *
          (2 : ℝ) ^ (4 * K₀ - 2) ≤ remaining g K₀ (i + 1) := by
    intro i hi
    have hiDepth : i + 1 ≤ dpth := by omega
    have hremDepth : stopTarget g n q r ≤ g - K₀ * dpth := by
      simpa [dpth, depth] using remaining_depth_lower hKpos
        (by simpa [g] using htarget)
    have hmono : g - K₀ * dpth ≤ g - K₀ * (i + 1) := by
      exact Nat.sub_le_sub_left (Nat.mul_le_mul_left K₀ hiDepth) g
    have hnat := hremDepth.trans hmono
    have hreal : (stopTarget g n q r : ℝ) ≤
        (g : ℝ) - K₀ * (i + 1) := by
      have hmul : K₀ * (i + 1) ≤ g := (hstep i hi).le
      exact_mod_cast hnat
    have hbase :
        (6 : ℝ) * (4 * (K₀ : ℝ) - 1) * K₀ *
            (2 : ℝ) ^ (4 * K₀ - 2) ≤ stopTarget g n q r := by
      simpa [K₀, g] using hremaining
    exact hbase.trans (by simpa [remaining] using hreal)
  have hKCL : ∀ i < dpth, K₀ * C₀ ≤ lowerNat g n q r i := by
    intro i hi
    let E := degreeError (profileA n q r) (centerDegree n q r) g K₀ i
    let Z := degreeCenter (centerDegree n q r) g K₀ i
    have hZE : 16 * (K₀ : ℝ) * E ≤ Z := by
      simpa [E, Z] using herrorSmall i hi
    have hEI : I ≤ E := by simpa [E] using hinitialCurrent i hi
    have hm : (4 : ℝ) *
        (1 + (K₀ : ℝ) * (K₀ + 1) * ((C₀ : ℝ) + 1)) ≤ I := by
      simpa [I, K₀, C₀] using hmargin
    apply Nat.le_floor
    change ((K₀ * C₀ : ℕ) : ℝ) ≤ lowerProfile g n q r i
    push_cast
    change (K₀ : ℝ) * (C₀ : ℝ) ≤ Z - E
    have hE0 : 0 ≤ E := by
      have hx := hdensityPos i hi
      have htr : (0 : ℝ) < T := by exact_mod_cast hTpos
      dsimp [E]
      unfold degreeError profileA centerDegree
      positivity
    have hKR : (3 : ℝ) ≤ K₀ := by exact_mod_cast hKthree
    have hCR : (0 : ℝ) ≤ C₀ := by positivity
    have haux : (K₀ : ℝ) * C₀ ≤ 4 *
        (1 + (K₀ : ℝ) * (K₀ + 1) * ((C₀ : ℝ) + 1)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hKR) hCR]
    have hKone : (1 : ℝ) ≤ 16 * K₀ - 1 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hKone) hE0]
  have hcliqueLowerPos : ∀ i < dpth,
      0 < cliqueLowerProfile g n q r i := by
    intro i hi
    have hLpos : 0 < lowerNat g n q r i :=
      lt_of_lt_of_le (Nat.mul_pos hKpos hCpos) (hKCL i hi)
    have hlowerPos : 0 < lowerProfile g n q r i := by
      have hfloor := lowerNat_le_lowerProfile g n q r i (hprofiles i hi).1
      exact (by exact_mod_cast hLpos : (0 : ℝ) < lowerNat g n q r i).trans_le hfloor
    rw [cliqueLowerProfile_eq_remaining_mul hgpos (by omega)
      (lt_of_le_of_lt (Nat.mul_le_mul_left K₀ (Nat.le_succ i)) (hstep i hi))]
    exact mul_pos (div_pos (remaining_pos
      (lt_of_le_of_lt (Nat.mul_le_mul_left K₀ (Nat.le_succ i)) (hstep i hi)))
      (by exact_mod_cast hKpos)) hlowerPos
  have hScalars := concrete_scalar_conditions
    (n := n) (q := q) (r := r) (host := host) (g := g) (dpth := dpth)
    hgpos hKq hstep hprofiles hinitialCurrent herrorSmall hKCL hCpos
    hcenterCost hround hremainingStep hmargin
  have hUpperScalar := hScalars.1
  have hLowerScalar := hScalars.2.1
  have hCliqueUpperScalar := hScalars.2.2.1
  have hCliqueLowerScalar := hScalars.2.2.2
  have hIpos : 0 < I := by
    have hbase : (0 : ℝ) < 4 *
        (1 + (K q r : ℝ) * (K q r + 1) *
          ((n : ℝ) ^ (q - r - 1) + 1)) := by positivity
    exact hbase.trans_le hmargin
  have hnpos : 0 < n := by omega
  have hslackPos : 0 < faceSlack n q r :=
    faceSlack_pos_of_pos hnpos (by simpa [T] using hTpos)
  have hInitial := concrete_initial_barriers
    (n := n) (q := q) (r := r) (host := host) (H := H)
    (by omega : 0 < r) hhost hH hregular hgpos hKpos hIpos
    hslackPos jumpCap hjumpNonneg
  apply hasBoundedNibble_of_leave_cap hrq
  exact exists_packing_faceDegree_le_of_finite_profiles
    (n := n) (q := q) (r := r) (host := host) (H := H)
    (by omega : 0 < r) hrq hhost hH
    (upperProfile g n q r) (lowerProfile g n q r)
    (cliqueUpperProfile g n q r) (cliqueLowerProfile g n q r)
    (upperNat g n q r) (lowerNat g n q r)
    (faceSlack n q r) (faceEps n q r)
    (profileWindow host q r) jumpCap
    (depth := dpth) hKpos hgpos hstep
    (fun i hi ↦ (hratioData i hi).1)
    (fun i hi ↦ upperProfile_le_upperNat g n q r i (hprofiles i hi).2)
    (fun i hi ↦ lowerNat_le_lowerProfile g n q r i (hprofiles i hi).1)
    (fun i hi ↦ (hratioData i hi).2.1)
    hcliqueLowerPos (fun i hi ↦ (hratioData i hi).2.2)
    hUpperScalar hLowerScalar hCliqueUpperScalar hCliqueLowerScalar
    hjump hjumpNonneg hjumpLt hInitial rate hrate hrateJump hsmall
    (B := Erdos722.CoverAsymptotic.coverLeaveCap q r n) hfaceTerminal

end

end Erdos722.NibbleInstantiation
