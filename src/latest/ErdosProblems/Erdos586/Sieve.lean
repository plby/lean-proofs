/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib

/-!
# The abstract distortion-sieve recurrence for Erdős Problem 586

This file separates the real-algebra part of the Balister--Bollobás--Morris--
Sahasrabudhe--Tiba argument from the congruence and moment calculations.  Its
inputs are the first/second-moment stage bounds; its outputs are positivity of
the remaining mass, the normalized recurrence, transport through an exact
rounded certificate, and the reciprocal envelope used for the analytic tail.

No fact in this file is specific to the concrete list of moduli.
-/

open scoped BigOperators

namespace Erdos586

noncomputable section

/-! ## A finite non-covering criterion -/

/-- Mass of an event for an explicitly represented finite weight function. -/
noncomputable def sieveMass {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (S : Set Ω) : ℝ := by
  classical
  exact ∑ ω, if ω ∈ S then weight ω else 0

/-- If the sum of the masses of finitely many events is less than one, some
point lies in none of the events.  This is the finite union bound in the exact
form used at the end of the sieve. -/
theorem exists_outside_of_sum_mass_lt_one
    {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (weight : Ω → ℝ) (hweight : ∀ ω, 0 ≤ weight ω)
    (hweightsum : ∑ ω, weight ω = 1)
    (B : ι → Set Ω) (s : Finset ι)
    (hsmall : (∑ i ∈ s, sieveMass weight (B i)) < 1) :
    ∃ ω : Ω, ∀ i ∈ s, ω ∉ B i := by
  classical
  by_contra h
  push_neg at h
  have hpoint : ∀ ω : Ω,
      weight ω ≤ ∑ i ∈ s, if ω ∈ B i then weight ω else 0 := by
    intro ω
    obtain ⟨i, hi, hωi⟩ := h ω
    calc
      weight ω = (if ω ∈ B i then weight ω else 0) := by simp [hωi]
      _ ≤ ∑ j ∈ s, if ω ∈ B j then weight ω else 0 := by
        let g : ι → ℝ := fun j ↦ if ω ∈ B j then weight ω else 0
        have hg : ∀ j ∈ s, 0 ≤ g j := by
          intro j hj
          simp only [g]
          split_ifs
          · exact hweight ω
          · exact le_rfl
        exact Finset.single_le_sum hg hi
  have htotal :
      (∑ ω : Ω, weight ω) ≤
        ∑ ω : Ω, ∑ i ∈ s, if ω ∈ B i then weight ω else 0 := by
    exact Finset.sum_le_sum fun ω _ ↦ hpoint ω
  have hreorder :
      (∑ ω : Ω, ∑ i ∈ s, if ω ∈ B i then weight ω else 0) =
        ∑ i ∈ s, sieveMass weight (B i) := by
    rw [Finset.sum_comm]
    simp only [sieveMass]
  rw [hweightsum, hreorder] at htotal
  exact (not_lt_of_ge htotal) hsmall

/-- The bookkeeping form used by the final stage: if `remaining` is one minus
the sum of the final masses of all processed events and is positive, there is
an uncovered point. -/
theorem positive_remaining_gives_uncovered
    {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (weight : Ω → ℝ) (hweight : ∀ ω, 0 ≤ weight ω)
    (hweightsum : ∑ ω, weight ω = 1)
    (B : ι → Set Ω) (s : Finset ι)
    (remaining : ℝ)
    (hremaining : remaining =
      1 - ∑ i ∈ s, sieveMass weight (B i))
    (hpositive : 0 < remaining) :
    ∃ ω : Ω, ∀ i ∈ s, ω ∉ B i := by
  apply exists_outside_of_sum_mass_lt_one weight hweight hweightsum B s
  linarith

/-- Union-bound bookkeeping when the recursively accumulated stage costs are
only upper bounds for the masses of the corresponding final events. -/
theorem positive_cost_budget_gives_uncovered
    {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (weight : Ω → ℝ) (hweight : ∀ ω, 0 ≤ weight ω)
    (hweightsum : ∑ ω, weight ω = 1)
    (B : ι → Set Ω) (s : Finset ι) (cost : ι → ℝ)
    (hmass : ∀ i ∈ s, sieveMass weight (B i) ≤ cost i)
    (hpositive : 0 < 1 - ∑ i ∈ s, cost i) :
    ∃ ω : Ω, ∀ i ∈ s, ω ∉ B i := by
  apply exists_outside_of_sum_mass_lt_one weight hweight hweightsum B s
  have hsum : (∑ i ∈ s, sieveMass weight (B i)) ≤ ∑ i ∈ s, cost i := by
    exact Finset.sum_le_sum fun i hi ↦ hmass i hi
  linarith

/-! ## The normalized one-step recurrence -/

/-- The numerator coefficient occurring in the second-moment Euler factor. -/
def stageA (p : ℝ) : ℝ := (3 * p - 1) / (p - 1) ^ 2

/-- The coefficient which converts the second moment into a distortion cost. -/
def stageB (p : ℝ) : ℝ := 1 / (4 * (p - 1) ^ 2)

/-- The Euler factor added at a stage with distortion parameter `δ`. -/
def sieveFactor (p δ : ℝ) : ℝ := 1 + stageA p / (1 - δ)

/-- The fraction of the old remaining mass which the second-moment estimate
allows the current stage to remove. -/
def lossRatio (p δ x : ℝ) : ℝ := stageB p * x / (δ * (1 - δ))

/-- The normalized BBMST recurrence map. -/
def recurrenceMap (p δ x : ℝ) : ℝ :=
  x * sieveFactor p δ / (1 - lossRatio p δ x)

lemma stageA_nonneg {p : ℝ} (hp : 1 < p) : 0 ≤ stageA p := by
  unfold stageA
  apply div_nonneg
  · linarith
  · positivity

lemma stageB_pos {p : ℝ} (hp : 1 < p) : 0 < stageB p := by
  unfold stageB
  apply one_div_pos.mpr
  have : 0 < (p - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hp)
  positivity

lemma sieveFactor_pos {p δ : ℝ} (hp : 1 < p) (hδ : δ < 1) :
    0 < sieveFactor p δ := by
  unfold sieveFactor
  have hA := stageA_nonneg hp
  have : 0 ≤ stageA p / (1 - δ) := div_nonneg hA (by linarith)
  linarith

lemma lossRatio_nonneg {p δ x : ℝ} (hp : 1 < p) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) (hx : 0 ≤ x) : 0 ≤ lossRatio p δ x := by
  unfold lossRatio
  apply div_nonneg
  · exact mul_nonneg (stageB_pos hp).le hx
  · exact mul_nonneg hδ0.le (sub_nonneg.mpr hδ1.le)

/-- The elementary monotonicity of `x / (1-cx)` on its positive-denominator
domain.  Stating it independently keeps all later certificate transport free
of calculus. -/
lemma linearFraction_mono {c x y : ℝ}
    (hc : 0 ≤ c) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : c * y < 1) :
    x / (1 - c * x) ≤ y / (1 - c * y) := by
  have hcx : c * x ≤ c * y := mul_le_mul_of_nonneg_left hxy hc
  have hdenx : 0 < 1 - c * x := by linarith
  have hdeny : 0 < 1 - c * y := by linarith
  rw [div_le_div_iff₀ hdenx hdeny]
  nlinarith

/-- The normalized recurrence is monotone in its incoming bound throughout
the valid denominator domain. -/
theorem recurrenceMap_mono {p δ x y : ℝ}
    (hp : 1 < p) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hy : lossRatio p δ y < 1) :
    recurrenceMap p δ x ≤ recurrenceMap p δ y := by
  let c : ℝ := stageB p / (δ * (1 - δ))
  have hc : 0 ≤ c := by
    dsimp [c]
    exact div_nonneg (stageB_pos hp).le
      (mul_nonneg hδ0.le (sub_nonneg.mpr hδ1.le))
  have hloss (z : ℝ) : lossRatio p δ z = c * z := by
    simp only [lossRatio, c]
    ring
  have hfrac := linearFraction_mono hc hx hxy (by simpa [hloss] using hy)
  have hfac : 0 ≤ sieveFactor p δ := (sieveFactor_pos hp hδ1).le
  calc
    recurrenceMap p δ x = sieveFactor p δ * (x / (1 - c * x)) := by
      rw [recurrenceMap, hloss]
      ring
    _ ≤ sieveFactor p δ * (y / (1 - c * y)) :=
      mul_le_mul_of_nonneg_left hfrac hfac
    _ = recurrenceMap p δ y := by
      rw [recurrenceMap, hloss]
      ring

/-- Positivity part of a sieve step.  This is deliberately separate from the
normalized-`f` balance: when `fNext` is defined using division by `μNext`, one
first proves this lemma and only then simplifies that definition. -/
theorem nextRemaining_pos
    {p δ μPrev μNext fPrev : ℝ}
    (hp : 1 < p) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hμPrev : 0 < μPrev) (hfPrev : 0 ≤ fPrev)
    (hvalid : lossRatio p δ fPrev < 1)
    (hloss : μPrev - μNext ≤ μPrev * lossRatio p δ fPrev) :
    0 < μNext := by
  have hden : 0 < 1 - lossRatio p δ fPrev := by linarith
  have hμlower : μPrev * (1 - lossRatio p δ fPrev) ≤ μNext := by
    nlinarith
  exact lt_of_lt_of_le (mul_pos hμPrev hden) hμlower

/-- Algebraic one-step distortion lemma.  The hypothesis `hbalance` is the
identity obtained from the definition of the normalized quantity `f`; the
mass-loss hypothesis is what the stage's second moment supplies. -/
theorem oneStep
    {p δ μPrev μNext fPrev fNext : ℝ}
    (hp : 1 < p) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hμPrev : 0 < μPrev) (hfPrev : 0 ≤ fPrev)
    (hvalid : lossRatio p δ fPrev < 1)
    (hloss : μPrev - μNext ≤ μPrev * lossRatio p δ fPrev)
    (hbalance : fNext * μNext =
      fPrev * μPrev * sieveFactor p δ) :
    0 < μNext ∧ fNext ≤ recurrenceMap p δ fPrev := by
  have hratio_nonneg : 0 ≤ lossRatio p δ fPrev :=
    lossRatio_nonneg hp hδ0 hδ1 hfPrev
  have hden : 0 < 1 - lossRatio p δ fPrev := by linarith
  have hμlower : μPrev * (1 - lossRatio p δ fPrev) ≤ μNext := by
    nlinarith
  have hμNext : 0 < μNext :=
    nextRemaining_pos hp hδ0 hδ1 hμPrev hfPrev hvalid hloss
  have hμratio : μPrev / μNext ≤ 1 / (1 - lossRatio p δ fPrev) := by
    rw [div_le_div_iff₀ hμNext hden]
    simpa [mul_comm] using hμlower
  have hfac_nonneg : 0 ≤ fPrev * sieveFactor p δ :=
    mul_nonneg hfPrev (sieveFactor_pos hp hδ1).le
  constructor
  · exact hμNext
  · calc
      fNext = fPrev * μPrev * sieveFactor p δ / μNext := by
        exact (eq_div_iff hμNext.ne').2 hbalance
      _ = (fPrev * sieveFactor p δ) * (μPrev / μNext) := by ring
      _ ≤ (fPrev * sieveFactor p δ) *
          (1 / (1 - lossRatio p δ fPrev)) :=
        mul_le_mul_of_nonneg_left hμratio hfac_nonneg
      _ = recurrenceMap p δ fPrev := by
        unfold recurrenceMap
        ring

/-- Positivity of the next remaining mass, with the loss bound discharged
from the second moment. -/
theorem nextRemaining_pos_of_secondMoment
    {p δ μPrev μNext fPrev M2 : ℝ}
    (hp : 1 < p) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hμPrev : 0 < μPrev) (hfPrev : 0 ≤ fPrev)
    (hvalid : lossRatio p δ fPrev < 1)
    (hstageCost : μPrev - μNext ≤ M2 / (4 * δ * (1 - δ)))
    (hmoment : M2 ≤ μPrev * fPrev / (p - 1) ^ 2) :
    0 < μNext := by
  apply nextRemaining_pos hp hδ0 hδ1 hμPrev hfPrev hvalid
  calc
    μPrev - μNext ≤ M2 / (4 * δ * (1 - δ)) := hstageCost
    _ ≤ (μPrev * fPrev / (p - 1) ^ 2) /
        (4 * δ * (1 - δ)) := by
      exact div_le_div_of_nonneg_right hmoment (by positivity)
    _ = μPrev * lossRatio p δ fPrev := by
      have hpne : p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
      have hδne : δ ≠ 0 := ne_of_gt hδ0
      have hδ'ne : 1 - δ ≠ 0 := ne_of_gt (sub_pos.mpr hδ1)
      unfold lossRatio stageB
      field_simp [hpne, hδne, hδ'ne]

/-- `oneStep` with its mass-loss premise discharged directly from the usual
second-moment estimate. -/
theorem oneStep_of_secondMoment
    {p δ μPrev μNext fPrev fNext M2 : ℝ}
    (hp : 1 < p) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hμPrev : 0 < μPrev) (hfPrev : 0 ≤ fPrev)
    (hvalid : lossRatio p δ fPrev < 1)
    (hstageCost : μPrev - μNext ≤ M2 / (4 * δ * (1 - δ)))
    (hmoment : M2 ≤ μPrev * fPrev / (p - 1) ^ 2)
    (hbalance : fNext * μNext =
      fPrev * μPrev * sieveFactor p δ) :
    0 < μNext ∧ fNext ≤ recurrenceMap p δ fPrev := by
  apply oneStep hp hδ0 hδ1 hμPrev hfPrev hvalid
  · calc
      μPrev - μNext ≤ M2 / (4 * δ * (1 - δ)) := hstageCost
      _ ≤ (μPrev * fPrev / (p - 1) ^ 2) /
          (4 * δ * (1 - δ)) := by
        exact div_le_div_of_nonneg_right hmoment (by positivity)
      _ = μPrev * lossRatio p δ fPrev := by
        have hpne : p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
        have hδne : δ ≠ 0 := ne_of_gt hδ0
        have hδ'ne : 1 - δ ≠ 0 := ne_of_gt (sub_pos.mpr hδ1)
        unfold lossRatio stageB
        field_simp [hpne, hδne, hδ'ne]
  · exact hbalance

/-! ## Transport through rounded certificates -/

/-- A checked upper bound for the recurrence map transports any smaller
incoming bound.  `U` and `V` can be casts of integer certificate states, or
arbitrary rational/real bounds. -/
theorem recurrenceMap_le_of_certificate
    {p δ f U V : ℝ}
    (hp : 1 < p) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hf0 : 0 ≤ f) (hfU : f ≤ U)
    (hvalidU : lossRatio p δ U < 1)
    (hcertificate : recurrenceMap p δ U ≤ V) :
    recurrenceMap p δ f ≤ V := by
  exact (recurrenceMap_mono hp hδ0 hδ1 hf0 hfU hvalidU).trans hcertificate

/-- Millirational (or, more generally, integer-over-scale) version of
`recurrenceMap_le_of_certificate`. -/
theorem roundedCertificateStep
    {p δ f fNext scale : ℝ} {U V : ℕ}
    (hp : 1 < p) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hscale : 0 < scale) (hf0 : 0 ≤ f)
    (hfU : f ≤ (U : ℝ) / scale)
    (hvalidU : lossRatio p δ ((U : ℝ) / scale) < 1)
    (hstep : fNext ≤ recurrenceMap p δ f)
    (hcertificate : recurrenceMap p δ ((U : ℝ) / scale) ≤
      (V : ℝ) / scale) :
    fNext ≤ (V : ℝ) / scale := by
  have hU0 : 0 ≤ (U : ℝ) / scale := div_nonneg (by positivity) hscale.le
  exact hstep.trans
    (recurrenceMap_le_of_certificate hp hδ0 hδ1 hf0 hfU hvalidU hcertificate)

/-! ## Reciprocal tail envelope -/

/-- Product of the first `n` numerator factors after stage `K`. -/
def tailProduct (N : ℕ → ℝ) (K n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range n, N (K + j + 1)

/-- Accumulated denominator charge for the first `n` stages after `K`. -/
def tailCharge (N C : ℕ → ℝ) (K n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, C (K + j + 1) * tailProduct N K j

@[simp] lemma tailProduct_zero (N : ℕ → ℝ) (K : ℕ) :
    tailProduct N K 0 = 1 := by simp [tailProduct]

@[simp] lemma tailProduct_succ (N : ℕ → ℝ) (K n : ℕ) :
    tailProduct N K (n + 1) =
      tailProduct N K n * N (K + n + 1) := by
  simp [tailProduct, Finset.prod_range_succ]

@[simp] lemma tailCharge_zero (N C : ℕ → ℝ) (K : ℕ) :
    tailCharge N C K 0 = 0 := by simp [tailCharge]

@[simp] lemma tailCharge_succ (N C : ℕ → ℝ) (K n : ℕ) :
    tailCharge N C K (n + 1) =
      tailCharge N C K n + C (K + n + 1) * tailProduct N K n := by
  simp [tailCharge, Finset.sum_range_succ]

lemma tailProduct_nonneg {N : ℕ → ℝ} (hN : ∀ r, 0 ≤ N r)
    (K n : ℕ) : 0 ≤ tailProduct N K n := by
  exact Finset.prod_nonneg fun j _ ↦ hN _

lemma tailCharge_nonneg {N C : ℕ → ℝ}
    (hN : ∀ r, 0 ≤ N r) (hC : ∀ r, 0 ≤ C r)
    (K n : ℕ) : 0 ≤ tailCharge N C K n := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (hC _) (tailProduct_nonneg hN K j)

/-- A single algebraic step in the reciprocal envelope induction. -/
lemma reciprocalEnvelopeStep
    {x y P D N C : ℝ}
    (hx0 : 0 ≤ x) (hP0 : 0 ≤ P) (hD : 0 < D)
    (hN0 : 0 ≤ N) (hC0 : 0 ≤ C)
    (hbound : x ≤ P / D) (hDnext : 0 < D - C * P)
    (hrec : y ≤ x * N / (1 - C * x)) :
    y ≤ P * N / (D - C * P) := by
  have hPD0 : 0 ≤ P / D := div_nonneg hP0 hD.le
  have hCP_lt : C * P < D := by linarith
  have hvalid : C * (P / D) < 1 := by
    have heq : C * (P / D) = (C * P) / D := by ring
    rw [heq, div_lt_one hD]
    exact hCP_lt
  have hmono := linearFraction_mono hC0 hx0 hbound hvalid
  calc
    y ≤ x * N / (1 - C * x) := hrec
    _ = N * (x / (1 - C * x)) := by ring
    _ ≤ N * ((P / D) / (1 - C * (P / D))) :=
      mul_le_mul_of_nonneg_left hmono hN0
    _ = P * N / (D - C * P) := by
      field_simp [hD.ne', hDnext.ne']

/-- The reciprocal-product envelope.  It turns a long nonlinear recurrence
into one product and one sum.  The budget condition is checked only at the
last requested stage; nonnegativity makes it imply every earlier condition. -/
theorem reciprocalEnvelope
    (f N C : ℕ → ℝ) (K n : ℕ) (F : ℝ)
    (hF : 0 < F)
    (hf0 : ∀ r, 0 ≤ f r)
    (hN : ∀ r, 0 ≤ N r) (hC : ∀ r, 0 ≤ C r)
    (hbase : f K ≤ F)
    (hrec : ∀ j : ℕ,
      f (K + j + 1) ≤
        f (K + j) * N (K + j + 1) /
          (1 - C (K + j + 1) * f (K + j)))
    (hbudget : F * tailCharge N C K n < 1) :
    f (K + n) ≤
      tailProduct N K n / (1 / F - tailCharge N C K n) := by
  induction n with
  | zero =>
      simpa [hF.ne'] using hbase
  | succ n ih =>
      have hterm0 :
          0 ≤ C (K + n + 1) * tailProduct N K n :=
        mul_nonneg (hC _) (tailProduct_nonneg hN K n)
      have hbudgetPrev : F * tailCharge N C K n < 1 := by
        rw [tailCharge_succ] at hbudget
        nlinarith [hF, hterm0]
      have ih' := ih hbudgetPrev
      have hD : 0 < 1 / F - tailCharge N C K n := by
        rw [sub_pos, lt_div_iff₀ hF]
        simpa [mul_comm] using hbudgetPrev
      have hDnext :
          0 < (1 / F - tailCharge N C K n) -
            C (K + n + 1) * tailProduct N K n := by
        have heq :
            (1 / F - tailCharge N C K n) -
                C (K + n + 1) * tailProduct N K n =
              1 / F - tailCharge N C K (n + 1) := by
          rw [tailCharge_succ]
          ring
        rw [heq]
        rw [sub_pos, lt_div_iff₀ hF]
        simpa [mul_comm] using hbudget
      have hstep := reciprocalEnvelopeStep
        (hf0 (K + n)) (tailProduct_nonneg hN K n) hD
        (hN _) (hC _) ih' hDnext (hrec n)
      rw [tailProduct_succ, tailCharge_succ]
      convert hstep using 1 <;> ring_nf

/-- A more familiar version of `reciprocalEnvelope`, with denominator
`1 - F*S`. -/
theorem reciprocalEnvelope'
    (f N C : ℕ → ℝ) (K n : ℕ) (F : ℝ)
    (hF : 0 < F)
    (hf0 : ∀ r, 0 ≤ f r)
    (hN : ∀ r, 0 ≤ N r) (hC : ∀ r, 0 ≤ C r)
    (hbase : f K ≤ F)
    (hrec : ∀ j : ℕ,
      f (K + j + 1) ≤
        f (K + j) * N (K + j + 1) /
          (1 - C (K + j + 1) * f (K + j)))
    (hbudget : F * tailCharge N C K n < 1) :
    f (K + n) ≤
      F * tailProduct N K n / (1 - F * tailCharge N C K n) := by
  have h := reciprocalEnvelope f N C K n F hF hf0 hN hC hbase hrec hbudget
  calc
    f (K + n) ≤
        tailProduct N K n / (1 / F - tailCharge N C K n) := h
    _ = F * tailProduct N K n /
        (1 - F * tailCharge N C K n) := by
      have hden : 0 < 1 - F * tailCharge N C K n := by linarith
      have hother : 0 < 1 / F - tailCharge N C K n := by
        rw [sub_pos, lt_div_iff₀ hF]
        simpa [mul_comm] using hbudget
      field_simp [hF.ne', hden.ne', hother.ne']

end

end Erdos586
