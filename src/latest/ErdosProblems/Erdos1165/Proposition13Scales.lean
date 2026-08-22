/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.Proposition13Assembly

/-!
# Explicit HLOZ scales for Proposition 1.3

This module chooses all deterministic parameters in the Appendix-A block
amplification.  The small positive number `scaleSlack delta` separates the
three powers which occur in the argument:

* `3/5 + scaleSlack delta`: the one-block second-moment cost;
* `3/5 + 2 * scaleSlack delta`: the terminal thick-point loss;
* `3/5 + 3 * scaleSlack delta`: the amount by which the Appendix scale is
  pulled below `(log n)/2`.

Thus all polynomial factors and finite constants are absorbed between strict
powers.  The only data left to the probabilistic Appendix are exactly the
one-point, terminal-local-time, and two-point annular comparisons.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Topology

namespace Erdos1165
namespace Proposition13Scales

open Proposition13Assembly

noncomputable section

/-- A bounded positive fraction of the requested lower-deviation slack. -/
def scaleSlack (delta : ℝ) : ℝ := min delta (1 / 10) / 10

lemma scaleSlack_pos {delta : ℝ} (hdelta : 0 < delta) :
    0 < scaleSlack delta := by
  unfold scaleSlack
  positivity

lemma scaleSlack_le_one_hundred (delta : ℝ) :
    scaleSlack delta ≤ 1 / 100 := by
  unfold scaleSlack
  have h := min_le_right delta (1 / 10 : ℝ)
  linarith

lemma ten_mul_scaleSlack_le {delta : ℝ} :
    10 * scaleSlack delta ≤ delta := by
  unfold scaleSlack
  have h := min_le_left delta (1 / 10 : ℝ)
  linarith

/-- Power in the first/second-moment cost. -/
def costExponent (delta : ℝ) : ℝ := 3 / 5 + scaleSlack delta

/-- HLOZ's terminal thick-point exponent. -/
def chosenThickDelta (delta : ℝ) : ℝ := 3 / 5 + 2 * scaleSlack delta

/-- Power in the deterministic-time gap below `(log n)/2`. -/
def gapExponent (delta : ℝ) : ℝ := 3 / 5 + 3 * scaleSlack delta

lemma costExponent_pos {delta : ℝ} (hdelta : 0 < delta) :
    0 < costExponent delta := by
  unfold costExponent
  linarith [scaleSlack_pos hdelta]

lemma costExponent_lt_gapExponent {delta : ℝ} (hdelta : 0 < delta) :
    costExponent delta < gapExponent delta := by
  unfold costExponent gapExponent
  linarith [scaleSlack_pos hdelta]

lemma gapExponent_lt_one (delta : ℝ) : gapExponent delta < 1 := by
  unfold gapExponent
  linarith [scaleSlack_le_one_hundred delta]

lemma chosenThickDelta_lt_target {delta : ℝ} (hdelta : 0 < delta) :
    chosenThickDelta delta < 3 / 5 + delta := by
  unfold chosenThickDelta
  have h := ten_mul_scaleSlack_le (delta := delta)
  have hs := scaleSlack_pos hdelta
  linarith

lemma gapExponent_lt_target {delta : ℝ} (hdelta : 0 < delta) :
    gapExponent delta < 3 / 5 + delta := by
  unfold gapExponent
  have h := ten_mul_scaleSlack_le (delta := delta)
  have hs := scaleSlack_pos hdelta
  linarith

/-- The real scale before rounding. -/
def realScale (delta : ℝ) (n : ℕ) : ℝ :=
  Real.log n / 2 - Real.log n ^ gapExponent delta

/-- The integer Appendix scale `q`. -/
def scaleIndex (delta : ℝ) (n : ℕ) : ℕ := ⌊realScale delta n⌋₊

/-- The explicit sublinear logarithmic cost reserved for one block. -/
def scaleCost (delta : ℝ) (n : ℕ) : ℝ :=
  (scaleIndex delta n : ℝ) ^ costExponent delta

/-- Uniform one-point value requested from the annular comparison. -/
def onePointBound (delta : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-2 * (scaleIndex delta n : ℝ) - scaleCost delta n)

/-- We reserve half of the successful-profile mass for the terminal local
time refinement. -/
def terminalEpsilon : ℝ := 1 / 2

/-- The first-moment lower bound which is squared in Paley--Zygmund. -/
def firstMomentBound (delta : ℝ) (n : ℕ) : ℝ :=
  ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) *
    ((1 - terminalEpsilon) * onePointBound delta n)

/-- A one-point upper envelope used only for the unavoidable diagonal of the
second moment.  Unlike `onePointBound`, this is an upper, not a lower, bound. -/
def pointUpperBound (delta : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-2 * (scaleIndex delta n : ℝ) + scaleCost delta n / 4)

/-- Explicit diagonal contribution to the ordered pair sum. -/
def diagonalPairBound (delta : ℝ) (n : ℕ) : ℝ :=
  256 * (scaleIndex delta n + 1 : ℕ) ^ (24 : ℕ) *
    ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) *
      pointUpperBound delta n

/-- Explicit off-diagonal separation-envelope contribution. -/
def offDiagonalPairBound (delta : ℝ) (n : ℕ) : ℝ :=
  256 * (scaleIndex delta n + 1 : ℕ) *
    ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) ^ 2 *
      Real.exp (-4 * (scaleIndex delta n : ℝ) + scaleCost delta n / 4)

/-- Honest summed pair bound: diagonal plus off-diagonal contributions. -/
def pairMomentBound (delta : ℝ) (n : ℕ) : ℝ :=
  diagonalPairBound delta n + offDiagonalPairBound delta n

/-- The rate used for one independent deterministic block. -/
def oneBlockRate (delta : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-3 * scaleCost delta n) / 16

lemma onePointBound_pos (delta : ℝ) (n : ℕ) :
    0 < onePointBound delta n := Real.exp_pos _

lemma oneBlockRate_pos (delta : ℝ) (n : ℕ) :
    0 < oneBlockRate delta n := by
  unfold oneBlockRate
  positivity

lemma terminalEpsilon_le_one : terminalEpsilon ≤ 1 := by
  norm_num [terminalEpsilon]

lemma one_sub_terminalEpsilon_pos : 0 < 1 - terminalEpsilon := by
  norm_num [terminalEpsilon]

lemma firstMomentBound_pos_of_candidateBox
    {delta : ℝ} {n : ℕ}
    (hbox : 0 < (ThickPoint.candidateBox (scaleIndex delta n)).card) :
    0 < firstMomentBound delta n := by
  unfold firstMomentBound
  have hbox' : (0 : ℝ) <
      (ThickPoint.candidateBox (scaleIndex delta n)).card := by exact_mod_cast hbox
  exact mul_pos hbox' (mul_pos one_sub_terminalEpsilon_pos
    (onePointBound_pos delta n))

lemma pairMomentBound_pos_of_candidateBox
    {delta : ℝ} {n : ℕ}
    (hbox : 0 < (ThickPoint.candidateBox (scaleIndex delta n)).card) :
    0 < pairMomentBound delta n := by
  unfold pairMomentBound
  have hbox' : (0 : ℝ) <
      (ThickPoint.candidateBox (scaleIndex delta n)).card := by exact_mod_cast hbox
  have hdiag : 0 < diagonalPairBound delta n := by
    unfold diagonalPairBound pointUpperBound
    positivity
  exact hdiag.trans_le (le_add_of_nonneg_right (by
    unfold offDiagonalPairBound
    positivity))

/-- If the candidate square has its natural `exp(2q)` size, the honest
diagonal-plus-off-diagonal pair bound still gives the required
`exp(-3 cost)` Paley--Zygmund scale. -/
lemma exp_neg_three_scaleCost_div_eight_le_firstMoment_sq_div_pairMomentBound
    {delta : ℝ} {n : ℕ}
    (hcard : Real.exp (2 * (scaleIndex delta n : ℝ)) ≤
      ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ))
    (hpoly : 256 * (scaleIndex delta n + 1 : ℕ) ^ (24 : ℕ) ≤
      Real.exp (scaleCost delta n / 4)) :
    Real.exp (-3 * scaleCost delta n) / 8 ≤
      firstMomentBound delta n ^ 2 / pairMomentBound delta n := by
  let M : ℝ := (ThickPoint.candidateBox (scaleIndex delta n)).card
  let q : ℝ := scaleIndex delta n
  let C : ℝ := scaleCost delta n
  push_cast at hpoly
  have hM : 0 < M := (Real.exp_pos _).trans_le (by simpa [M, q] using hcard)
  have hqfac : (scaleIndex delta n + 1 : ℝ) ≤
      (scaleIndex delta n + 1 : ℝ) ^ (24 : ℕ) := by
    exact le_self_pow₀ (by push_cast; linarith) (by norm_num)
  have hbase : M * pointUpperBound delta n ≤
      M ^ 2 * Real.exp (-4 * q + C / 4) := by
    unfold pointUpperBound
    dsimp [M, q, C] at hM hcard ⊢
    calc
      ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) *
          Real.exp (-2 * (scaleIndex delta n : ℝ) + scaleCost delta n / 4) =
        ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) *
          (Real.exp (2 * (scaleIndex delta n : ℝ)) *
            Real.exp (-4 * (scaleIndex delta n : ℝ) + scaleCost delta n / 4)) := by
              rw [← Real.exp_add]
              congr 2
              ring
      _ ≤ ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) *
          (((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) *
            Real.exp (-4 * (scaleIndex delta n : ℝ) + scaleCost delta n / 4)) := by
              gcongr
      _ = ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) ^ 2 *
          Real.exp (-4 * (scaleIndex delta n : ℝ) + scaleCost delta n / 4) := by ring
  let B : ℝ := M ^ 2 * Real.exp (-4 * q + C / 4) * Real.exp (C / 4)
  have hpolyScaled : 256 * (scaleIndex delta n + 1 : ℝ) ^ (24 : ℕ) ≤
      Real.exp (scaleCost delta n / 4) := hpoly
  have hqfacScaled : 256 * (scaleIndex delta n + 1 : ℝ) ≤
      Real.exp (scaleCost delta n / 4) :=
    (mul_le_mul_of_nonneg_left hqfac (by norm_num)).trans hpolyScaled
  have hdiag : diagonalPairBound delta n ≤ B := by
    unfold diagonalPairBound
    push_cast
    dsimp [B]
    calc
      256 * ((scaleIndex delta n : ℝ) + 1) ^ (24 : ℕ) *
          ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) *
            pointUpperBound delta n =
        (256 * ((scaleIndex delta n : ℝ) + 1) ^ (24 : ℕ)) *
          (((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) *
            pointUpperBound delta n) := by ring
      _ ≤ Real.exp (scaleCost delta n / 4) *
          (((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) ^ 2 *
            Real.exp (-4 * (scaleIndex delta n : ℝ) + scaleCost delta n / 4)) := by
              exact mul_le_mul hpolyScaled hbase
                (mul_nonneg hM.le (by unfold pointUpperBound; positivity))
                (Real.exp_nonneg _)
      _ = M ^ 2 * Real.exp (-4 * q + C / 4) * Real.exp (C / 4) := by
        dsimp [M, q, C]
        ring
  have hoff : offDiagonalPairBound delta n ≤ B := by
    unfold offDiagonalPairBound
    push_cast
    dsimp [B]
    calc
      256 * ((scaleIndex delta n : ℝ) + 1) *
          ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) ^ 2 *
            Real.exp (-4 * (scaleIndex delta n : ℝ) + scaleCost delta n / 4) =
        (256 * ((scaleIndex delta n : ℝ) + 1)) *
          (((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) ^ 2 *
            Real.exp (-4 * (scaleIndex delta n : ℝ) + scaleCost delta n / 4)) := by ring
      _ ≤
        Real.exp (scaleCost delta n / 4) *
          (((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) ^ 2 *
            Real.exp (-4 * (scaleIndex delta n : ℝ) + scaleCost delta n / 4)) := by
              exact mul_le_mul_of_nonneg_right hqfacScaled (by positivity)
      _ = M ^ 2 * Real.exp (-4 * q + C / 4) * Real.exp (C / 4) := by
        dsimp [M, q, C]
        ring
  have hC0 : 0 ≤ C := by dsimp [C, scaleCost]; positivity
  have hB_eq : B =
      4 * firstMomentBound delta n ^ 2 * Real.exp (5 * C / 2) := by
    have hsquare : Real.exp (-2 * q - C) ^ (2 : ℕ) =
        Real.exp (2 * (-2 * q - C)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hexp : Real.exp (-4 * q + C / 4) * Real.exp (C / 4) =
        Real.exp (-2 * q - C) ^ (2 : ℕ) * Real.exp (5 * C / 2) := by
      rw [hsquare, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    unfold firstMomentBound onePointBound terminalEpsilon
    dsimp [B, M, q, C] at hexp ⊢
    rw [mul_assoc, hexp]
    ring
  have hpair : pairMomentBound delta n ≤
      8 * firstMomentBound delta n ^ 2 * Real.exp (3 * scaleCost delta n) := by
    unfold pairMomentBound
    have htwo : diagonalPairBound delta n + offDiagonalPairBound delta n ≤ 2 * B := by
      linarith
    calc
      diagonalPairBound delta n + offDiagonalPairBound delta n ≤ 2 * B := htwo
      _ = 8 * firstMomentBound delta n ^ 2 * Real.exp (5 * C / 2) := by
        rw [hB_eq]
        ring
      _ ≤ 8 * firstMomentBound delta n ^ 2 * Real.exp (3 * scaleCost delta n) := by
        dsimp [C]
        apply mul_le_mul_of_nonneg_left
        · exact Real.exp_le_exp.mpr (by linarith)
        · positivity
  have hpairpos : 0 < pairMomentBound delta n := by
    apply pairMomentBound_pos_of_candidateBox
    have hM' : (0 : ℝ) <
        (ThickPoint.candidateBox (scaleIndex delta n)).card := by simpa [M] using hM
    exact_mod_cast hM'
  rw [le_div_iff₀ hpairpos]
  calc
    Real.exp (-3 * scaleCost delta n) / 8 * pairMomentBound delta n ≤
        Real.exp (-3 * scaleCost delta n) / 8 *
          (8 * firstMomentBound delta n ^ 2 *
            Real.exp (3 * scaleCost delta n)) := by gcongr
    _ = firstMomentBound delta n ^ 2 := by
      have hcanc : Real.exp (-3 * scaleCost delta n) *
          Real.exp (3 * scaleCost delta n) = 1 := by
        rw [← Real.exp_add]
        simp
      rw [div_eq_mul_inv]
      calc
        Real.exp (-3 * scaleCost delta n) * (8 : ℝ)⁻¹ *
            (8 * firstMomentBound delta n ^ 2 *
              Real.exp (3 * scaleCost delta n)) =
          firstMomentBound delta n ^ 2 *
            (Real.exp (-3 * scaleCost delta n) *
              Real.exp (3 * scaleCost delta n)) := by ring
        _ = firstMomentBound delta n ^ 2 := by rw [hcanc]; ring

/-- Pure numerical closure of the one-block inequality.  The only input is
the independently proved exit tail at the selected block length. -/
lemma oneBlockNumerical_of_exit
    {delta : ℝ} {n : ℕ}
    (hcard : Real.exp (2 * (scaleIndex delta n : ℝ)) ≤
      ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ))
    (hpoly : 256 * (scaleIndex delta n + 1 : ℕ) ^ (24 : ℕ) ≤
      Real.exp (scaleCost delta n / 4))
    {exitLoss : ℝ}
    (hexit : exitLoss ≤ 1 / 16 * Real.exp (-3 * scaleCost delta n)) :
    1 - firstMomentBound delta n ^ 2 / pairMomentBound delta n + exitLoss ≤
      Real.exp (-oneBlockRate delta n) := by
  have hsuccess :=
    exp_neg_three_scaleCost_div_eight_le_firstMoment_sq_div_pairMomentBound hcard hpoly
  have hp : 0 ≤ Real.exp (-3 * scaleCost delta n) := (Real.exp_pos _).le
  calc
    1 - firstMomentBound delta n ^ 2 / pairMomentBound delta n + exitLoss ≤
        1 - Real.exp (-3 * scaleCost delta n) / 8 +
          1 / 16 * Real.exp (-3 * scaleCost delta n) := by gcongr
    _ = 1 - oneBlockRate delta n := by
      unfold oneBlockRate
      ring
    _ ≤ Real.exp (-oneBlockRate delta n) :=
      Real.one_sub_le_exp_neg (oneBlockRate delta n)

/-! ## Elementary asymptotics of the rounded scale -/

lemma tendsto_log_nat_atTop :
    Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- A lower real power is eventually at most one quarter of the first
power.  Keeping this lemma explicit makes every later use of a strict power
margin independent of automation. -/
lemma eventually_rpow_le_quarter_mul {a : ℝ} (ha : a < 1) :
    ∀ᶠ x : ℝ in atTop, x ^ a ≤ x / 4 := by
  have hpow : Tendsto (fun x : ℝ ↦ x ^ (a - 1)) atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop (sub_pos.mpr ha)
    apply h.congr'
    filter_upwards [] with x
    congr 1
    ring
  have hsmall : ∀ᶠ x : ℝ in atTop, x ^ (a - 1) ≤ 1 / 4 :=
    hpow.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hsplit : x ^ a = x ^ (a - 1) * x := by
    calc
      x ^ a = x ^ ((a - 1) + 1) := by ring_nf
      _ = x ^ (a - 1) * x ^ (1 : ℝ) := Real.rpow_add hx0 _ _
      _ = x ^ (a - 1) * x := by rw [Real.rpow_one]
  rw [hsplit]
  exact (mul_le_mul_of_nonneg_right hx hx0.le).trans_eq (by ring)

lemma eventually_log_gap_le_quarter (delta : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log n ^ gapExponent delta ≤ Real.log n / 4 := by
  exact tendsto_log_nat_atTop.eventually
    (eventually_rpow_le_quarter_mul (gapExponent_lt_one delta))

lemma eventually_realScale_bounds (delta : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log n / 4 ≤ realScale delta n ∧
        realScale delta n ≤ Real.log n / 2 := by
  filter_upwards [eventually_log_gap_le_quarter delta,
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop 0)] with n hgap hlog
  unfold realScale
  constructor
  · linarith
  · have hp := Real.rpow_nonneg hlog (gapExponent delta)
    linarith

lemma eventually_scaleIndex_bounds (delta : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Real.log n / 4 - 1 < (scaleIndex delta n : ℝ) ∧
        (scaleIndex delta n : ℝ) ≤ Real.log n / 2 := by
  filter_upwards [eventually_realScale_bounds delta,
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop 4)] with n hb hlog
  have hreal0 : 0 ≤ realScale delta n := by linarith [hb.1]
  have hfloor := Nat.floor_le hreal0
  have hfloorUpper := Nat.lt_floor_add_one (realScale delta n)
  change Real.log n / 4 - 1 < (⌊realScale delta n⌋₊ : ℝ) ∧
    (⌊realScale delta n⌋₊ : ℝ) ≤ Real.log n / 2
  constructor <;> linarith [hb.1, hb.2]

lemma tendsto_scaleIndex_atTop (delta : ℝ) :
    Tendsto (fun n : ℕ ↦ (scaleIndex delta n : ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_scaleIndex_bounds delta,
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop (4 * (b + 1)))]
      with n hb hlog
  linarith

lemma eventually_scaleIndex_pos (delta : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < scaleIndex delta n := by
  have h := (tendsto_scaleIndex_atTop delta).eventually (eventually_gt_atTop 0)
  filter_upwards [h] with n hn
  exact_mod_cast hn

/-! ## Nonemptiness and positivity of the finite candidate square -/

lemma regularRadius_zero_ge_one {q : ℕ} (hq : 0 < q) :
    1 ≤ ThickPoint.regularRadius q 0 := by
  rw [ThickPoint.regularRadius]
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hexp : (1 : ℝ) ≤ Real.exp ((q : ℝ) - (0 : ℝ)) := by
    simpa using Real.one_le_exp (by positivity : (0 : ℝ) ≤ (q : ℝ))
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ (9 : ℕ) := by
    exact one_le_pow₀ hqR
  calc
    (1 : ℝ) = 1 * 1 := by ring
    _ ≤ Real.exp ((q : ℝ) - (0 : ℝ)) * (q : ℝ) ^ (9 : ℕ) :=
      mul_le_mul hexp hpow (by positivity) (by positivity)
    _ = Real.exp ((q : ℝ) - (0 : ℕ)) * (q : ℝ) ^ (9 : ℕ) := by norm_num

lemma candidateInterval_nonempty {q : ℕ} (hq : 0 < q) :
    (ThickPoint.candidateInterval q).Nonempty := by
  let r := ThickPoint.regularRadius q 0
  refine ⟨⌈2 * r⌉, ?_⟩
  rw [ThickPoint.mem_candidateInterval]
  refine ⟨le_rfl, ?_⟩
  apply Int.le_floor.mpr
  have hr : (1 : ℝ) ≤ r := by simpa [r] using regularRadius_zero_ge_one hq
  have hceil : ((⌈2 * r⌉ : ℤ) : ℝ) < 2 * r + 1 := Int.ceil_lt_add_one _
  linarith

lemma candidateBox_card_pos {q : ℕ} (hq : 0 < q) :
    0 < (ThickPoint.candidateBox q).card := by
  rw [ThickPoint.card_candidateBox]
  exact pow_pos (Finset.card_pos.mpr (candidateInterval_nonempty hq)) _

lemma eventually_candidateBox_card_pos (delta : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      0 < (ThickPoint.candidateBox (scaleIndex delta n)).card := by
  filter_upwards [eventually_scaleIndex_pos delta] with n hn
  exact candidateBox_card_pos hn

/-- The HLOZ candidate interval has at least its natural exponential length.
The two units lost to rounding are absorbed by the `q^9` factor. -/
lemma exp_scale_le_candidateInterval_card {q : ℕ} (hq : 2 ≤ q) :
    Real.exp (q : ℝ) ≤ (ThickPoint.candidateInterval q).card := by
  let r : ℝ := ThickPoint.regularRadius q 0
  let a : ℤ := ⌈2 * r⌉
  let b : ℤ := ⌊3 * r⌋
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hexpOne : (1 : ℝ) ≤ Real.exp (q : ℝ) :=
    Real.one_le_exp (by positivity)
  have hpow : (2 : ℝ) ≤ (q : ℝ) ^ (9 : ℕ) := by
    calc
      (2 : ℝ) ≤ 2 ^ (9 : ℕ) := by norm_num
      _ ≤ (q : ℝ) ^ (9 : ℕ) := pow_le_pow_left₀ (by norm_num) hqR 9
  have hr : r = Real.exp (q : ℝ) * (q : ℝ) ^ (9 : ℕ) := by
    simp [r, ThickPoint.regularRadius]
  have hrTwo : 2 ≤ r := by rw [hr]; nlinarith [Real.exp_pos (q : ℝ)]
  have hab : a ≤ b := by
    rw [← Int.cast_le (R := ℝ)]
    dsimp [a, b]
    push_cast
    linarith [Int.ceil_lt_add_one (2 * r), Int.lt_floor_add_one (3 * r)]
  have hcardZ : ((ThickPoint.candidateInterval q).card : ℤ) = b + 1 - a := by
    unfold ThickPoint.candidateInterval
    change ((Finset.Icc a b).card : ℤ) = b + 1 - a
    exact Int.card_Icc_of_le a b (by omega)
  have hround : r - 1 < ((ThickPoint.candidateInterval q).card : ℝ) := by
    rw [show ((ThickPoint.candidateInterval q).card : ℝ) =
        ((b + 1 - a : ℤ) : ℝ) by exact_mod_cast hcardZ]
    dsimp [a, b]
    push_cast
    linarith [Int.ceil_lt_add_one (2 * r), Int.lt_floor_add_one (3 * r)]
  have hmul : 1 ≤ Real.exp (q : ℝ) * ((q : ℝ) ^ (9 : ℕ) - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hexpOne)
      (sub_nonneg.mpr (by linarith : (1 : ℝ) ≤ (q : ℝ) ^ (9 : ℕ)))]
  rw [hr] at hround
  linarith

lemma exp_two_scale_le_candidateBox_card {q : ℕ} (hq : 2 ≤ q) :
    Real.exp (2 * (q : ℝ)) ≤ (ThickPoint.candidateBox q).card := by
  rw [ThickPoint.card_candidateBox]
  push_cast
  have hinterval := exp_scale_le_candidateInterval_card hq
  have hsquare := pow_le_pow_left₀ (Real.exp_pos (q : ℝ)).le hinterval 2
  calc
    Real.exp (2 * (q : ℝ)) = Real.exp (q : ℝ) ^ (2 : ℕ) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    _ ≤ ((ThickPoint.candidateInterval q).card : ℝ) ^ (2 : ℕ) := hsquare

lemma eventually_candidateBox_card_ge_exp_two_scale (delta : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (2 * (scaleIndex delta n : ℝ)) ≤
        (ThickPoint.candidateBox (scaleIndex delta n)).card := by
  have hq := (tendsto_scaleIndex_atTop delta).eventually (eventually_ge_atTop 2)
  filter_upwards [hq] with n hn
  exact exp_two_scale_le_candidateBox_card (by exact_mod_cast hn)

/-! ## Diffusive block length and its exit loss -/

/-- Sixteen times `q+1` diffusive escape blocks.  The extra constant factor
leaves room for the full sublinear one-block moment cost. -/
def chosenBlockLength (delta : ℝ) (n : ℕ) : ℕ :=
  DiffusiveExitTail.diffusiveBlockLength
      (outerExitRadius (scaleIndex delta n)) *
    (16 * (scaleIndex delta n + 1))

/-- The maximal number of consecutive complete blocks before time `n`. -/
def chosenBlockCount (delta : ℝ) (n : ℕ) : ℕ :=
  n / chosenBlockLength delta n

/-- The logarithmic number of blocks actually needed by amplification. -/
def requiredBlockLog (delta : ℝ) (n : ℕ) : ℝ :=
  Real.log n ^ (3 / 5 : ℝ) + 3 * scaleCost delta n

/-- A convenient integer minorant which will eventually fit among the
complete consecutive blocks. -/
def requiredBlockCount (delta : ℝ) (n : ℕ) : ℕ :=
  ⌈16 * Real.exp (requiredBlockLog delta n)⌉₊

lemma requiredBlockCount_rate (delta : ℝ) (n : ℕ) :
    Real.exp (Real.log n ^ (3 / 5 : ℝ)) ≤
      (requiredBlockCount delta n : ℝ) * oneBlockRate delta n := by
  have hceil : 16 * Real.exp (requiredBlockLog delta n) ≤
      (requiredBlockCount delta n : ℝ) := by
    exact Nat.le_ceil _
  have hrate : 0 ≤ oneBlockRate delta n := (oneBlockRate_pos delta n).le
  calc
    Real.exp (Real.log n ^ (3 / 5 : ℝ)) =
        (16 * Real.exp (requiredBlockLog delta n)) * oneBlockRate delta n := by
      unfold requiredBlockLog oneBlockRate
      rw [Real.exp_add]
      have hcanc : Real.exp (3 * scaleCost delta n) *
          Real.exp (-3 * scaleCost delta n) = 1 := by
        rw [← Real.exp_add]
        simp
      symm
      calc
        16 * (Real.exp (Real.log n ^ (3 / 5 : ℝ)) *
            Real.exp (3 * scaleCost delta n)) *
            (Real.exp (-3 * scaleCost delta n) / 16) =
          Real.exp (Real.log n ^ (3 / 5 : ℝ)) *
            (Real.exp (3 * scaleCost delta n) *
              Real.exp (-3 * scaleCost delta n)) := by ring
        _ = Real.exp (Real.log n ^ (3 / 5 : ℝ)) := by rw [hcanc]; ring
    _ ≤ (requiredBlockCount delta n : ℝ) * oneBlockRate delta n :=
      mul_le_mul_of_nonneg_right hceil hrate

lemma chosenBlockLength_pos (delta : ℝ) (n : ℕ) :
    0 < chosenBlockLength delta n := by
  unfold chosenBlockLength
  exact Nat.mul_pos (DiffusiveExitTail.diffusiveBlockLength_pos _) (by omega)

lemma chosenBlocks_fit (delta : ℝ) (n : ℕ) :
    chosenBlockCount delta n * chosenBlockLength delta n ≤ n := by
  unfold chosenBlockCount
  simpa [Nat.mul_comm] using Nat.div_mul_le_self n (chosenBlockLength delta n)

lemma outerScale_ge_one {q : ℕ} (hq : 0 < q) :
    1 ≤ ThickPoint.outerScale q := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hexp : (1 : ℝ) ≤ Real.exp (q : ℝ) :=
    Real.one_le_exp (by positivity)
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ (9 : ℕ) := one_le_pow₀ hqR
  unfold ThickPoint.outerScale
  nlinarith [mul_pos (Real.exp_pos (q : ℝ)) (pow_pos (by positivity : (0 : ℝ) < q) 9)]

lemma outerExitRadius_add_one_cast_le {q : ℕ} (hq : 0 < q) :
    ((outerExitRadius q + 1 : ℕ) : ℝ) ≤ 3 * ThickPoint.outerScale q := by
  have hK0 : 0 ≤ ThickPoint.outerScale q :=
    zero_le_one.trans (outerScale_ge_one hq)
  have hceil := Nat.ceil_lt_add_one hK0
  unfold outerExitRadius
  push_cast
  linarith [outerScale_ge_one hq]

lemma chosenBlockLength_cast_le {delta : ℝ} {n : ℕ}
    (hq : 0 < scaleIndex delta n) :
    (chosenBlockLength delta n : ℝ) ≤
      4608 * ThickPoint.outerScale (scaleIndex delta n) ^ 2 *
        (scaleIndex delta n + 1 : ℕ) := by
  have hR := outerExitRadius_add_one_cast_le hq
  have hq1 : (0 : ℝ) ≤ (scaleIndex delta n + 1 : ℕ) := by positivity
  unfold chosenBlockLength DiffusiveExitTail.diffusiveBlockLength
  push_cast
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤
    (outerExitRadius (scaleIndex delta n) + 1 : ℕ)) hR 2
  push_cast at hsq
  calc
    32 * (outerExitRadius (scaleIndex delta n) + 1) ^ 2 *
          (16 * ((scaleIndex delta n : ℝ) + 1)) =
        512 * (outerExitRadius (scaleIndex delta n) + 1) ^ 2 *
          ((scaleIndex delta n : ℝ) + 1) := by ring
    _ ≤ 512 * (3 * ThickPoint.outerScale (scaleIndex delta n)) ^ 2 *
          ((scaleIndex delta n : ℝ) + 1) := by gcongr
    _ = 4608 * ThickPoint.outerScale (scaleIndex delta n) ^ 2 *
          ((scaleIndex delta n : ℝ) + 1) := by ring

lemma exitExponent_chosenBlockLength (delta : ℝ) (n : ℕ) :
    exitExponent (outerExitRadius (scaleIndex delta n))
        (chosenBlockLength delta n) =
      3 * (scaleIndex delta n + 1 : ℕ) := by
  unfold exitExponent chosenBlockLength
  rw [Nat.mul_div_cancel_left _ (DiffusiveExitTail.diffusiveBlockLength_pos _)]
  push_cast
  ring

lemma costExponent_lt_one (delta : ℝ) : costExponent delta < 1 := by
  unfold costExponent
  linarith [scaleSlack_le_one_hundred delta]

lemma eventually_scaleCost_le_quarter (delta : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      scaleCost delta n ≤ (scaleIndex delta n : ℝ) / 4 := by
  exact (tendsto_scaleIndex_atTop delta).eventually
    (eventually_rpow_le_quarter_mul (costExponent_lt_one delta))

/-- The `q^24` near-diagonal multiplicity and the `q` separation-level
multiplicity are both absorbed by one quarter of the reserved scale cost. -/
lemma eventually_pairPolynomial_le_exp_quarter_cost
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      256 * ((scaleIndex delta n + 1 : ℕ) : ℝ) ^ (24 : ℕ) ≤
        Real.exp (scaleCost delta n / 4) := by
  have hcost : 0 < costExponent delta := costExponent_pos hdelta
  have hsmall := (isLittleO_log_rpow_atTop hcost).bound
    (show (0 : ℝ) < 1 / 384 by norm_num)
  have hcomposed := (tendsto_scaleIndex_atTop delta).eventually hsmall
  filter_upwards [hcomposed,
    (tendsto_scaleIndex_atTop delta).eventually (eventually_ge_atTop 2),
    ((tendsto_rpow_atTop hcost).comp (tendsto_scaleIndex_atTop delta)).eventually
      (eventually_ge_atTop (8 * Real.log 256))]
      with n hlog hq hcostLarge
  simp only [Function.comp_apply] at hcostLarge
  let q : ℝ := scaleIndex delta n
  have hqTwo : (2 : ℝ) ≤ q := hq
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have hcost0 : 0 ≤ q ^ costExponent delta := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg hlogq0, Real.norm_of_nonneg hcost0] at hlog
  have hqSuccSq : q + 1 ≤ q ^ (2 : ℕ) := by nlinarith
  have hlogSucc : Real.log (q + 1) ≤ 2 * Real.log q := by
    calc
      Real.log (q + 1) ≤ Real.log (q ^ (2 : ℕ)) :=
        Real.log_le_log (by positivity) hqSuccSq
      _ = 2 * Real.log q := by rw [Real.log_pow]; norm_num
  have htargetR : 256 * (q + 1) ^ (24 : ℕ) ≤
      Real.exp (q ^ costExponent delta / 4) := by
    rw [← Real.exp_log (by positivity : 0 < 256 * (q + 1) ^ (24 : ℕ))]
    apply Real.exp_le_exp.mpr
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
    linarith
  simpa [q, scaleCost] using htargetR

lemma eventually_exitLoss_le (delta : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (-exitExponent (outerExitRadius (scaleIndex delta n))
          (chosenBlockLength delta n)) ≤
        1 / 16 * Real.exp (-3 * scaleCost delta n) := by
  filter_upwards [eventually_scaleCost_le_quarter delta,
    eventually_scaleIndex_pos delta] with n hcost hq
  rw [exitExponent_chosenBlockLength]
  let D : ℝ := 3 * (scaleIndex delta n + 1 : ℕ) - 3 * scaleCost delta n
  have hD : 4 ≤ D := by
    dsimp [D]
    push_cast
    have hqR : (1 : ℝ) ≤ scaleIndex delta n := by exact_mod_cast hq
    linarith
  have hnegD : -D ≤ (-4 : ℝ) := neg_le_neg hD
  have hexpFour : Real.exp (-4 : ℝ) < 1 / 16 := by
    calc
      Real.exp (-4 : ℝ) = Real.exp (-1 : ℝ) ^ (4 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ < (1 / 2 : ℝ) ^ (4 : ℕ) :=
        pow_lt_pow_left₀ Real.exp_neg_one_lt_half (Real.exp_pos _).le (by norm_num)
      _ = 1 / 16 := by norm_num
  have hexpD : Real.exp (-D) ≤ 1 / 16 :=
    (Real.exp_le_exp.mpr hnegD).trans hexpFour.le
  have hsplit :
      -(3 * (scaleIndex delta n + 1 : ℕ)) =
        -3 * scaleCost delta n + (-D) := by
    dsimp [D]
    ring
  rw [hsplit, Real.exp_add]
  nlinarith [Real.exp_pos (-3 * scaleCost delta n)]

/-! ## The outer radius on the rounded scale -/

lemma log_outerScale {q : ℕ} (hq : 0 < q) :
    Real.log (ThickPoint.outerScale q) =
      Real.log 16 + q + 9 * Real.log q := by
  unfold ThickPoint.outerScale
  have h16 : (16 : ℝ) ≠ 0 := by norm_num
  have hexp : Real.exp (q : ℝ) ≠ 0 := (Real.exp_pos _).ne'
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [Real.log_mul (mul_ne_zero h16 hexp) (pow_ne_zero 9 hqR),
    Real.log_mul h16 hexp, Real.log_exp, Real.log_pow]
  push_cast
  ring

lemma log_outerScale_ge_scale {q : ℕ} (hq : 0 < q) :
    (q : ℝ) ≤ Real.log (ThickPoint.outerScale q) := by
  rw [log_outerScale hq]
  have hlog16 : (0 : ℝ) ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have hlogq : (0 : ℝ) ≤ Real.log q :=
    Real.log_nonneg (by exact_mod_cast hq)
  linarith

lemma eventually_log_scale_le_gap {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      Real.log 16 + 9 * Real.log (scaleIndex delta n) ≤
        (1 / 2 : ℝ) * Real.log n ^ gapExponent delta := by
  have hgap : 0 < gapExponent delta := by
    unfold gapExponent
    linarith [scaleSlack_pos hdelta]
  have hlogSmall := (isLittleO_log_rpow_atTop hgap).bound
    (show (0 : ℝ) < 1 / 20 by norm_num)
  have hcomposed := tendsto_log_nat_atTop.eventually hlogSmall
  filter_upwards [hcomposed, eventually_scaleIndex_bounds delta,
    eventually_scaleIndex_pos delta,
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop 4),
    ((tendsto_rpow_atTop hgap).comp tendsto_log_nat_atTop).eventually
      (eventually_ge_atTop (20 * Real.log 16))] with n hsmall hqbounds hq hlog hpow
  simp only [Function.comp_apply] at hpow
  have hlogq_le : Real.log (scaleIndex delta n : ℝ) ≤
      Real.log (Real.log n) := by
    apply Real.log_le_log (by positivity)
    exact hqbounds.2.trans (by linarith)
  have hloglog_nonneg : 0 ≤ Real.log (Real.log n) :=
    Real.log_nonneg (by linarith)
  have habs : |Real.log (Real.log n)| = Real.log (Real.log n) :=
    abs_of_nonneg hloglog_nonneg
  have hloglog : Real.log (Real.log n) ≤
      (1 / 20 : ℝ) * Real.log n ^ gapExponent delta := by
    rw [Real.norm_of_nonneg hloglog_nonneg,
      Real.norm_of_nonneg
      (Real.rpow_nonneg (by linarith : 0 ≤ Real.log n) _)] at hsmall
    exact hsmall
  have hlogq_nonneg : 0 ≤ Real.log (scaleIndex delta n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq)
  calc
    Real.log 16 + 9 * Real.log (scaleIndex delta n) ≤
        Real.log 16 + 9 * Real.log (Real.log n) := by gcongr
    _ ≤ Real.log 16 + 9 * ((1 / 20 : ℝ) *
          Real.log n ^ gapExponent delta) := by gcongr
    _ ≤ (1 / 2 : ℝ) * Real.log n ^ gapExponent delta := by linarith

/-- All polynomial factors in the diffusive block length are negligible
relative to the gap power. -/
lemma eventually_blockPolynomial_le_exp {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      (4608 * 16 ^ 2 : ℝ) * (scaleIndex delta n : ℝ) ^ (18 : ℕ) *
          (scaleIndex delta n + 1 : ℕ) ≤
        Real.exp ((1 / 2 : ℝ) * Real.log n ^ gapExponent delta) := by
  have hgap : 0 < gapExponent delta := by
    unfold gapExponent
    linarith [scaleSlack_pos hdelta]
  have hlogSmall := (isLittleO_log_rpow_atTop hgap).bound
    (show (0 : ℝ) < 1 / 100 by norm_num)
  have hcomposed := tendsto_log_nat_atTop.eventually hlogSmall
  filter_upwards [hcomposed, eventually_scaleIndex_bounds delta,
    eventually_scaleIndex_pos delta,
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop 4),
    ((tendsto_rpow_atTop hgap).comp tendsto_log_nat_atTop).eventually
      (eventually_ge_atTop (4 * Real.log (4608 * 16 ^ 2 : ℝ)))]
      with n hsmall hqbounds hq hL hG
  simp only [Function.comp_apply] at hG
  have hlogL_nonneg : 0 ≤ Real.log (Real.log n) :=
    Real.log_nonneg (by linarith)
  have hloglog : Real.log (Real.log n) ≤
      (1 / 100 : ℝ) * Real.log n ^ gapExponent delta := by
    rw [Real.norm_of_nonneg hlogL_nonneg,
      Real.norm_of_nonneg
        (Real.rpow_nonneg (by linarith : 0 ≤ Real.log n) _)] at hsmall
    exact hsmall
  have hqSucc_le : (scaleIndex delta n + 1 : ℝ) ≤ Real.log n := by
    push_cast
    linarith [hqbounds.2]
  have hlogSucc_le : Real.log (scaleIndex delta n + 1 : ℝ) ≤
      Real.log (Real.log n) := by
    apply Real.log_le_log (by positivity)
    exact hqSucc_le
  have hlogq_le : Real.log (scaleIndex delta n : ℝ) ≤
      Real.log (scaleIndex delta n + 1 : ℝ) := by
    apply Real.log_le_log (by positivity)
    push_cast
    linarith
  have hlogSucc_final : Real.log (scaleIndex delta n + 1 : ℝ) ≤
      (1 / 100 : ℝ) * Real.log n ^ gapExponent delta :=
    hlogSucc_le.trans hloglog
  have hlogq_final : Real.log (scaleIndex delta n : ℝ) ≤
      (1 / 100 : ℝ) * Real.log n ^ gapExponent delta :=
    hlogq_le.trans hlogSucc_final
  have hpolypos : 0 < (4608 * 16 ^ 2 : ℝ) *
      (scaleIndex delta n : ℝ) ^ (18 : ℕ) *
        (scaleIndex delta n + 1 : ℕ) := by positivity
  rw [← Real.exp_log hpolypos]
  apply Real.exp_le_exp.mpr
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  norm_num at *
  linarith

lemma eventually_blockLength_le_exp {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      (chosenBlockLength delta n : ℝ) ≤
        Real.exp (Real.log n - (3 / 2 : ℝ) *
          Real.log n ^ gapExponent delta) := by
  filter_upwards [eventually_blockPolynomial_le_exp hdelta,
    eventually_scaleIndex_pos delta, eventually_realScale_bounds delta]
      with n hpoly hq hreal
  have hqfloor : 0 < ⌊realScale delta n⌋₊ := by simpa [scaleIndex] using hq
  have hreal0 : 0 ≤ realScale delta n :=
    zero_le_one.trans (Nat.floor_pos.mp hqfloor)
  have hqUpper := Nat.floor_le hreal0
  change (scaleIndex delta n : ℝ) ≤ realScale delta n at hqUpper
  simp only [realScale] at hqUpper
  have hblock := chosenBlockLength_cast_le (delta := delta) (n := n) hq
  have hrearrange :
      4608 * ThickPoint.outerScale (scaleIndex delta n) ^ 2 *
          (scaleIndex delta n + 1 : ℕ) =
        ((4608 * 16 ^ 2 : ℝ) * (scaleIndex delta n : ℝ) ^ (18 : ℕ) *
          (scaleIndex delta n + 1 : ℕ)) *
            Real.exp (2 * (scaleIndex delta n : ℝ)) := by
    unfold ThickPoint.outerScale
    have hexp : Real.exp (2 * (scaleIndex delta n : ℝ)) =
        Real.exp (scaleIndex delta n : ℝ) ^ (2 : ℕ) := by
      convert Real.exp_nat_mul (scaleIndex delta n : ℝ) 2 using 1 <;> norm_num
    rw [hexp]
    ring
  rw [hrearrange] at hblock
  calc
    (chosenBlockLength delta n : ℝ) ≤
        ((4608 * 16 ^ 2 : ℝ) * (scaleIndex delta n : ℝ) ^ (18 : ℕ) *
          (scaleIndex delta n + 1 : ℕ)) *
            Real.exp (2 * (scaleIndex delta n : ℝ)) := hblock
    _ ≤ Real.exp ((1 / 2 : ℝ) * Real.log n ^ gapExponent delta) *
          Real.exp (2 * (scaleIndex delta n : ℝ)) := by gcongr
    _ = Real.exp ((1 / 2 : ℝ) * Real.log n ^ gapExponent delta +
          2 * (scaleIndex delta n : ℝ)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (Real.log n - (3 / 2 : ℝ) *
          Real.log n ^ gapExponent delta) := by
      apply Real.exp_le_exp.mpr
      linarith

lemma eventually_log_outerScale_bounds {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      Real.log n / 2 - Real.log n ^ gapExponent delta - 1 <
          Real.log (ThickPoint.outerScale (scaleIndex delta n)) ∧
        Real.log (ThickPoint.outerScale (scaleIndex delta n)) ≤
          Real.log n / 2 - (1 / 2 : ℝ) * Real.log n ^ gapExponent delta := by
  filter_upwards [eventually_scaleIndex_bounds delta, eventually_realScale_bounds delta,
    eventually_scaleIndex_pos delta, eventually_log_scale_le_gap hdelta]
      with n hqBounds hrealBounds hq hlogError
  have hqfloor : 0 < ⌊realScale delta n⌋₊ := by simpa [scaleIndex] using hq
  have hreal0 : 0 ≤ realScale delta n :=
    zero_le_one.trans (Nat.floor_pos.mp hqfloor)
  have hfloorLower := Nat.lt_floor_add_one (realScale delta n)
  have hfloorUpper := Nat.floor_le hreal0
  change (scaleIndex delta n : ℝ) ≤ realScale delta n at hfloorUpper
  simp only [realScale] at hfloorUpper
  have hqLower : Real.log n / 2 - Real.log n ^ gapExponent delta - 1 <
      (scaleIndex delta n : ℝ) := by
    change realScale delta n - 1 < (scaleIndex delta n : ℝ)
    change realScale delta n < (scaleIndex delta n : ℝ) + 1 at hfloorLower
    linarith
  rw [log_outerScale hq]
  constructor
  · have hnonneg : 0 ≤ Real.log 16 + 9 * Real.log (scaleIndex delta n) := by
      have hqone : (1 : ℝ) ≤ scaleIndex delta n := by exact_mod_cast hq
      have hlogq := Real.log_nonneg hqone
      have hlog16 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16)
      positivity
    linarith
  · linarith

/-! ## The thick threshold dominates the target lower-deviation level -/

lemma eventually_const_mul_rpow_le_half_rpow
    {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C) :
    ∀ᶠ x : ℝ in atTop, C * x ^ a ≤ (1 / 2 : ℝ) * x ^ b := by
  have hpow : Tendsto (fun x : ℝ ↦ x ^ (a - b)) atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop (sub_pos.mpr hab)
    apply h.congr'
    filter_upwards [] with x
    congr 1
    ring
  have hsmall : ∀ᶠ x : ℝ in atTop,
      x ^ (a - b) ≤ 1 / (2 * (C + 1)) := by
    exact hpow.eventually (Iic_mem_nhds (by positivity :
      (0 : ℝ) < 1 / (2 * (C + 1))))
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hb0 : 0 ≤ x ^ b := Real.rpow_nonneg hx0.le _
  have hsplit : x ^ a = x ^ (a - b) * x ^ b := by
    calc
      x ^ a = x ^ ((a - b) + b) := by ring_nf
      _ = x ^ (a - b) * x ^ b := Real.rpow_add hx0 _ _
  rw [hsplit]
  calc
    C * (x ^ (a - b) * x ^ b) = (C * x ^ (a - b)) * x ^ b := by ring
    _ ≤ (C * (1 / (2 * (C + 1)))) * x ^ b := by gcongr
    _ ≤ (1 / 2 : ℝ) * x ^ b := by
      gcongr
      have hCp : 0 < C + 1 := by linarith
      rw [div_eq_mul_inv]
      field_simp
      linarith

lemma eventually_threshold_error_bounds {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      20 * Real.log n ^ (1 + gapExponent delta) ≤
          (1 / 2 : ℝ) * Real.log n ^ levelTailExponent delta ∧
        Real.log n ^ (1 + chosenThickDelta delta) ≤
          (1 / 2 : ℝ) * Real.log n ^ levelTailExponent delta := by
  have hgap : 1 + gapExponent delta < levelTailExponent delta := by
    unfold levelTailExponent
    linarith [gapExponent_lt_target hdelta]
  have hthick : 1 + chosenThickDelta delta < levelTailExponent delta := by
    unfold levelTailExponent
    linarith [chosenThickDelta_lt_target hdelta]
  have hfirst := tendsto_log_nat_atTop.eventually
    (eventually_const_mul_rpow_le_half_rpow hgap (by norm_num : (0 : ℝ) ≤ 20))
  have hsecond := tendsto_log_nat_atTop.eventually
    (eventually_const_mul_rpow_le_half_rpow hthick (by norm_num : (0 : ℝ) ≤ 1))
  filter_upwards [hfirst, hsecond] with n h1 h2
  exact ⟨h1, by simpa using h2⟩

lemma eventually_globalThreshold_le (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      lowerDeviationThreshold delta n ≤
        ThickPoint.thickThreshold (scaleIndex delta n) (chosenThickDelta delta) := by
  filter_upwards [eventually_log_outerScale_bounds hdelta,
    eventually_log_gap_le_quarter delta, eventually_threshold_error_bounds hdelta,
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop 8)]
      with n hA hgap herr hL
  let L : ℝ := Real.log n
  let G : ℝ := L ^ gapExponent delta
  let A : ℝ := Real.log (ThickPoint.outerScale (scaleIndex delta n))
  have hAlower : L / 2 - G - 1 < A := by
    simpa [L, G, A] using hA.1
  have hAupperStrong : A ≤ L / 2 - G / 2 := by
    dsimp [A, L, G]
    linarith [hA.2]
  have hAupper : A ≤ L / 2 + G := by
    have hGnonneg : 0 ≤ G := by dsimp [G]; positivity
    linarith
  have hGquarter : G ≤ L / 4 := by simpa [L, G] using hgap
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hGone : 1 ≤ G := by
    dsimp [G]
    apply Real.one_le_rpow (by linarith)
    unfold gapExponent
    linarith [scaleSlack_pos hdelta]
  have hApos : 0 < A := by
    linarith
  have hAle : A ≤ L := by
    linarith
  have hsum : L + 2 * A ≤ 3 * L := by linarith
  have hdiff : L - 2 * A ≤ 4 * G := by
    linarith
  have hdeficit : L ^ 2 / Real.pi - 4 / Real.pi * A ^ 2 ≤
      20 * L ^ (1 + gapExponent delta) := by
    have hpi : 0 < Real.pi := Real.pi_pos
    have hprod : (L - 2 * A) * (L + 2 * A) ≤ 12 * L * G := by
      by_cases hd : L - 2 * A ≤ 0
      · have hright : 0 ≤ L + 2 * A := by positivity
        have : (L - 2 * A) * (L + 2 * A) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hd hright
        have : 0 ≤ 12 * L * G := by positivity
        linarith
      · have hd0 : 0 ≤ L - 2 * A := le_of_not_ge hd
        calc
          (L - 2 * A) * (L + 2 * A) ≤ (4 * G) * (3 * L) :=
            mul_le_mul hdiff hsum (by positivity) (by positivity)
          _ = 12 * L * G := by ring
    have hrewrite : L ^ (1 + gapExponent delta) = L * G := by
      dsimp [G]
      rw [Real.rpow_add hLpos, Real.rpow_one]
    rw [hrewrite]
    have hpiOne : (1 : ℝ) ≤ Real.pi := le_of_lt (by linarith [Real.pi_gt_three])
    calc
      L ^ 2 / Real.pi - 4 / Real.pi * A ^ 2 =
          ((L - 2 * A) * (L + 2 * A)) / Real.pi := by field_simp; ring
      _ ≤ (12 * L * G) / Real.pi := by gcongr
      _ ≤ 12 * L * G := (div_le_self (by positivity) hpiOne)
      _ ≤ 20 * (L * G) := by
        have hLG : 0 ≤ L * G := mul_nonneg hLpos.le (by positivity)
        linarith
  have hthickPow : A ^ (1 + chosenThickDelta delta) ≤
      L ^ (1 + chosenThickDelta delta) := by
    apply Real.rpow_le_rpow hApos.le hAle
    unfold chosenThickDelta
    linarith [scaleSlack_pos hdelta]
  unfold lowerDeviationThreshold ThickPoint.thickThreshold
  dsimp [L, A] at hdeficit hthickPow herr ⊢
  linarith

lemma eventually_thickThreshold_pos (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      0 < ThickPoint.thickThreshold (scaleIndex delta n) (chosenThickDelta delta) := by
  have hAtop : Tendsto (fun n : ℕ ↦
      Real.log (ThickPoint.outerScale (scaleIndex delta n))) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    have hqtop := (tendsto_scaleIndex_atTop delta).eventually (eventually_ge_atTop b)
    filter_upwards [hqtop, eventually_scaleIndex_pos delta] with n hqb hq
    exact hqb.trans (log_outerScale_ge_scale hq)
  have hexp : 1 + chosenThickDelta delta < 2 := by
    unfold chosenThickDelta
    linarith [scaleSlack_le_one_hundred delta]
  have hpow := hAtop.eventually
    (eventually_const_mul_rpow_le_half_rpow hexp (by norm_num : (0 : ℝ) ≤ 1))
  filter_upwards [hpow, hAtop.eventually (eventually_gt_atTop 0)] with n hpow hA
  unfold ThickPoint.thickThreshold
  have hcoef : (1 / 2 : ℝ) < 4 / Real.pi := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) Real.pi_pos]
    linarith [Real.pi_lt_four]
  have hA2 : 0 < Real.log (ThickPoint.outerScale (scaleIndex delta n)) ^ (2 : ℝ) :=
    Real.rpow_pos_of_pos hA _
  have hnatpow : Real.log (ThickPoint.outerScale (scaleIndex delta n)) ^ (2 : ℕ) =
      Real.log (ThickPoint.outerScale (scaleIndex delta n)) ^ (2 : ℝ) := by
    rw [Real.rpow_two]
  rw [hnatpow]
  nlinarith

/-! ## Enough complete deterministic blocks -/

lemma eventually_amplification_exponent_budget
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      Real.log 17 + Real.log n ^ (3 / 5 : ℝ) + 3 * scaleCost delta n ≤
        (3 / 4 : ℝ) * Real.log n ^ gapExponent delta := by
  have htarget : (3 / 5 : ℝ) < gapExponent delta := by
    unfold gapExponent
    linarith [scaleSlack_pos hdelta]
  have hcostGap := costExponent_lt_gapExponent hdelta
  have htargetSmall := tendsto_log_nat_atTop.eventually
    (eventually_const_mul_rpow_le_half_rpow htarget (by norm_num : (0 : ℝ) ≤ 4))
  have hcostSmall := tendsto_log_nat_atTop.eventually
    (eventually_const_mul_rpow_le_half_rpow hcostGap (by norm_num : (0 : ℝ) ≤ 4))
  have hgapPos : 0 < gapExponent delta := by
    unfold gapExponent
    linarith [scaleSlack_pos hdelta]
  have hgapLarge := ((tendsto_rpow_atTop hgapPos).comp tendsto_log_nat_atTop).eventually
    (eventually_ge_atTop (8 * Real.log 17))
  filter_upwards [htargetSmall, hcostSmall, hgapLarge,
    eventually_scaleIndex_bounds delta,
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop 4)]
      with n htargetN hcostN hgapN hqBounds hL
  simp only [Function.comp_apply] at hgapN
  have hqLeL : (scaleIndex delta n : ℝ) ≤ Real.log n := by
    linarith [hqBounds.2]
  have hcostNonneg : 0 ≤ costExponent delta :=
    (costExponent_pos hdelta).le
  have hscaleCost : scaleCost delta n ≤
      Real.log n ^ costExponent delta := by
    unfold scaleCost
    exact Real.rpow_le_rpow (by positivity) hqLeL hcostNonneg
  have htargetEighth : Real.log n ^ (3 / 5 : ℝ) ≤
      (1 / 8 : ℝ) * Real.log n ^ gapExponent delta := by linarith
  have hcostEighth : Real.log n ^ costExponent delta ≤
      (1 / 8 : ℝ) * Real.log n ^ gapExponent delta := by linarith
  have hscaleCostEighth : scaleCost delta n ≤
      (1 / 8 : ℝ) * Real.log n ^ gapExponent delta :=
    hscaleCost.trans hcostEighth
  have hlogEighth : Real.log 17 ≤
      (1 / 8 : ℝ) * Real.log n ^ gapExponent delta := by linarith
  calc
    Real.log 17 + Real.log n ^ (3 / 5 : ℝ) + 3 * scaleCost delta n ≤
        (1 / 8 : ℝ) * Real.log n ^ gapExponent delta +
          (1 / 8 : ℝ) * Real.log n ^ gapExponent delta +
            3 * ((1 / 8 : ℝ) * Real.log n ^ gapExponent delta) := by
              exact add_le_add (add_le_add hlogEighth htargetEighth)
                (mul_le_mul_of_nonneg_left hscaleCostEighth (by norm_num))
    _ ≤ (3 / 4 : ℝ) * Real.log n ^ gapExponent delta := by
      have hG0 : 0 ≤ Real.log n ^ gapExponent delta := by positivity
      linarith

lemma requiredBlockCount_cast_le (delta : ℝ) (n : ℕ)
    (hlog : 0 ≤ requiredBlockLog delta n) :
    (requiredBlockCount delta n : ℝ) ≤
      17 * Real.exp (requiredBlockLog delta n) := by
  have hceil := Nat.ceil_lt_add_one
    (by positivity : 0 ≤ 16 * Real.exp (requiredBlockLog delta n))
  have hexp : 1 ≤ Real.exp (requiredBlockLog delta n) :=
    Real.one_le_exp hlog
  unfold requiredBlockCount
  linarith

lemma eventually_requiredBlocks_fit {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      requiredBlockCount delta n * chosenBlockLength delta n ≤ n := by
  filter_upwards [eventually_blockLength_le_exp hdelta,
    eventually_amplification_exponent_budget hdelta,
    tendsto_log_nat_atTop.eventually (eventually_ge_atTop 1),
    eventually_ge_atTop 1] with n hblock hbudget hL hn
  let L : ℝ := Real.log n
  let G : ℝ := L ^ gapExponent delta
  let D : ℝ := requiredBlockLog delta n
  have hL0 : 0 ≤ L := by dsimp [L]; linarith
  have hD0 : 0 ≤ D := by
    dsimp [D, requiredBlockLog, scaleCost]
    positivity
  have hcount : (requiredBlockCount delta n : ℝ) ≤ 17 * Real.exp D := by
    simpa [D] using requiredBlockCount_cast_le delta n hD0
  have hblock' : (chosenBlockLength delta n : ℝ) ≤
      Real.exp (L - (3 / 2 : ℝ) * G) := by
    simpa [L, G] using hblock
  have hbudget' : Real.log 17 + D ≤ (3 / 4 : ℝ) * G := by
    dsimp [D, G, L, requiredBlockLog]
    linarith [hbudget]
  have hproductReal : (requiredBlockCount delta n : ℝ) *
      (chosenBlockLength delta n : ℝ) ≤ (n : ℝ) := by
    calc
      (requiredBlockCount delta n : ℝ) * chosenBlockLength delta n ≤
        (17 * Real.exp D) * Real.exp (L - (3 / 2 : ℝ) * G) :=
        mul_le_mul hcount hblock' (by positivity) (by positivity)
      _ = Real.exp (Real.log 17 + D + (L - (3 / 2 : ℝ) * G)) := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 17)]
      _ ≤ Real.exp L := by
        apply Real.exp_le_exp.mpr
        linarith [Real.rpow_nonneg hL0 (gapExponent delta)]
      _ = (n : ℝ) := by
        dsimp [L]
        rw [Real.exp_log]
        exact_mod_cast hn
  exact_mod_cast hproductReal

lemma eventually_enoughBlocks {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (Real.log n ^ (3 / 5 : ℝ)) ≤
        (chosenBlockCount delta n : ℝ) * oneBlockRate delta n := by
  filter_upwards [eventually_requiredBlocks_fit hdelta] with n hfit
  have hcount : requiredBlockCount delta n ≤ chosenBlockCount delta n := by
    unfold chosenBlockCount
    exact (Nat.le_div_iff_mul_le (chosenBlockLength_pos delta n)).2 hfit
  calc
    Real.exp (Real.log n ^ (3 / 5 : ℝ)) ≤
        (requiredBlockCount delta n : ℝ) * oneBlockRate delta n :=
      requiredBlockCount_rate delta n
    _ ≤ (chosenBlockCount delta n : ℝ) * oneBlockRate delta n := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcount
      · exact (oneBlockRate_pos delta n).le

/-! ## Canonical certificate and the three remaining annular comparisons -/

/-- A fixed harmless width exponent for the successful excursion profile. -/
def chosenProfileDelta : ℝ := 1 / 5

/-- The exact three probabilistic comparisons which remain after all
deterministic, measurability, exit-tail, small-ball, and amplification
parameters have been fixed. -/
structure AnnularComparisons (delta : ℝ) (n : ℕ) where
  /-- Annular Harnack/profile transfer for one marked point. -/
  onePointProfile : ∀ (i : Fin (chosenBlockCount delta n)) x,
    x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
    onePointBound delta n ≤ fairSteps.real
      (stoppedSuccessfulPointEvent
        ((i : ℕ) * chosenBlockLength delta n)
        (scaleIndex delta n) chosenProfileDelta x)
  /-- Terminal annular Harnack/disintegration transfer from a successful
  profile to the required thick local time. -/
  terminalThick : ∀ (i : Fin (chosenBlockCount delta n)) x,
    x ∈ ThickPoint.candidateBox (scaleIndex delta n) →
    (1 - terminalEpsilon) * fairSteps.real
        (stoppedSuccessfulPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta x) ≤
      fairSteps.real
        (stoppedThickPointEvent
          ((i : ℕ) * chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta
          (chosenThickDelta delta) x)
  /-- Summed two-point annular comparison, including every separation
  regime and the diagonal. -/
  pairMoment : ∀ i : Fin (chosenBlockCount delta n),
    (∑ x ∈ ThickPoint.candidateBox (scaleIndex delta n),
      ∑ y ∈ ThickPoint.candidateBox (scaleIndex delta n),
        fairSteps.real
          (stoppedThickPointEvent
              ((i : ℕ) * chosenBlockLength delta n)
              (scaleIndex delta n) chosenProfileDelta
              (chosenThickDelta delta) x ∩
            stoppedThickPointEvent
              ((i : ℕ) * chosenBlockLength delta n)
              (scaleIndex delta n) chosenProfileDelta
              (chosenThickDelta delta) y)) ≤
      pairMomentBound delta n

/-- For every sufficiently large target time, the three annular comparisons
produce the canonical `ScaleCertificate`; every other field is discharged
by the explicit scale lemmas above. -/
theorem eventually_scaleCertificate_of_annular
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, AnnularComparisons delta n →
      Nonempty (ScaleCertificate delta n) := by
  filter_upwards [eventually_candidateBox_card_pos delta,
    eventually_candidateBox_card_ge_exp_two_scale delta,
    eventually_pairPolynomial_le_exp_quarter_cost hdelta,
    eventually_thickThreshold_pos delta hdelta,
    eventually_globalThreshold_le delta hdelta,
    eventually_exitLoss_le delta,
    eventually_enoughBlocks hdelta]
      with n hbox hcard hpoly hthickPos hthreshold hexit henough
  intro analytic
  refine ⟨{
    scale := scaleIndex delta n
    blockCount := chosenBlockCount delta n
    blockLength := chosenBlockLength delta n
    blockLength_pos := chosenBlockLength_pos delta n
    profileDelta := chosenProfileDelta
    thickDelta := chosenThickDelta delta
    onePoint := onePointBound delta n
    epsilon := terminalEpsilon
    pairUpper := pairMomentBound delta n
    blockRate := oneBlockRate delta n
    epsilon_le_one := terminalEpsilon_le_one
    onePoint_nonneg := (onePointBound_pos delta n).le
    pairUpper_pos := pairMomentBound_pos_of_candidateBox hbox
    blocksFit := chosenBlocks_fit delta n
    thickThreshold_pos := hthickPos
    globalThreshold_le := hthreshold
    onePointProfile := analytic.onePointProfile
    terminalThick := analytic.terminalThick
    pairMoment := analytic.pairMoment
    oneBlockNumerical := ?_
    enoughBlocks := henough }⟩
  simpa [firstMomentBound] using
    (oneBlockNumerical_of_exit (delta := delta) (n := n) hcard hpoly hexit)

/-- Eventual validity of precisely the three annular comparison fields. -/
def HasAnnularComparisons : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    Nonempty (AnnularComparisons delta n)

theorem hasAppendixCertificates_of_annularComparisons
    (hannular : HasAnnularComparisons) : HasAppendixCertificates := by
  intro delta hdelta
  obtain ⟨N₁, hN₁⟩ := hannular delta hdelta
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp
    (eventually_scaleCertificate_of_annular hdelta)
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  exact hN₂ n (le_trans (le_max_right _ _) hn) (Classical.choice
    (hN₁ n (le_trans (le_max_left _ _) hn)))

/-- **Proposition 1.3 with only its genuine annular Harnack inputs.** -/
theorem hasPlanarMaximumLowerDeviation_of_annularComparisons
    (hannular : HasAnnularComparisons) :
    HasPlanarMaximumLowerDeviation simpleRandomWalk :=
  hasPlanarMaximumLowerDeviation_of_appendixCertificates
    (hasAppendixCertificates_of_annularComparisons hannular)

end

end Proposition13Scales
end Erdos1165
