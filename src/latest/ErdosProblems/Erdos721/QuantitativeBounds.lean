/- leanprover/lean4:v4.33.0 -/
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

import ErdosProblems.Erdos721.ImprovedLocalDensityStep

/-!
# Quantitative bookkeeping for the improved local iteration

This file converts the exact Croot--Sisask cardinality estimate into a
logarithmic density estimate and then into an explicit Chang rank bound.
The constants are deliberately generous; their role is to make every loss in
the finite density-increment iteration completely explicit.
-/

namespace Erdos721

open Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ENNReal Indicator mu NNReal Pointwise

namespace CyclicQuantitativeBounds

variable {N : ℕ} [NeZero N]

/-- The logarithmic weight used throughout the quantitative iteration. -/
noncomputable def curLog (x : ℝ) : ℝ := 1 + Real.log x⁻¹

lemma one_le_curLog {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    1 ≤ curLog x := by
  have : 0 ≤ Real.log x⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ hx0).2 hx1)
  simp only [curLog]
  linarith

/-- The natural-number moment used in Chang's lemma costs at most twice the
logarithmic weight. -/
lemma changMoment_cast_le {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    (CyclicChang.changMoment x : ℝ) ≤ 2 * curLog x := by
  have hlog : 0 ≤ Real.log x⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ hx0).2 hx1)
  have hceil : (⌈Real.log x⁻¹⌉₊ : ℝ) < Real.log x⁻¹ + 1 :=
    Nat.ceil_lt_add_one hlog
  simp only [CyclicChang.changMoment, Nat.cast_add, Nat.cast_one]
  dsimp only [curLog]
  linarith

lemma exp_half_le_three : Real.exp (1 / 2 : ℝ) ≤ 3 := by
  calc
    Real.exp (1 / 2 : ℝ) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
    _ ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)

lemma exp_two_le_nine : Real.exp (2 : ℝ) ≤ 9 := by
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith [Real.exp_one_lt_d9, Real.exp_pos 1]

/-- At the fixed spectral threshold `1/2`, Chang's rank is linear in the
logarithmic reciprocal density. -/
lemma changRankBound_half_le (X : Finset (ZMod N)) (hX : X.Nonempty) :
    (CyclicChang.changRankBound X (1 / 2) : ℝ) ≤
      8192 * curLog (CyclicChang.density X) := by
  let alpha := CyclicChang.density X
  have halpha0 : 0 < alpha := CyclicChang.density_pos hX
  have halpha1 : alpha ≤ 1 := CyclicChang.density_le_one X
  let R : ℝ :=
    (2 * Real.exp (1 / 2 : ℝ)) ^ 2 *
      (CyclicChang.changMoment alpha : ℝ) * Real.exp 2 / (1 / 2 : ℝ) ^ 2
  have hmoment : (CyclicChang.changMoment alpha : ℝ) ≤ 2 * curLog alpha :=
    changMoment_cast_le halpha0 halpha1
  have hRhalf : (1 / 2 : ℝ) ≤ R := by
    dsimp only [R]
    have hm : (1 : ℝ) ≤ CyclicChang.changMoment alpha := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (CyclicChang.changMoment_pos alpha))
    have he0 : 1 ≤ Real.exp (1 / 2 : ℝ) := by
      simpa using Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have he2 : 1 ≤ Real.exp (2 : ℝ) := by
      simpa using Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 2)
    calc
      (1 / 2 : ℝ) ≤ (2 * 1) ^ 2 * 1 * 1 / (1 / 2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 * Real.exp (1 / 2 : ℝ)) ^ 2 *
          (CyclicChang.changMoment alpha : ℝ) * Real.exp 2 /
            (1 / 2 : ℝ) ^ 2 := by gcongr
  have hceil : (CyclicChang.changRankBound X (1 / 2) : ℝ) ≤ 2 * R := by
    unfold CyclicChang.changRankBound
    have hRhalf' : (2 : ℝ)⁻¹ ≤
        (2 * Real.exp (1 / 2 : ℝ)) ^ 2 *
          (CyclicChang.changMoment (CyclicChang.density X) : ℝ) *
          Real.exp 2 / (1 / 2 : ℝ) ^ 2 := by
      simpa only [R, alpha, one_div] using hRhalf
    simpa only [R, alpha] using Nat.ceil_le_two_mul hRhalf'
  have hcur : 0 ≤ curLog alpha :=
    (one_le_curLog halpha0 halpha1).trans' zero_le_one
  calc
    (CyclicChang.changRankBound X (1 / 2) : ℝ) ≤ 2 * R := hceil
    _ ≤ 2 * ((2 * 3) ^ 2 *
        (CyclicChang.changMoment alpha : ℝ) * Real.exp 2 /
          (1 / 2 : ℝ) ^ 2) := by
      dsimp only [R]
      gcongr
      exact exp_half_le_three
    _ ≤ 2 * ((2 * 3) ^ 2 * (2 * curLog alpha) * Real.exp 2 /
          (1 / 2 : ℝ) ^ 2) := by
      gcongr
    _ ≤ 2 * ((2 * 3) ^ 2 * (2 * curLog alpha) * 9 /
          (1 / 2 : ℝ) ^ 2) := by
      gcongr
      exact exp_two_le_nine
    _ ≤ 8192 * curLog alpha := by
      norm_num
      nlinarith

/-- A power-law cardinality lower bound becomes an additive logarithmic
density bound. -/
lemma curLog_density_le_of_rpow_card_lower
    (S X : Finset (ZMod N)) {K cost : ℝ}
    (hK : 0 < K) (hS : S.Nonempty) (hX : X.Nonempty)
    (hbound : K ^ (-cost) * (S.card : ℝ) ≤ X.card) :
    curLog (CyclicChang.density X) ≤
      curLog ((S.card : ℝ) / N) + cost * Real.log K := by
  have hN : (0 : ℝ) < N := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hXcard : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hpow : 0 < K ^ (-cost) := Real.rpow_pos_of_pos hK _
  have hbase : 0 < K ^ (-cost) * (S.card : ℝ) := mul_pos hpow hScard
  have hlog := Real.log_le_log hbase hbound
  rw [Real.log_mul hpow.ne' hScard.ne', Real.log_rpow hK] at hlog
  unfold curLog CyclicChang.density
  rw [inv_div, inv_div, Real.log_div hN.ne' hXcard.ne',
    Real.log_div hN.ne' hScard.ne']
  linarith

/-- The positive cost appearing in the exact improved Croot--Sisask lower
bound. -/
noncomputable def improvedCrootCost
    (A₂ U : Finset (ZMod N)) (epsilon beta : ℝ) : ℝ :=
  4096 *
      ((⌈1 + Real.log
        (min 1 ((A₂.card : ℝ) / (U.card : ℝ)))⁻¹⌉ : ℤ) : ℝ) *
      (CyclicImprovedParameters.improvedExponent epsilon beta : ℝ) ^ 2 /
        (epsilon / 32) ^ 2

lemma improvedCrootLowerBound_eq_rpow
    (H : CyclicBohr.Set N) (A₂ U : Finset (ZMod N))
    (zeta alpha epsilon beta : ℝ) :
    CyclicImprovedLocalDensityIteration.improvedCrootLowerBound
        H A₂ U zeta alpha epsilon beta =
      (11 / (10 * alpha)) ^ (-improvedCrootCost A₂ U epsilon beta) *
        ((H.dilate zeta).carrier.card : ℝ) := by
  unfold CyclicImprovedLocalDensityIteration.improvedCrootLowerBound
    improvedCrootCost
  congr 2
  ring

lemma improvedCrootCost_nonneg
    (A₂ U : Finset (ZMod N)) {epsilon beta : ℝ}
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty) :
    0 ≤ improvedCrootCost A₂ U epsilon beta := by
  have hA₂card : (0 : ℝ) < A₂.card := by exact_mod_cast hA₂.card_pos
  have hUcard : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hratio : 0 < min 1 ((A₂.card : ℝ) / U.card) := by positivity
  have hratio1 : min 1 ((A₂.card : ℝ) / U.card) ≤ 1 := min_le_left _ _
  have hloginv : 0 ≤ Real.log
      (min 1 ((A₂.card : ℝ) / U.card))⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ hratio).2 hratio1)
  have hceil : (0 : ℝ) ≤
      ((⌈1 + Real.log
        (min 1 ((A₂.card : ℝ) / U.card))⁻¹⌉ : ℤ) : ℝ) := by
    exact_mod_cast Int.ceil_nonneg (by linarith)
  unfold improvedCrootCost
  positivity

/-- Doubling the dilation parameter costs at most `9^rank` in cardinality.
This is the radius-independent Bohr doubling estimate, applied at scale
`2 * zeta`; its half-radius dilate is exactly the scale `zeta`. -/
lemma card_two_dilate_le_nine_pow_rank_mul_card
    (H : CyclicBohr.Set N) {zeta : ℝ}
    (hHradius : 0 < H.radius) (hzeta : 0 < zeta) :
    (H.dilate (2 * zeta)).carrier.card ≤
      9 ^ H.rank * (H.dilate zeta).carrier.card := by
  let K := H.dilate (2 * zeta)
  have hKradius : 0 < K.radius := by
    simp only [K, CyclicBohr.Set.radius_dilate]
    positivity
  have hdouble :=
    CyclicBohr.card_carrier_le_nine_pow_rank_mul_card_half K hKradius
  have hhalf :
      (K.dilate (1 / 2 : ℝ)).carrier = (H.dilate zeta).carrier := by
    ext x
    simp only [K, CyclicBohr.Set.mem_carrier,
      CyclicBohr.Set.frequencies_dilate, CyclicBohr.Set.radius_dilate]
    have hradius :
        |(1 / 2 : ℝ)| * (|2 * zeta| * H.radius) = |zeta| * H.radius := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        abs_of_pos (mul_pos (by norm_num) hzeta), abs_of_pos hzeta]
      ring
    rw [hradius]
  simpa only [K, hhalf, CyclicBohr.Set.rank_dilate] using hdouble

/-- The logarithmic quotient used in the rank-free entropy is bounded by
the Bohr doubling loss plus the exact Croot--Sisask exponent. -/
lemma log_two_dilate_div_improvedCrootLowerBound_le
    (H : CyclicBohr.Set N) (A₂ U : Finset (ZMod N))
    {zeta alpha epsilon beta : ℝ}
    (hHradius : 0 < H.radius) (hzeta : 0 < zeta)
    (halpha : 0 < alpha) :
    Real.log
        (((H.dilate (2 * zeta)).carrier.card : ℝ) /
          CyclicImprovedLocalDensityIteration.improvedCrootLowerBound
            H A₂ U zeta alpha epsilon beta) ≤
      (H.rank : ℝ) * Real.log 9 +
        improvedCrootCost A₂ U epsilon beta *
          Real.log (11 / (10 * alpha)) := by
  let outer : ℝ := (H.dilate (2 * zeta)).carrier.card
  let inner : ℝ := (H.dilate zeta).carrier.card
  let cost := improvedCrootCost A₂ U epsilon beta
  let K : ℝ := 11 / (10 * alpha)
  have houter : 0 < outer := by
    dsimp only [outer]
    exact_mod_cast (H.dilate (2 * zeta)).carrier_nonempty.card_pos
  have hinner : 0 < inner := by
    dsimp only [inner]
    exact_mod_cast (H.dilate zeta).carrier_nonempty.card_pos
  have hK : 0 < K := by dsimp only [K]; positivity
  have hpow : 0 < K ^ (-cost) := Real.rpow_pos_of_pos hK _
  have hlower : 0 < K ^ (-cost) * inner := mul_pos hpow hinner
  have hcardNat :=
    card_two_dilate_le_nine_pow_rank_mul_card H hHradius hzeta
  have hcard : outer ≤ (9 : ℝ) ^ H.rank * inner := by
    dsimp only [outer, inner]
    exact_mod_cast hcardNat
  have hlogOuter :
      Real.log outer ≤
        (H.rank : ℝ) * Real.log 9 + Real.log inner := by
    have hlog := Real.log_le_log houter hcard
    rw [Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 9) _).ne'
      hinner.ne', Real.log_pow] at hlog
    exact hlog
  rw [improvedCrootLowerBound_eq_rpow]
  change Real.log (outer / (K ^ (-cost) * inner)) ≤
    (H.rank : ℝ) * Real.log 9 + cost * Real.log K
  rw [Real.log_div houter.ne' hlower.ne',
    Real.log_mul hpow.ne' hinner.ne', Real.log_rpow hK]
  linarith

/-- A real upper bound for the canonical integer entropy cutoff. -/
lemma rankFreeEntropy_cast_le
    (H : CyclicBohr.Set N) (A₂ U : Finset (ZMod N))
    {zeta alpha epsilon beta : ℝ}
    (hHradius : 0 < H.radius) (hzeta : 0 < zeta)
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hA₂ : A₂.Nonempty) (hU : U.Nonempty) :
    (CyclicImprovedLocalDensityIteration.rankFreeEntropy
        H A₂ U zeta alpha epsilon beta : ℝ) ≤
      8 * ((H.rank : ℝ) * Real.log 9 +
        improvedCrootCost A₂ U epsilon beta *
          Real.log (11 / (10 * alpha)) + Real.log 4) + 2 := by
  let E : ℝ := 2 * (Real.log
      (((H.dilate (2 * zeta)).carrier.card : ℝ) /
        CyclicImprovedLocalDensityIteration.improvedCrootLowerBound
          H A₂ U zeta alpha epsilon beta) + Real.log 4) /
      (1 / 2 : ℝ) ^ 2
  let P : ℝ := 8 * ((H.rank : ℝ) * Real.log 9 +
      improvedCrootCost A₂ U epsilon beta *
        Real.log (11 / (10 * alpha)) + Real.log 4)
  have hlog := log_two_dilate_div_improvedCrootLowerBound_le
    H A₂ U (epsilon := epsilon) (beta := beta)
      hHradius hzeta halpha0
  have hE : E ≤ P := by
    dsimp only [E, P]
    norm_num
    linarith
  have hcost : 0 ≤ improvedCrootCost A₂ U epsilon beta :=
    improvedCrootCost_nonneg A₂ U hA₂ hU
  have hlog9 : 0 ≤ Real.log 9 := Real.log_nonneg (by norm_num)
  have hKone : 1 ≤ 11 / (10 * alpha) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) halpha0)]
    nlinarith
  have hlogK : 0 ≤ Real.log (11 / (10 * alpha)) :=
    Real.log_nonneg hKone
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hP : 0 ≤ P := by
    dsimp only [P]
    positivity
  have hmax : max 0 E ≤ P := max_le hP hE
  have hceil : (⌈max 0 E⌉₊ : ℝ) < max 0 E + 1 :=
    Nat.ceil_lt_add_one (le_max_left _ _)
  unfold CyclicImprovedLocalDensityIteration.rankFreeEntropy
  change (⌈max 0 E⌉₊ + 1 : ℕ) ≤ P + 2
  push_cast
  linarith

/-- The exact shift-set lower bound returned by the improved local step gives
the logarithmic density estimate used by the rank recurrence. -/
lemma curLog_density_X_le_of_improvedCrootLowerBound
    (H : CyclicBohr.Set N) (A₂ U X : Finset (ZMod N))
    {zeta alpha epsilon beta : ℝ}
    (halpha : 0 < alpha) (hH : (H.dilate zeta).carrier.Nonempty)
    (hX : X.Nonempty)
    (hbound :
      CyclicImprovedLocalDensityIteration.improvedCrootLowerBound
          H A₂ U zeta alpha epsilon beta ≤ X.card) :
    curLog (CyclicChang.density X) ≤
      curLog (((H.dilate zeta).carrier.card : ℝ) / N) +
        improvedCrootCost A₂ U epsilon beta *
          Real.log (11 / (10 * alpha)) := by
  rw [improvedCrootLowerBound_eq_rpow] at hbound
  exact curLog_density_le_of_rpow_card_lower
    (H.dilate zeta).carrier X (by positivity) hH hX hbound

/-- The even moment used when lifting a local correlation discrepancy. -/
noncomputable def localMoment (gamma : ℝ) : ℕ :=
  2 * ⌈curLog gamma⌉₊

lemma localMoment_pos {gamma : ℝ} (hgamma0 : 0 < gamma)
    (hgamma1 : gamma ≤ 1) : 0 < localMoment gamma := by
  unfold localMoment
  have hcur : 0 < curLog gamma :=
    zero_lt_one.trans_le (one_le_curLog hgamma0 hgamma1)
  positivity

lemma localMoment_ne_zero {gamma : ℝ} (hgamma0 : 0 < gamma)
    (hgamma1 : gamma ≤ 1) : localMoment gamma ≠ 0 :=
  Nat.ne_of_gt (localMoment_pos hgamma0 hgamma1)

lemma localMoment_even (gamma : ℝ) : Even (localMoment gamma) := by
  unfold localMoment
  exact even_two_mul _

/-- The local lifting moment is at most four logarithmic weights. -/
lemma localMoment_cast_le {gamma : ℝ} (hgamma0 : 0 < gamma)
    (hgamma1 : gamma ≤ 1) :
    (localMoment gamma : ℝ) ≤ 4 * curLog gamma := by
  have hcur : 1 ≤ curLog gamma := one_le_curLog hgamma0 hgamma1
  calc
    (localMoment gamma : ℝ) = 2 * (⌈curLog gamma⌉₊ : ℝ) := by
      simp [localMoment]
    _ ≤ 2 * (2 * curLog gamma) := by
      gcongr
      exact Nat.ceil_le_two_mul
        (by linarith : (2 : ℝ)⁻¹ ≤ curLog gamma)
    _ = 4 * curLog gamma := by ring

lemma inv_rpow_curLog_le_exp_one
    {gamma : ℝ} (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    gamma⁻¹ ^ (curLog gamma)⁻¹ ≤ Real.exp 1 := by
  obtain rfl | hgamma1 := hgamma1.eq_or_lt
  · simp [curLog]
  have hx : 1 < gamma⁻¹ := (one_lt_inv₀ hgamma0).2 hgamma1
  have hlog : 0 < Real.log gamma⁻¹ := Real.log_pos hx
  calc
    gamma⁻¹ ^ (curLog gamma)⁻¹ ≤
        gamma⁻¹ ^ (Real.log gamma⁻¹)⁻¹ := by
      apply Real.rpow_le_rpow_of_exponent_le hx.le
      exact inv_anti₀ hlog (by simp [curLog])
    _ ≤ Real.exp 1 := gamma⁻¹.rpow_inv_log_le_exp_one

/-- The chosen moment makes the relative Hölder loss at most two. -/
lemma gamma_inv_rpow_inv_localMoment_le_two
    {gamma : ℝ} (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1) :
    gamma⁻¹ ^ ((localMoment gamma : ℝ)⁻¹) ≤ 2 := by
  have hcur0 : 0 < curLog gamma :=
    zero_lt_one.trans_le (one_le_curLog hgamma0 hgamma1)
  have hginv : 1 ≤ gamma⁻¹ := (one_le_inv₀ hgamma0).2 hgamma1
  have hceilpos : 0 < (⌈curLog gamma⌉₊ : ℝ) := by
    exact_mod_cast Nat.ceil_pos.mpr hcur0
  calc
    gamma⁻¹ ^ ((localMoment gamma : ℝ)⁻¹) =
        √(gamma⁻¹ ^ ((⌈curLog gamma⌉₊ : ℝ)⁻¹)) := by
      rw [sqrt_eq_rpow, one_div]
      unfold localMoment
      push_cast
      rw [mul_inv_rev, Real.rpow_mul]
      norm_num
      positivity
    _ ≤ √(gamma⁻¹ ^ ((curLog gamma)⁻¹ : ℝ)) := by
      apply Real.sqrt_le_sqrt
      exact Real.rpow_le_rpow_of_exponent_le hginv
        (inv_anti₀ hcur0 (Nat.le_ceil (curLog gamma)))
    _ ≤ √(Real.exp 1) := by
      gcongr
      exact inv_rpow_curLog_le_exp_one hgamma0 hgamma1
    _ ≤ √2.7182818286 := by
      gcongr
      exact Real.exp_one_lt_d9.le
    _ ≤ 2 := by
      rw [Real.sqrt_le_iff]
      norm_num

/-- With the fixed local error `1/16`, the sifting exponent is linear in the
logarithmic reciprocal density of the correlation test set. -/
lemma local_q_le {gamma : ℝ} (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1)
    {p' q : ℕ}
    (hp' : (p' : ℝ) ≤
      2 ^ 10 * (1 / 16 : ℝ)⁻¹ ^ 2 * localMoment gamma)
    (hq : q = max (2 * p')
      (2 ^ 4 *
        ⌈(1 / 16 : ℝ)⁻¹ * Real.log (256 / (1 / 16 : ℝ))⌉₊)) :
    (q : ℝ) ≤ 2 ^ 24 * curLog gamma := by
  have hcur : 1 ≤ curLog gamma := one_le_curLog hgamma0 hgamma1
  have hp := localMoment_cast_le hgamma0 hgamma1
  have hp'bound : (p' : ℝ) ≤ 2 ^ 20 * curLog gamma := by
    calc
      (p' : ℝ) ≤
          2 ^ 10 * (1 / 16 : ℝ)⁻¹ ^ 2 * localMoment gamma := hp'
      _ ≤ 2 ^ 10 * (1 / 16 : ℝ)⁻¹ ^ 2 *
          (4 * curLog gamma) := by
        gcongr
      _ = 2 ^ 20 * curLog gamma := by norm_num; ring
  have hlog : Real.log (256 / (1 / 16 : ℝ)) ≤ 4096 := by
    calc
      Real.log (256 / (1 / 16 : ℝ)) ≤ 256 / (1 / 16 : ℝ) :=
        Real.log_le_self (by norm_num)
      _ = 4096 := by norm_num
  have hceil :
      (⌈(1 / 16 : ℝ)⁻¹ *
        Real.log (256 / (1 / 16 : ℝ))⌉₊ : ℝ) ≤ 2 ^ 18 := by
    have hx0 : 0 ≤
        (1 / 16 : ℝ)⁻¹ * Real.log (256 / (1 / 16 : ℝ)) := by
      positivity
    exact (calc
      (⌈(1 / 16 : ℝ)⁻¹ *
          Real.log (256 / (1 / 16 : ℝ))⌉₊ : ℝ) <
          (1 / 16 : ℝ)⁻¹ * Real.log (256 / (1 / 16 : ℝ)) + 1 :=
        Nat.ceil_lt_add_one hx0
      _ ≤ 2 ^ 18 := by norm_num at hlog ⊢; linarith).le
  rw [hq]
  push_cast
  apply max_le
  · calc
      2 * (p' : ℝ) ≤ 2 * (2 ^ 20 * curLog gamma) := by gcongr
      _ ≤ 2 ^ 24 * curLog gamma := by nlinarith
  · calc
      (16 : ℝ) *
          (⌈(1 / 16 : ℝ)⁻¹ *
            Real.log (256 / (1 / 16 : ℝ))⌉₊ : ℝ) ≤
          16 * 2 ^ 18 := by gcongr
      _ ≤ 2 ^ 24 * curLog gamma := by
        norm_num at hcur ⊢
        nlinarith

lemma curLog_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    curLog y ≤ curLog x := by
  have hy : 0 < y := hx.trans_le hxy
  have hinv : y⁻¹ ≤ x⁻¹ := inv_anti₀ hx hxy
  have hlog := Real.log_le_log (inv_pos.mpr hy) hinv
  unfold curLog
  linarith

/-- Losing the fixed narrowing factor `1 - 1/8192` changes the logarithmic
reciprocal density by at most a harmless absolute factor. -/
lemma curLog_le_four_of_fixed_narrowing {x y : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (_hy1 : y ≤ 1)
    (hxy : (1 - 1 / 8192 : ℝ) * x ≤ y) :
    curLog y ≤ 4 * curLog x := by
  let c : ℝ := 1 - 1 / 8192
  have hc0 : 0 < c := by norm_num [c]
  have hcx0 : 0 < c * x := mul_pos hc0 hx0
  have hanti : curLog y ≤ curLog (c * x) :=
    curLog_anti hcx0 (by simpa only [c] using hxy)
  have hformula : curLog (c * x) = curLog x + Real.log c⁻¹ := by
    unfold curLog
    rw [mul_inv, Real.log_mul (inv_ne_zero hc0.ne') (inv_ne_zero hx0.ne')]
    ring
  have hloginv : Real.log c⁻¹ ≤ 2 := by
    calc
      Real.log c⁻¹ ≤ c⁻¹ := Real.log_le_self (inv_nonneg.mpr hc0.le)
      _ ≤ 2 := by norm_num [c]
  have hL : 1 ≤ curLog x := one_le_curLog hx0 hx1
  calc
    curLog y ≤ curLog (c * x) := hanti
    _ = curLog x + Real.log c⁻¹ := hformula
    _ ≤ curLog x + 2 := by linarith
    _ ≤ 4 * curLog x := by linarith

lemma curLog_pow_le {x : ℝ} {n : ℕ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hn : n ≠ 0) :
    curLog (x ^ n) ≤ (n : ℝ) * curLog x := by
  have hlog : 0 ≤ Real.log x⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ hx0).2 hx1)
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  unfold curLog
  rw [← inv_pow, Real.log_pow]
  nlinarith

/-- The auxiliary density `beta^(2q)/4` has logarithmic weight linear in
`q` and in the weight of `beta`. -/
lemma curLog_quarter_mul_pow_le {beta : ℝ} {q : ℕ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    curLog ((4 : ℝ)⁻¹ * beta ^ (2 * q)) ≤
      4 * ((q : ℝ) + 1) * curLog beta := by
  have hloginv : 0 ≤ Real.log beta⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ hbeta0).2 hbeta1)
  unfold curLog
  rw [mul_inv, inv_inv, ← inv_pow,
    Real.log_mul (by norm_num) (pow_pos (inv_pos.mpr hbeta0) _).ne',
    Real.log_pow]
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num) (by norm_num)]
    nlinarith [Real.log_two_lt_d9]
  push_cast
  nlinarith

/-- The logarithm of the Croot--Sisask small-doubling base is absorbed by
the auxiliary logarithmic density. -/
lemma log_croot_base_le_curLog {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    Real.log (11 / (10 * alpha)) ≤ curLog alpha := by
  have hloginv : 0 ≤ Real.log alpha⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ halpha0).2 halpha1)
  rw [show 11 / (10 * alpha) = (11 / 10 : ℝ) * alpha⁻¹ by
    field_simp [halpha0.ne']]
  rw [Real.log_mul (by norm_num) (inv_pos.mpr halpha0).ne']
  have hlog : Real.log (11 / 10 : ℝ) ≤ 1 :=
    (Real.log_le_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 11 / 10)).trans (by norm_num)
  unfold curLog
  linarith

/-- At fixed error `1/16`, the improved convolution exponent is linear in
the current logarithmic reciprocal density. -/
lemma improvedExponent_fixed_le {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    (CyclicImprovedParameters.improvedExponent (1 / 16) beta : ℝ) ≤
      2 ^ 15 * curLog beta := by
  have hloginv : 0 ≤ Real.log beta⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ hbeta0).2 hbeta1)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : (Real.log 2)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hlog2]
    nlinarith [Real.log_two_gt_d9]
  have hlogarg :
      Real.log (512 / ((1 / 16 : ℝ) * beta)) ≤
        8192 + Real.log beta⁻¹ := by
    rw [show 512 / ((1 / 16 : ℝ) * beta) =
        (8192 : ℝ) * beta⁻¹ by
      field_simp [hbeta0.ne']
      ring]
    rw [Real.log_mul (by norm_num) (inv_pos.mpr hbeta0).ne']
    have hlog8192 := Real.log_le_self (by norm_num : (0 : ℝ) ≤ 8192)
    linarith
  have hlogb :
      Real.logb 2 (512 / ((1 / 16 : ℝ) * beta)) ≤
        2 * (8192 + Real.log beta⁻¹) := by
    rw [Real.logb]
    calc
      Real.log (512 / ((1 / 16 : ℝ) * beta)) / Real.log 2 ≤
          (8192 + Real.log beta⁻¹) / Real.log 2 := by
        gcongr
      _ = (8192 + Real.log beta⁻¹) * (Real.log 2)⁻¹ := by ring
      _ ≤ (8192 + Real.log beta⁻¹) * 2 := by
        exact mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = 2 * (8192 + Real.log beta⁻¹) := by ring
  have hceil :=
    CyclicImprovedParameters.improvedExponent_lt_logb_add_one
      (epsilon := (1 / 16 : ℝ)) (beta := beta)
      (by norm_num) (by norm_num) hbeta0 hbeta1
  have hcur : 1 ≤ curLog beta := one_le_curLog hbeta0 hbeta1
  have hlogle : Real.log beta⁻¹ ≤ curLog beta := by
    unfold curLog
    linarith
  exact (calc
    (CyclicImprovedParameters.improvedExponent (1 / 16) beta : ℝ) <
        Real.logb 2 (512 / ((1 / 16 : ℝ) * beta)) + 1 := hceil
    _ ≤ 2 * (8192 + Real.log beta⁻¹) + 1 := by linarith
    _ ≤ 2 ^ 15 * curLog beta := by
      norm_num at hcur hlogle ⊢
      nlinarith).le

/-- If `A₂` has relative density `alpha` in `S`, while `U` has cardinality at
most `9^rank |S|`, then the logarithmic cardinal ratio in the Croot--Sisask
cost is bounded by `L(alpha) + rank log 9`. -/
lemma curLog_min_card_ratio_le
    (S A₂ U : Finset (ZMod N)) (rank : ℕ) {alpha : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hS : S.Nonempty) (hU : U.Nonempty)
    (hA₂dense : alpha * (S.card : ℝ) ≤ A₂.card)
    (hUcard : (U.card : ℝ) ≤ (9 : ℝ) ^ rank * S.card) :
    curLog (min 1 ((A₂.card : ℝ) / U.card)) ≤
      curLog alpha + (rank : ℝ) * Real.log 9 := by
  have hScard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hUcard0 : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hpow0 : (0 : ℝ) < 9 ^ rank := pow_pos (by norm_num) _
  have hpow1 : (1 : ℝ) ≤ 9 ^ rank := one_le_pow₀ (by norm_num)
  have ha0 : 0 < alpha / (9 : ℝ) ^ rank := div_pos halpha0 hpow0
  have ha1 : alpha / (9 : ℝ) ^ rank ≤ 1 := by
    rw [div_le_one hpow0]
    exact halpha1.trans hpow1
  have haratio : alpha / (9 : ℝ) ^ rank ≤
      (A₂.card : ℝ) / U.card := by
    rw [div_le_div_iff₀ hpow0 hUcard0]
    calc
      alpha * (U.card : ℝ) ≤
          alpha * ((9 : ℝ) ^ rank * S.card) := by
        gcongr
      _ = (alpha * (S.card : ℝ)) * (9 : ℝ) ^ rank := by ring
      _ ≤ (A₂.card : ℝ) * (9 : ℝ) ^ rank := by gcongr
  have hamin : alpha / (9 : ℝ) ^ rank ≤
      min 1 ((A₂.card : ℝ) / U.card) := le_min ha1 haratio
  calc
    curLog (min 1 ((A₂.card : ℝ) / U.card)) ≤
        curLog (alpha / (9 : ℝ) ^ rank) := curLog_anti ha0 hamin
    _ = curLog alpha + (rank : ℝ) * Real.log 9 := by
      unfold curLog
      rw [show (alpha / (9 : ℝ) ^ rank)⁻¹ =
          alpha⁻¹ * (9 : ℝ) ^ rank by field_simp [halpha0.ne']]
      rw [Real.log_mul (inv_pos.mpr halpha0).ne' hpow0.ne',
        Real.log_pow]
      ring

/-- Replacing the real logarithmic weight by the integer ceiling costs at
most a factor two. -/
lemma intCeil_curLog_min_card_ratio_le
    (A₂ U : Finset (ZMod N)) (hA₂ : A₂.Nonempty) (hU : U.Nonempty) :
    (((⌈1 + Real.log
      (min 1 ((A₂.card : ℝ) / U.card))⁻¹⌉ : ℤ) : ℝ)) ≤
      2 * curLog (min 1 ((A₂.card : ℝ) / U.card)) := by
  have hA₂card : (0 : ℝ) < A₂.card := by exact_mod_cast hA₂.card_pos
  have hUcard : (0 : ℝ) < U.card := by exact_mod_cast hU.card_pos
  have hratio0 : 0 < min 1 ((A₂.card : ℝ) / U.card) := by positivity
  have hratio1 : min 1 ((A₂.card : ℝ) / U.card) ≤ 1 := min_le_left _ _
  have hcur : 1 ≤ curLog (min 1 ((A₂.card : ℝ) / U.card)) :=
    one_le_curLog hratio0 hratio1
  have hceil :
      (((⌈curLog (min 1 ((A₂.card : ℝ) / U.card))⌉ : ℤ) : ℝ)) <
        curLog (min 1 ((A₂.card : ℝ) / U.card)) + 1 := by
    exact_mod_cast Int.ceil_lt_add_one
      (curLog (min 1 ((A₂.card : ℝ) / U.card)))
  have hbound :
      (((⌈curLog (min 1 ((A₂.card : ℝ) / U.card))⌉ : ℤ) : ℝ)) ≤
        2 * curLog (min 1 ((A₂.card : ℝ) / U.card)) :=
    hceil.le.trans (by linarith)
  simpa only [curLog] using hbound

/-- Complete polynomial upper bound for the Croot--Sisask exponent in one
improved local step.  Here `rank` is the current Bohr rank and `q` is the
sifting exponent. -/
lemma improvedCrootCost_fixed_le
    (S A₂ U : Finset (ZMod N)) (rank q : ℕ) {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hS : S.Nonempty) (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hq : (q : ℝ) ≤ 2 ^ 24 * curLog beta)
    (hA₂dense :
      (4 : ℝ)⁻¹ * beta ^ (2 * q) * (S.card : ℝ) ≤ A₂.card)
    (hUcard : (U.card : ℝ) ≤ (9 : ℝ) ^ rank * S.card) :
    improvedCrootCost A₂ U (1 / 16) beta ≤
      2 ^ 96 * ((rank : ℝ) + curLog beta ^ 2) * curLog beta ^ 2 := by
  let L := curLog beta
  let alpha := (4 : ℝ)⁻¹ * beta ^ (2 * q)
  have hL1 : 1 ≤ L := one_le_curLog hbeta0 hbeta1
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have halpha0 : 0 < alpha := by dsimp [alpha]; positivity
  have hpow1 : beta ^ (2 * q) ≤ 1 := pow_le_one₀ hbeta0.le hbeta1
  have halpha1 : alpha ≤ 1 := by
    dsimp [alpha]
    calc
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (4 : ℝ)⁻¹ * 1 := by gcongr
      _ ≤ 1 := by norm_num
  have hlogalpha : curLog alpha ≤ 2 ^ 27 * L ^ 2 := by
    calc
      curLog alpha ≤ 4 * ((q : ℝ) + 1) * L :=
        curLog_quarter_mul_pow_le hbeta0 hbeta1
      _ ≤ 4 * (2 ^ 24 * L + 1) * L := by gcongr
      _ ≤ 2 ^ 27 * L ^ 2 := by
        nlinarith [sq_nonneg L]
  have hlog9 : Real.log 9 ≤ 9 := Real.log_le_self (by norm_num)
  have hratio := curLog_min_card_ratio_le S A₂ U rank halpha0 halpha1
    hS hU (by simpa only [alpha] using hA₂dense) hUcard
  have hratio' : curLog (min 1 ((A₂.card : ℝ) / U.card)) ≤
      2 ^ 30 * ((rank : ℝ) + L ^ 2) := by
    calc
      curLog (min 1 ((A₂.card : ℝ) / U.card)) ≤
          curLog alpha + (rank : ℝ) * Real.log 9 := hratio
      _ ≤ 2 ^ 27 * L ^ 2 + (rank : ℝ) * 9 := by gcongr
      _ ≤ 2 ^ 30 * ((rank : ℝ) + L ^ 2) := by
        have hrank : (0 : ℝ) ≤ rank := by positivity
        nlinarith
  have hceil := intCeil_curLog_min_card_ratio_le A₂ U hA₂ hU
  have hceil' :
      (((⌈1 + Real.log
        (min 1 ((A₂.card : ℝ) / U.card))⁻¹⌉ : ℤ) : ℝ)) ≤
        2 ^ 31 * ((rank : ℝ) + L ^ 2) := by
    exact hceil.trans (by nlinarith)
  have hk := improvedExponent_fixed_le hbeta0 hbeta1
  have hk2 :
      (CyclicImprovedParameters.improvedExponent (1 / 16) beta : ℝ) ^ 2 ≤
        2 ^ 30 * L ^ 2 := by
    nlinarith [sq_nonneg
      ((CyclicImprovedParameters.improvedExponent (1 / 16) beta : ℝ) -
        2 ^ 15 * L)]
  unfold improvedCrootCost
  dsimp only [L] at hceil' hk2 ⊢
  calc
    4096 *
          (((⌈1 + Real.log
            (min 1 ((A₂.card : ℝ) / U.card))⁻¹⌉ : ℤ) : ℝ)) *
          (CyclicImprovedParameters.improvedExponent (1 / 16) beta : ℝ) ^ 2 /
          ((1 / 16 : ℝ) / 32) ^ 2 ≤
        4096 * (2 ^ 31 * ((rank : ℝ) + curLog beta ^ 2)) *
          (2 ^ 30 * curLog beta ^ 2) / ((1 / 16 : ℝ) / 32) ^ 2 := by
      gcongr
    _ ≤ 2 ^ 96 * ((rank : ℝ) + curLog beta ^ 2) *
          curLog beta ^ 2 := by
      norm_num
      nlinarith [sq_nonneg (curLog beta),
        (Nat.cast_nonneg rank : (0 : ℝ) ≤ rank)]

/-- Complete polynomial bound for the canonical rank-free entropy cutoff at
the fixed error used by the density iteration. -/
lemma rankFreeEntropy_fixed_le
    (H : CyclicBohr.Set N) (S A₂ U : Finset (ZMod N)) (q : ℕ)
    {zeta beta alpha : ℝ}
    (halpha : alpha = (4 : ℝ)⁻¹ * beta ^ (2 * q))
    (hHradius : 0 < H.radius) (hzeta : 0 < zeta)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hS : S.Nonempty) (hA₂ : A₂.Nonempty) (hU : U.Nonempty)
    (hq : (q : ℝ) ≤ 2 ^ 24 * curLog beta)
    (hA₂dense :
      (4 : ℝ)⁻¹ * beta ^ (2 * q) * (S.card : ℝ) ≤ A₂.card)
    (hUcard : (U.card : ℝ) ≤ (9 : ℝ) ^ H.rank * S.card) :
    (CyclicImprovedLocalDensityIteration.rankFreeEntropy
        H A₂ U zeta alpha (1 / 16) beta : ℝ) ≤
      2 ^ 128 * ((H.rank : ℝ) + curLog beta ^ 2) * curLog beta ^ 4 := by
  subst alpha
  let L := curLog beta
  let Q := ((H.rank : ℝ) + L ^ 2) * L ^ 4
  have hL1 : 1 ≤ L := one_le_curLog hbeta0 hbeta1
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have halpha0 : 0 < (4 : ℝ)⁻¹ * beta ^ (2 * q) := by positivity
  have hpow1 : beta ^ (2 * q) ≤ 1 := pow_le_one₀ hbeta0.le hbeta1
  have halpha1 : (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ 1 := by
    calc
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (4 : ℝ)⁻¹ * 1 := by gcongr
      _ ≤ 1 := by norm_num
  have hlogalpha : curLog ((4 : ℝ)⁻¹ * beta ^ (2 * q)) ≤
      2 ^ 27 * L ^ 2 := by
    calc
      curLog ((4 : ℝ)⁻¹ * beta ^ (2 * q)) ≤
          4 * ((q : ℝ) + 1) * L :=
        curLog_quarter_mul_pow_le hbeta0 hbeta1
      _ ≤ 4 * (2 ^ 24 * L + 1) * L := by gcongr
      _ ≤ 2 ^ 27 * L ^ 2 := by
        nlinarith [sq_nonneg L]
  have hlogK : Real.log (11 / (10 * ((4 : ℝ)⁻¹ * beta ^ (2 * q)))) ≤
      2 ^ 27 * L ^ 2 :=
    (log_croot_base_le_curLog halpha0 halpha1).trans hlogalpha
  have hcost := improvedCrootCost_fixed_le S A₂ U H.rank q
    hbeta0 hbeta1 hS hA₂ hU hq
    hA₂dense hUcard
  have hcost0 : 0 ≤ improvedCrootCost A₂ U (1 / 16) beta :=
    improvedCrootCost_nonneg A₂ U hA₂ hU
  have hlogK0 : 0 ≤
      Real.log (11 / (10 * ((4 : ℝ)⁻¹ * beta ^ (2 * q)))) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (mul_pos (by norm_num) halpha0)]
    nlinarith
  have hcostlog :
      improvedCrootCost A₂ U (1 / 16) beta *
          Real.log (11 / (10 * ((4 : ℝ)⁻¹ * beta ^ (2 * q)))) ≤
        2 ^ 123 * Q := by
    calc
      improvedCrootCost A₂ U (1 / 16) beta *
          Real.log (11 / (10 * ((4 : ℝ)⁻¹ * beta ^ (2 * q)))) ≤
          (2 ^ 96 * ((H.rank : ℝ) + L ^ 2) * L ^ 2) *
            (2 ^ 27 * L ^ 2) := by gcongr
      _ = 2 ^ 123 * Q := by
        dsimp only [Q]
        norm_num
        ring
  have hQ1 : 1 ≤ Q := by
    have hL2 : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
    have hL4 : 1 ≤ L ^ 4 := by nlinarith [sq_nonneg (L ^ 2 - 1)]
    dsimp only [Q]
    calc
      (1 : ℝ) ≤ ((H.rank : ℝ) + L ^ 2) * 1 := by
        have hrank0 : (0 : ℝ) ≤ H.rank := Nat.cast_nonneg _
        nlinarith
      _ ≤ ((H.rank : ℝ) + L ^ 2) * L ^ 4 := by
        gcongr
  have hrankQ : (H.rank : ℝ) ≤ Q := by
    have hL4 : 1 ≤ L ^ 4 := by
      have hL2 : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
      nlinarith [sq_nonneg (L ^ 2 - 1)]
    dsimp only [Q]
    have hrank0 : (0 : ℝ) ≤ H.rank := Nat.cast_nonneg _
    nlinarith [mul_nonneg (add_nonneg hrank0 (sq_nonneg L))
      (pow_nonneg hL0 4)]
  have hlog9 : Real.log 9 ≤ 9 := Real.log_le_self (by norm_num)
  have hlog4 : Real.log 4 ≤ 4 := Real.log_le_self (by norm_num)
  have hranklog : (H.rank : ℝ) * Real.log 9 ≤ 9 * Q := by
    calc
      (H.rank : ℝ) * Real.log 9 ≤ (H.rank : ℝ) * 9 := by
        gcongr
      _ ≤ Q * 9 := by gcongr
      _ = 9 * Q := by ring
  have hent := rankFreeEntropy_cast_le H A₂ U hHradius hzeta
    halpha0 halpha1 hA₂ hU (epsilon := (1 / 16 : ℝ)) (beta := beta)
  have hfinal :
    (CyclicImprovedLocalDensityIteration.rankFreeEntropy
        H A₂ U zeta ((4 : ℝ)⁻¹ * beta ^ (2 * q))
          (1 / 16) beta : ℝ) ≤ 2 ^ 128 * Q
      := by
    calc
      (CyclicImprovedLocalDensityIteration.rankFreeEntropy
          H A₂ U zeta ((4 : ℝ)⁻¹ * beta ^ (2 * q))
            (1 / 16) beta : ℝ) ≤
          8 * ((H.rank : ℝ) * Real.log 9 +
            improvedCrootCost A₂ U (1 / 16) beta *
              Real.log
                (11 / (10 * ((4 : ℝ)⁻¹ * beta ^ (2 * q)))) +
              Real.log 4) + 2 := hent
      _ ≤ 8 * (9 * Q + 2 ^ 123 * Q + 4) + 2 := by
        gcongr
      _ ≤ 2 ^ 128 * Q := by
        norm_num at hQ1 ⊢
        linarith
  calc
    (CyclicImprovedLocalDensityIteration.rankFreeEntropy
        H A₂ U zeta ((4 : ℝ)⁻¹ * beta ^ (2 * q))
          (1 / 16) beta : ℝ) ≤ 2 ^ 128 * Q := hfinal
    _ = 2 ^ 128 * ((H.rank : ℝ) + curLog beta ^ 2) *
        curLog beta ^ 4 := by
      dsimp only [Q, L]
      ring

/-! ## Rank-independent reflected entropy -/

lemma reflectedCrootCost_eq_improvedCrootCost
    (A₁ U : Finset (ZMod N)) (epsilon beta : ℝ) :
    CyclicImprovedLocalDensityIteration.reflectedCrootCost
        A₁ U epsilon beta = improvedCrootCost A₁ U epsilon beta := by
  rfl

/-- Real upper bound for the stable-carrier entropy ceiling. -/
lemma reflectedStableEntropy_cast_le
    (A₁ U : Finset (ZMod N)) {alpha epsilon beta : ℝ}
    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hA₁ : A₁.Nonempty) (hU : U.Nonempty) :
    (CyclicImprovedLocalDensityIteration.reflectedStableEntropy
        A₁ U alpha epsilon beta : ℝ) ≤
      8 * (improvedCrootCost A₁ U epsilon beta *
        Real.log (11 / (10 * alpha)) + Real.log 4) + 2 := by
  let cost := improvedCrootCost A₁ U epsilon beta
  let E : ℝ := 2 * (cost * Real.log (11 / (10 * alpha)) + Real.log 4) /
    (1 / 2 : ℝ) ^ 2
  let P : ℝ := 8 * (cost * Real.log (11 / (10 * alpha)) + Real.log 4)
  have hcost : 0 ≤ cost := by
    dsimp only [cost]
    exact improvedCrootCost_nonneg A₁ U hA₁ hU
  have hKone : 1 ≤ 11 / (10 * alpha) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) halpha0)]
    nlinarith
  have hlogK : 0 ≤ Real.log (11 / (10 * alpha)) :=
    Real.log_nonneg hKone
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hEP : E = P := by
    dsimp only [E, P]
    norm_num
    ring
  have hmax : max 0 E ≤ P := max_le hP hEP.le
  have hceil : (⌈max 0 E⌉₊ : ℝ) < max 0 E + 1 :=
    Nat.ceil_lt_add_one (le_max_left _ _)
  unfold CyclicImprovedLocalDensityIteration.reflectedStableEntropy
  rw [reflectedCrootCost_eq_improvedCrootCost]
  change (⌈max 0 E⌉₊ + 1 : ℕ) ≤ P + 2
  push_cast
  linarith

/-- The sifted correlation support is contained in one slightly enlarged
regular Bohr carrier.  This is the cardinality estimate `|U| ≤ 2|B'|` used
in the source; the generous constant `9` is convenient for the polynomial
bookkeeping below. -/
lemma sifted_support_card_le_nine_mul_inner
    (H : CyclicBohr.Set N) (A₁ A₂ T U : Finset (ZMod N)) (x : ZMod N)
    {u zeta : ℝ}
    (hzeta : 0 ≤ zeta) (hzetau : zeta ≤ u)
    (hA₁ : A₁ ⊆ (H.dilate (u - zeta)).carrier)
    (hA₂ : A₂ ⊆ CyclicLocalSifting.reflectedTranslate T x)
    (hT : T ⊆ (H.dilate zeta).carrier)
    (hU : U ⊆ A₁ - A₂)
    (hregular :
      10 * (H.dilate (u + zeta)).carrier.card ≤
        11 * (H.dilate (u - zeta)).carrier.card) :
    (U.card : ℝ) ≤ 9 * (H.dilate (u - zeta)).carrier.card := by
  have htranslate : x +ᵥ U ⊆ (H.dilate (u + zeta)).carrier := by
    intro y hy
    rw [Finset.mem_vadd_finset] at hy
    obtain ⟨z, hzU, rfl⟩ := hy
    have hzDiff := hU hzU
    rw [Finset.mem_sub] at hzDiff
    obtain ⟨a, ha, b, hb, rfl⟩ := hzDiff
    have hb' := hA₂ hb
    rw [CyclicLocalSifting.reflectedTranslate, Finset.mem_vadd_finset] at hb'
    obtain ⟨nt, hnt, hbEq⟩ := hb'
    obtain ⟨t, ht, hntEq⟩ := Finset.mem_neg.mp hnt
    subst nt
    have hbEq' : b = x + -t := by simpa [vadd_eq_add] using hbEq.symm
    subst b
    have hadd := CyclicBohr.Set.add_mem_dilate
      (B := H) (sub_nonneg.mpr hzetau) hzeta (hA₁ ha) (hT ht)
    have hmono := CyclicBohr.Set.dilate_mono H
      (add_nonneg (sub_nonneg.mpr hzetau) hzeta)
      (by linarith : (u - zeta) + zeta ≤ u + zeta)
    have hmem := hmono hadd
    convert hmem using 1 <;>
      simp only [vadd_eq_add, sub_eq_add_neg] <;> abel
  have hcardTranslate : (x +ᵥ U).card = U.card :=
    Finset.card_vadd_finset x U
  have hcardOuter : U.card ≤ (H.dilate (u + zeta)).carrier.card := by
    rw [← hcardTranslate]
    exact Finset.card_le_card htranslate
  have hinnerNonzero : 0 < (H.dilate (u - zeta)).carrier.card :=
    (H.dilate (u - zeta)).carrier_nonempty.card_pos
  have hnat : U.card ≤ 9 * (H.dilate (u - zeta)).carrier.card := by
    omega
  exact_mod_cast hnat

/-- At the fixed error of the iteration, the stable-carrier entropy is a
degree-six polynomial in the current logarithmic reciprocal density. -/
lemma reflectedStableEntropy_fixed_le
    (S A₁ U : Finset (ZMod N)) (q : ℕ) {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hS : S.Nonempty) (hA₁ : A₁.Nonempty) (hU : U.Nonempty)
    (hq : (q : ℝ) ≤ 2 ^ 24 * curLog beta)
    (hA₁dense :
      (4 : ℝ)⁻¹ * beta ^ (2 * q) * (S.card : ℝ) ≤ A₁.card)
    (hUcard : (U.card : ℝ) ≤ (9 : ℝ) * S.card) :
    (CyclicImprovedLocalDensityIteration.reflectedStableEntropy
        A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) (1 / 16) beta : ℝ) ≤
      2 ^ 132 * curLog beta ^ 6 := by
  let L := curLog beta
  let alpha := (4 : ℝ)⁻¹ * beta ^ (2 * q)
  have hL1 : 1 ≤ L := one_le_curLog hbeta0 hbeta1
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have halpha0 : 0 < alpha := by dsimp only [alpha]; positivity
  have hpow1 : beta ^ (2 * q) ≤ 1 := pow_le_one₀ hbeta0.le hbeta1
  have halpha1 : alpha ≤ 1 := by
    dsimp only [alpha]
    calc
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (4 : ℝ)⁻¹ * 1 := by gcongr
      _ ≤ 1 := by norm_num
  have hlogalpha : curLog alpha ≤ 2 ^ 27 * L ^ 2 := by
    calc
      curLog alpha ≤ 4 * ((q : ℝ) + 1) * L :=
        curLog_quarter_mul_pow_le hbeta0 hbeta1
      _ ≤ 4 * (2 ^ 24 * L + 1) * L := by gcongr
      _ ≤ 2 ^ 27 * L ^ 2 := by
        nlinarith [sq_nonneg L]
  have hlogK : Real.log (11 / (10 * alpha)) ≤ 2 ^ 27 * L ^ 2 :=
    (log_croot_base_le_curLog halpha0 halpha1).trans hlogalpha
  have hUcard' : (U.card : ℝ) ≤ (9 : ℝ) ^ (1 : ℕ) * S.card := by
    simpa using hUcard
  have hcostRaw := improvedCrootCost_fixed_le S A₁ U 1 q
    hbeta0 hbeta1 hS hA₁ hU hq
    (by simpa only [alpha] using hA₁dense) hUcard'
  have hcost : improvedCrootCost A₁ U (1 / 16) beta ≤ 2 ^ 99 * L ^ 4 := by
    calc
      improvedCrootCost A₁ U (1 / 16) beta ≤
          2 ^ 96 * ((1 : ℝ) + L ^ 2) * L ^ 2 := by
        simpa only [Nat.cast_one] using hcostRaw
      _ ≤ 2 ^ 99 * L ^ 4 := by
        have hL2 : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
        nlinarith [sq_nonneg (L ^ 2)]
  have hcost0 : 0 ≤ improvedCrootCost A₁ U (1 / 16) beta :=
    improvedCrootCost_nonneg A₁ U hA₁ hU
  have hlogK0 : 0 ≤ Real.log (11 / (10 * alpha)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (mul_pos (by norm_num) halpha0)]
    nlinarith
  have hcostlog :
      improvedCrootCost A₁ U (1 / 16) beta *
          Real.log (11 / (10 * alpha)) ≤ 2 ^ 126 * L ^ 6 := by
    calc
      improvedCrootCost A₁ U (1 / 16) beta *
          Real.log (11 / (10 * alpha)) ≤
          (2 ^ 99 * L ^ 4) * (2 ^ 27 * L ^ 2) := by gcongr
      _ = 2 ^ 126 * L ^ 6 := by norm_num; ring
  have hent := reflectedStableEntropy_cast_le A₁ U
    halpha0 halpha1 hA₁ hU (epsilon := (1 / 16 : ℝ)) (beta := beta)
  have hlog4 : Real.log 4 ≤ 4 := Real.log_le_self (by norm_num)
  have hL6 : 1 ≤ L ^ 6 := by
    have hL2 : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
    have hL4 : 1 ≤ L ^ 4 := by
      nlinarith [sq_nonneg (L ^ 2 - 1)]
    calc
      (1 : ℝ) ≤ L ^ 2 * L ^ 4 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hL2) (sub_nonneg.mpr hL4)]
      _ = L ^ 6 := by ring
  simpa only [alpha, L] using (hent.trans (by
    calc
      8 * (improvedCrootCost A₁ U (1 / 16) beta *
          Real.log (11 / (10 * alpha)) + Real.log 4) + 2 ≤
          8 * (2 ^ 126 * L ^ 6 + 4) + 2 := by gcongr
      _ ≤ 2 ^ 132 * L ^ 6 := by
        norm_num at hL6 ⊢
        linarith))

/-- Rank-independent entropy bound with a common logarithmic budget.  This
form is used in the nested step because the sifting moment is controlled by
the inner test density, while the Croot--Sisask exponent uses the outer
density; both logarithmic reciprocals are bounded by the current state's
single budget `L`. -/
lemma reflectedStableEntropy_common_le
    (S A₁ U : Finset (ZMod N)) (q : ℕ) {beta L : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hL1 : 1 ≤ L)
    (hlogbeta : curLog beta ≤ 4 * L)
    (hS : S.Nonempty) (hA₁ : A₁.Nonempty) (hU : U.Nonempty)
    (hq : (q : ℝ) ≤ 2 ^ 26 * L)
    (hA₁dense :
      (4 : ℝ)⁻¹ * beta ^ (2 * q) * (S.card : ℝ) ≤ A₁.card)
    (hUcard : (U.card : ℝ) ≤ (9 : ℝ) * S.card) :
    (CyclicImprovedLocalDensityIteration.reflectedStableEntropy
        A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) (1 / 16) beta : ℝ) ≤
      2 ^ 140 * L ^ 6 := by
  let alpha := (4 : ℝ)⁻¹ * beta ^ (2 * q)
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hcur0 : 0 ≤ curLog beta :=
    zero_le_one.trans (one_le_curLog hbeta0 hbeta1)
  have halpha0 : 0 < alpha := by dsimp only [alpha]; positivity
  have hpow1 : beta ^ (2 * q) ≤ 1 := pow_le_one₀ hbeta0.le hbeta1
  have halpha1 : alpha ≤ 1 := by
    dsimp only [alpha]
    calc
      (4 : ℝ)⁻¹ * beta ^ (2 * q) ≤ (4 : ℝ)⁻¹ * 1 := by gcongr
      _ ≤ 1 := by norm_num
  have hlogalpha : curLog alpha ≤ 2 ^ 31 * L ^ 2 := by
    calc
      curLog alpha ≤ 4 * ((q : ℝ) + 1) * curLog beta :=
        curLog_quarter_mul_pow_le hbeta0 hbeta1
      _ ≤ 4 * (2 ^ 26 * L + 1) * (4 * L) := by gcongr
      _ ≤ 2 ^ 31 * L ^ 2 := by
        nlinarith [sq_nonneg L]
  have hUcard' : (U.card : ℝ) ≤ (9 : ℝ) ^ (1 : ℕ) * S.card := by
    simpa using hUcard
  have hratio := curLog_min_card_ratio_le S A₁ U 1 halpha0 halpha1
    hS hU (by simpa only [alpha] using hA₁dense) hUcard'
  have hlog9 : Real.log 9 ≤ 9 := Real.log_le_self (by norm_num)
  have hratio' : curLog (min 1 ((A₁.card : ℝ) / U.card)) ≤
      2 ^ 32 * L ^ 2 := by
    calc
      curLog (min 1 ((A₁.card : ℝ) / U.card)) ≤
          curLog alpha + (1 : ℝ) * Real.log 9 := by
            simpa only [Nat.cast_one] using hratio
      _ ≤ 2 ^ 31 * L ^ 2 + 9 := by
        simpa only [one_mul] using add_le_add hlogalpha hlog9
      _ ≤ 2 ^ 32 * L ^ 2 := by
        have hL2 : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
        norm_num at hL2 ⊢
        nlinarith
  have hceil := intCeil_curLog_min_card_ratio_le A₁ U hA₁ hU
  have hceil' :
      (((⌈1 + Real.log
        (min 1 ((A₁.card : ℝ) / U.card))⁻¹⌉ : ℤ) : ℝ)) ≤
        2 ^ 33 * L ^ 2 := hceil.trans (by nlinarith)
  have hk := improvedExponent_fixed_le hbeta0 hbeta1
  have hkBound :
      (CyclicImprovedParameters.improvedExponent (1 / 16) beta : ℝ) ≤
        2 ^ 17 * L := by
    calc
      (CyclicImprovedParameters.improvedExponent (1 / 16) beta : ℝ) ≤
          2 ^ 15 * curLog beta := hk
      _ ≤ 2 ^ 15 * (4 * L) := by gcongr
      _ = 2 ^ 17 * L := by norm_num; ring
  have hk0 : (0 : ℝ) ≤
      CyclicImprovedParameters.improvedExponent (1 / 16) beta := by
    positivity
  have hk2 :
      (CyclicImprovedParameters.improvedExponent (1 / 16) beta : ℝ) ^ 2 ≤
        2 ^ 34 * L ^ 2 := by
    nlinarith [sq_nonneg
      ((CyclicImprovedParameters.improvedExponent (1 / 16) beta : ℝ) -
        2 ^ 17 * L)]
  have hcost : improvedCrootCost A₁ U (1 / 16) beta ≤
      2 ^ 100 * L ^ 4 := by
    unfold improvedCrootCost
    calc
      4096 *
          (((⌈1 + Real.log
            (min 1 ((A₁.card : ℝ) / U.card))⁻¹⌉ : ℤ) : ℝ)) *
          (CyclicImprovedParameters.improvedExponent (1 / 16) beta : ℝ) ^ 2 /
          ((1 / 16 : ℝ) / 32) ^ 2 ≤
        4096 * (2 ^ 33 * L ^ 2) * (2 ^ 34 * L ^ 2) /
          ((1 / 16 : ℝ) / 32) ^ 2 := by gcongr
      _ ≤ 2 ^ 100 * L ^ 4 := by
        norm_num
        nlinarith [sq_nonneg L]
  have hlogK : Real.log (11 / (10 * alpha)) ≤ 2 ^ 31 * L ^ 2 :=
    (log_croot_base_le_curLog halpha0 halpha1).trans hlogalpha
  have hcost0 : 0 ≤ improvedCrootCost A₁ U (1 / 16) beta :=
    improvedCrootCost_nonneg A₁ U hA₁ hU
  have hlogK0 : 0 ≤ Real.log (11 / (10 * alpha)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (mul_pos (by norm_num) halpha0)]
    nlinarith
  have hcostlog :
      improvedCrootCost A₁ U (1 / 16) beta *
          Real.log (11 / (10 * alpha)) ≤ 2 ^ 131 * L ^ 6 := by
    calc
      improvedCrootCost A₁ U (1 / 16) beta *
          Real.log (11 / (10 * alpha)) ≤
          (2 ^ 100 * L ^ 4) * (2 ^ 31 * L ^ 2) := by gcongr
      _ = 2 ^ 131 * L ^ 6 := by norm_num; ring
  have hent := reflectedStableEntropy_cast_le A₁ U
    halpha0 halpha1 hA₁ hU (epsilon := (1 / 16 : ℝ)) (beta := beta)
  have hlog4 : Real.log 4 ≤ 4 := Real.log_le_self (by norm_num)
  have hL6 : 1 ≤ L ^ 6 := one_le_pow₀ hL1
  simpa only [alpha] using (hent.trans (by
    calc
      8 * (improvedCrootCost A₁ U (1 / 16) beta *
          Real.log (11 / (10 * alpha)) + Real.log 4) + 2 ≤
          8 * (2 ^ 131 * L ^ 6 + 4) + 2 := by gcongr
      _ ≤ 2 ^ 140 * L ^ 6 := by
        norm_num at hL6 ⊢
        linarith))

/-- At the fixed error `1/16`, the auxiliary local-spectrum accuracy is at
most an absolute constant times the reciprocal density. -/
lemma rankFreeAuxiliaryAccuracy_fixed_le {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    (CyclicImprovedLocalDensityIteration.rankFreeAuxiliaryAccuracy
        (1 / 16) beta : ℝ) ≤ 2 ^ 15 * beta⁻¹ := by
  let x : ℝ := ((1 / 16 : ℝ) * beta)⁻¹
  have hx0 : 0 ≤ x := (inv_pos.mpr (mul_pos (by norm_num) hbeta0)).le
  have hceil : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hinv1 : 1 ≤ beta⁻¹ := (one_le_inv₀ hbeta0).2 hbeta1
  have hx : x = 16 * beta⁻¹ := by
    dsimp only [x]
    field_simp
  unfold CyclicImprovedLocalDensityIteration.rankFreeAuxiliaryAccuracy
  push_cast
  calc
    512 * ((⌈x⌉₊ : ℝ) + 1) ≤ 512 * (x + 2) := by
      nlinarith [hceil]
    _ = 512 * (16 * beta⁻¹ + 2) := by rw [hx]
    _ ≤ 512 * (18 * beta⁻¹) := by
      gcongr
      nlinarith
    _ ≤ 2 ^ 15 * beta⁻¹ := by
      have hinv0 : 0 ≤ beta⁻¹ := (inv_pos.mpr hbeta0).le
      norm_num
      nlinarith

/-- A uniform lower floor for the stable-carrier controller radius when its
entropy is bounded by the natural number `M`. -/
noncomputable def controlledStableRadiusFloor
    (B : CyclicBohr.Set N) (beta : ℝ) (M : ℕ) : ℝ :=
  min 1 B.radius * beta /
    (2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 * (2 : ℝ) ^ M)

lemma controlledStableRadiusFloor_pos
    (B : CyclicBohr.Set N) {beta : ℝ} (M : ℕ)
    (hBradius : 0 < B.radius) (hBrank : 0 < B.rank)
    (hbeta : 0 < beta) :
    0 < controlledStableRadiusFloor B beta M := by
  unfold controlledStableRadiusFloor
  have hmin : 0 < min 1 B.radius := lt_min zero_lt_one hBradius
  have hden : 0 <
      (2 ^ 40 : ℝ) * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 * (2 : ℝ) ^ M := by
    have hM : (0 : ℝ) < M + 1 := by positivity
    have hr : (0 : ℝ) < B.rank := by exact_mod_cast hBrank
    positivity
  exact div_pos (mul_pos hmin hbeta) hden

lemma controlledStableRadiusFloor_mono_beta
    (B : CyclicBohr.Set N) (M : ℕ) {beta gamma : ℝ}
    (hBrank : 0 < B.rank) (hbetaGamma : beta ≤ gamma) :
    controlledStableRadiusFloor B beta M ≤
      controlledStableRadiusFloor B gamma M := by
  unfold controlledStableRadiusFloor
  have hr : (0 : ℝ) < B.rank := by exact_mod_cast hBrank
  have hden : 0 <
      (2 ^ 40 : ℝ) * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 * (2 : ℝ) ^ M := by
    positivity
  apply (div_le_div_iff_of_pos_right hden).2
  exact mul_le_mul_of_nonneg_left hbetaGamma
    (le_min zero_le_one B.radius_nonneg)

lemma controlledStableRadiusFloor_le_radius
    (B : CyclicBohr.Set N) (M : ℕ) {beta : ℝ}
    (hBrank : 0 < B.rank) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) :
    controlledStableRadiusFloor B beta M ≤ B.radius := by
  have hr1 : (1 : ℝ) ≤ B.rank := by exact_mod_cast hBrank
  have hM1 : (1 : ℝ) ≤ M + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
  have hrSq : (1 : ℝ) ≤ (B.rank : ℝ) ^ 2 := by nlinarith
  have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ M := one_le_pow₀ (by norm_num)
  have hden1 : (1 : ℝ) ≤
      2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 * (2 : ℝ) ^ M := by
    calc
      (1 : ℝ) ≤ 2 ^ 40 := by norm_num
      _ ≤ 2 ^ 40 * (M + 1 : ℝ) := by
        exact le_mul_of_one_le_right (by positivity) hM1
      _ ≤ 2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 := by
        exact le_mul_of_one_le_right (by positivity) hrSq
      _ ≤ 2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 * (2 : ℝ) ^ M := by
        exact le_mul_of_one_le_right (by positivity) hpow1
  have hmin0 : 0 ≤ min 1 B.radius := le_min zero_le_one B.radius_nonneg
  unfold controlledStableRadiusFloor
  calc
    min 1 B.radius * beta /
          (2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 * (2 : ℝ) ^ M) ≤
        min 1 B.radius * beta := div_le_self (mul_nonneg hmin0 hbeta0) hden1
    _ ≤ min 1 B.radius := by nlinarith [mul_nonneg hmin0 (sub_nonneg.mpr hbeta1)]
    _ ≤ B.radius := min_le_right _ _

lemma controlledStableRadiusFloor_le_controller
    (B : CyclicBohr.Set N) (entropy M : ℕ) {beta : ℝ}
    (hBradius : 0 < B.radius) (hBrank : 0 < B.rank)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hentropy : 0 < entropy) (hentropyM : entropy ≤ M) :
    controlledStableRadiusFloor B beta M ≤
      min B.radius
        (CyclicLocalChangSanders.stableCarrierControllerRadius
          B entropy
          (CyclicImprovedLocalDensityIteration.rankFreeAuxiliaryAccuracy
            (1 / 16) beta)
          ((400 * ((2 ^ entropy : ℕ) : ℝ) * (B.rank : ℝ))⁻¹)
          (CyclicImprovedLocalDensityIteration.rankFreeExtractedRadius
            (1 / 16) beta entropy)) := by
  let ell := CyclicImprovedLocalDensityIteration.rankFreeAuxiliaryAccuracy
    (1 / 16) beta
  let delta : ℝ :=
    (400 * ((2 ^ entropy : ℕ) : ℝ) * (B.rank : ℝ))⁻¹
  let sigma := CyclicImprovedLocalDensityIteration.rankFreeExtractedRadius
    (1 / 16) beta entropy
  let den : ℝ :=
    2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 * (2 : ℝ) ^ M
  let smallDen : ℝ :=
    400 * (ell : ℝ) * (B.rank : ℝ) * (entropy : ℝ) *
      (400 * (2 : ℝ) ^ entropy * (B.rank : ℝ))
  have he0 : (0 : ℝ) < entropy := by exact_mod_cast hentropy
  have hr0 : (0 : ℝ) < B.rank := by exact_mod_cast hBrank
  have hpow : (2 : ℝ) ^ entropy ≤ (2 : ℝ) ^ M :=
    pow_le_pow_right₀ (by norm_num) hentropyM
  have hMcast : (entropy : ℝ) ≤ (M : ℝ) + 1 := by
    exact_mod_cast (hentropyM.trans (Nat.le_succ M))
  have hell0 : (0 : ℝ) < ell := by
    dsimp only [ell]
    exact_mod_cast
      CyclicImprovedLocalDensityIteration.rankFreeAuxiliaryAccuracy_pos
        (1 / 16) beta
  have hellBound : (ell : ℝ) ≤ 2 ^ 15 * beta⁻¹ := by
    dsimp only [ell]
    exact rankFreeAuxiliaryAccuracy_fixed_le hbeta0 hbeta1
  have hbetaEll : beta * (ell : ℝ) ≤ 2 ^ 15 := by
    calc
      beta * (ell : ℝ) ≤ beta * (2 ^ 15 * beta⁻¹) := by gcongr
      _ = 2 ^ 15 := by field_simp
  have hden0 : 0 < den := by dsimp only [den]; positivity
  have hdenOne : 1 ≤ den := by
    dsimp only [den]
    have hr1 : (1 : ℝ) ≤ B.rank := by exact_mod_cast hBrank
    have hpowr : 1 ≤ (B.rank : ℝ) ^ 2 := one_le_pow₀ hr1
    have hpowM : 1 ≤ (2 : ℝ) ^ M := one_le_pow₀ (by norm_num)
    have hfac : 1 ≤ (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 * (2 : ℝ) ^ M := by
      have hM1 : (1 : ℝ) ≤ M + 1 := by
        have hMnonneg : (0 : ℝ) ≤ M := by positivity
        linarith
      exact one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hM1 hpowr) hpowM
    calc
      (1 : ℝ) ≤ 2 ^ 40 := by norm_num
      _ ≤ 2 ^ 40 *
          ((M + 1 : ℝ) * (B.rank : ℝ) ^ 2 * (2 : ℝ) ^ M) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hfac
            (show (0 : ℝ) ≤ 2 ^ 40 by positivity))
      _ = 2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 *
          (2 : ℝ) ^ M := by ring
  have hfloorB : controlledStableRadiusFloor B beta M ≤ B.radius := by
    unfold controlledStableRadiusFloor
    have hfrac : beta /
        (2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 * (2 : ℝ) ^ M) ≤ 1 := by
      rw [div_le_one hden0]
      exact hbeta1.trans hdenOne
    rw [show min 1 B.radius * beta /
        (2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 * (2 : ℝ) ^ M) =
          min 1 B.radius *
            (beta / (2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 *
              (2 : ℝ) ^ M)) by ring]
    exact (mul_le_mul_of_nonneg_left hfrac (by positivity)).trans
      (by simpa only [mul_one] using (min_le_right 1 B.radius))
  have hfloorSigma : controlledStableRadiusFloor B beta M ≤ sigma := by
    have hdenSigma : (8192 : ℝ) * entropy ≤ den := by
      calc
        (8192 : ℝ) * entropy ≤ 8192 * (M + 1 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hMcast (by norm_num)
        _ ≤ 2 ^ 40 * (M + 1 : ℝ) := by gcongr <;> norm_num
        _ ≤ den := by
          dsimp only [den]
          have hr1 : (1 : ℝ) ≤ B.rank := by exact_mod_cast hBrank
          have hr2 : (1 : ℝ) ≤ (B.rank : ℝ) ^ 2 := one_le_pow₀ hr1
          have hpowM : 1 ≤ (2 : ℝ) ^ M := one_le_pow₀ (by norm_num)
          have hfac : 1 ≤ (B.rank : ℝ) ^ 2 * (2 : ℝ) ^ M :=
            one_le_mul_of_one_le_of_one_le hr2 hpowM
          calc
            2 ^ 40 * (M + 1 : ℝ) =
                2 ^ 40 * (M + 1 : ℝ) * 1 := by ring
            _ ≤ 2 ^ 40 * (M + 1 : ℝ) *
                ((B.rank : ℝ) ^ 2 * (2 : ℝ) ^ M) := by gcongr
            _ = 2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 *
                (2 : ℝ) ^ M := by ring
    have hdiv : beta / den ≤ beta / ((8192 : ℝ) * entropy) :=
      div_le_div_of_nonneg_left hbeta0.le (mul_pos (by norm_num) he0)
        hdenSigma
    unfold controlledStableRadiusFloor
    dsimp only [den] at hdiv
    dsimp only [sigma,
      CyclicImprovedLocalDensityIteration.rankFreeExtractedRadius]
    have hmin1 : min 1 B.radius ≤ 1 := min_le_left _ _
    have hmin0 : 0 ≤ min 1 B.radius := by positivity
    calc
      min 1 B.radius * beta /
          (2 ^ 40 * (↑M + 1) * ↑B.rank ^ 2 * 2 ^ M) =
          min 1 B.radius *
            (beta / (2 ^ 40 * (↑M + 1) * ↑B.rank ^ 2 * 2 ^ M)) := by ring
      _ ≤ 1 * (beta / (2 ^ 40 * (↑M + 1) * ↑B.rank ^ 2 * 2 ^ M)) := by
        gcongr
      _ ≤ beta / (8192 * entropy) := by simpa using hdiv
      _ = 1 / 16 * beta / (512 * entropy) := by ring
  have hsmall0 : 0 < smallDen := by dsimp only [smallDen]; positivity
  have hbetaSmallDen : beta * smallDen ≤ den := by
    have hP0 : 0 ≤ (M + 1 : ℝ) * (2 : ℝ) ^ M * (B.rank : ℝ) ^ 2 := by
      positivity
    calc
      beta * smallDen =
          160000 * (entropy : ℝ) * (2 : ℝ) ^ entropy *
            (B.rank : ℝ) ^ 2 * (beta * (ell : ℝ)) := by
        dsimp only [smallDen]
        ring
      _ ≤ 160000 * (M + 1 : ℝ) * (2 : ℝ) ^ M *
            (B.rank : ℝ) ^ 2 * (2 ^ 15 : ℝ) := by
        gcongr
      _ = (160000 * 2 ^ 15 : ℝ) *
          ((M + 1 : ℝ) * (2 : ℝ) ^ M * (B.rank : ℝ) ^ 2) := by ring
      _ ≤ (2 ^ 40 : ℝ) *
          ((M + 1 : ℝ) * (2 : ℝ) ^ M * (B.rank : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) hP0
      _ = den := by dsimp only [den]; ring
  have hratio : beta / den ≤ 1 / smallDen := by
    rw [div_le_div_iff₀ hden0 hsmall0]
    simpa only [one_mul] using hbetaSmallDen
  have hfloorSecond : controlledStableRadiusFloor B beta M ≤
      (400 * (ell : ℝ) * (B.rank : ℝ))⁻¹ *
        ((delta / (entropy : ℝ)) * B.radius) := by
    have hminRadius : min 1 B.radius ≤ B.radius := min_le_right _ _
    have hratio0 : 0 ≤ 1 / smallDen := by positivity
    have hleft : controlledStableRadiusFloor B beta M ≤
        B.radius * (1 / smallDen) := by
      unfold controlledStableRadiusFloor
      rw [show min 1 B.radius * beta / den =
        min 1 B.radius * (beta / den) by ring]
      exact mul_le_mul hminRadius hratio (by positivity) (by positivity)
    calc
      controlledStableRadiusFloor B beta M ≤
          B.radius * (1 / smallDen) := hleft
      _ = (400 * (ell : ℝ) * (B.rank : ℝ))⁻¹ *
          ((delta / (entropy : ℝ)) * B.radius) := by
        dsimp only [smallDen, delta]
        push_cast
        field_simp
  unfold CyclicLocalChangSanders.stableCarrierControllerRadius
  exact le_min hfloorB (le_min hfloorSigma hfloorSecond)

/-! ## Polynomial radius floor from the sharp controller -/

/-- The sharp controller removes the exponential factor `2^M` from the
radius recurrence. -/
noncomputable def controlledSharpRadiusFloor
    (B : CyclicBohr.Set N) (beta : ℝ) (M : ℕ) : ℝ :=
  min 1 B.radius * beta /
    (2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2)

lemma controlledSharpRadiusFloor_pos
    (B : CyclicBohr.Set N) {beta : ℝ} (M : ℕ)
    (hBradius : 0 < B.radius) (hBrank : 0 < B.rank)
    (hbeta : 0 < beta) :
    0 < controlledSharpRadiusFloor B beta M := by
  unfold controlledSharpRadiusFloor
  have hmin : 0 < min 1 B.radius := lt_min zero_lt_one hBradius
  have hden : 0 <
      (2 ^ 40 : ℝ) * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 := by
    have hr : (0 : ℝ) < B.rank := by exact_mod_cast hBrank
    positivity
  exact div_pos (mul_pos hmin hbeta) hden

lemma controlledSharpRadiusFloor_mono_beta
    (B : CyclicBohr.Set N) (M : ℕ) {beta gamma : ℝ}
    (hBrank : 0 < B.rank) (hbetaGamma : beta ≤ gamma) :
    controlledSharpRadiusFloor B beta M ≤
      controlledSharpRadiusFloor B gamma M := by
  unfold controlledSharpRadiusFloor
  have hr : (0 : ℝ) < B.rank := by exact_mod_cast hBrank
  have hden : 0 <
      (2 ^ 40 : ℝ) * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 := by
    positivity
  apply (div_le_div_iff_of_pos_right hden).2
  exact mul_le_mul_of_nonneg_left hbetaGamma
    (le_min zero_le_one B.radius_nonneg)

lemma controlledSharpRadiusFloor_le_radius
    (B : CyclicBohr.Set N) (M : ℕ) {beta : ℝ}
    (hBrank : 0 < B.rank) (hbeta0 : 0 ≤ beta) (hbeta1 : beta ≤ 1) :
    controlledSharpRadiusFloor B beta M ≤ B.radius := by
  have hr1 : (1 : ℝ) ≤ B.rank := by exact_mod_cast hBrank
  have hM1 : (1 : ℝ) ≤ M + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
  have hrSq : (1 : ℝ) ≤ (B.rank : ℝ) ^ 2 := one_le_pow₀ hr1
  have hden1 : (1 : ℝ) ≤
      2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 := by
    calc
      (1 : ℝ) ≤ 2 ^ 40 := by norm_num
      _ ≤ 2 ^ 40 * (M + 1 : ℝ) := by
        exact le_mul_of_one_le_right (by positivity) hM1
      _ ≤ 2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 := by
        exact le_mul_of_one_le_right (by positivity) hrSq
  have hmin0 : 0 ≤ min 1 B.radius := le_min zero_le_one B.radius_nonneg
  unfold controlledSharpRadiusFloor
  calc
    min 1 B.radius * beta /
          (2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2) ≤
        min 1 B.radius * beta :=
      div_le_self (mul_nonneg hmin0 hbeta0) hden1
    _ ≤ min 1 B.radius := by
      nlinarith [mul_nonneg hmin0 (sub_nonneg.mpr hbeta1)]
    _ ≤ B.radius := min_le_right _ _

lemma controlledSharpRadiusFloor_le_controller
    (B : CyclicBohr.Set N) (entropy M : ℕ) {beta : ℝ}
    (hBradius : 0 < B.radius) (hBrank : 0 < B.rank)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hentropy : 0 < entropy) (hentropyM : entropy ≤ M) :
    controlledSharpRadiusFloor B beta M ≤
      min B.radius
        (CyclicSharpLocalChangSanders.sharpControllerRadius
          B (entropy - 1)
          (CyclicImprovedLocalDensityIteration.rankFreeAuxiliaryAccuracy
            (1 / 16) beta)
          (CyclicImprovedLocalDensityIteration.rankFreeExtractedRadius
            (1 / 16) beta entropy)) := by
  let ell := CyclicImprovedLocalDensityIteration.rankFreeAuxiliaryAccuracy
    (1 / 16) beta
  let sigma := CyclicImprovedLocalDensityIteration.rankFreeExtractedRadius
    (1 / 16) beta entropy
  let den : ℝ :=
    2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2
  let smallDen : ℝ :=
    320000 * (ell : ℝ) * (entropy : ℝ) * (B.rank : ℝ) ^ 2
  have he0 : (0 : ℝ) < entropy := by exact_mod_cast hentropy
  have hr0 : (0 : ℝ) < B.rank := by exact_mod_cast hBrank
  have hMcast : (entropy : ℝ) ≤ (M : ℝ) + 1 := by
    exact_mod_cast (hentropyM.trans (Nat.le_succ M))
  have hEntropySucc : entropy - 1 + 1 = entropy := by omega
  have hell0 : (0 : ℝ) < ell := by
    dsimp only [ell]
    exact_mod_cast
      CyclicImprovedLocalDensityIteration.rankFreeAuxiliaryAccuracy_pos
        (1 / 16) beta
  have hellBound : (ell : ℝ) ≤ 2 ^ 15 * beta⁻¹ := by
    dsimp only [ell]
    exact rankFreeAuxiliaryAccuracy_fixed_le hbeta0 hbeta1
  have hbetaEll : beta * (ell : ℝ) ≤ 2 ^ 15 := by
    calc
      beta * (ell : ℝ) ≤ beta * (2 ^ 15 * beta⁻¹) := by gcongr
      _ = 2 ^ 15 := by field_simp
  have hden0 : 0 < den := by dsimp only [den]; positivity
  have hdenOne : 1 ≤ den := by
    dsimp only [den]
    have hr1 : (1 : ℝ) ≤ B.rank := by exact_mod_cast hBrank
    have hrSq : 1 ≤ (B.rank : ℝ) ^ 2 := one_le_pow₀ hr1
    have hM1 : (1 : ℝ) ≤ M + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le M)
    have hfac : 1 ≤ (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le hM1 hrSq
    calc
      (1 : ℝ) ≤ 2 ^ 40 := by norm_num
      _ ≤ 2 ^ 40 * ((M + 1 : ℝ) * (B.rank : ℝ) ^ 2) := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hfac
            (show (0 : ℝ) ≤ 2 ^ 40 by positivity))
      _ = 2 ^ 40 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 := by ring
  have hfloorB : controlledSharpRadiusFloor B beta M ≤ B.radius := by
    exact controlledSharpRadiusFloor_le_radius B M hBrank hbeta0.le hbeta1
  have hfloorSigma : controlledSharpRadiusFloor B beta M ≤ sigma := by
    have hdenSigma : (8192 : ℝ) * entropy ≤ den := by
      calc
        (8192 : ℝ) * entropy ≤ 8192 * (M + 1 : ℝ) := by gcongr
        _ ≤ 2 ^ 40 * (M + 1 : ℝ) := by gcongr <;> norm_num
        _ ≤ den := by
          dsimp only [den]
          have hr1 : (1 : ℝ) ≤ B.rank := by exact_mod_cast hBrank
          have hrSq : (1 : ℝ) ≤ (B.rank : ℝ) ^ 2 := one_le_pow₀ hr1
          exact le_mul_of_one_le_right (by positivity) hrSq
    have hdiv : beta / den ≤ beta / ((8192 : ℝ) * entropy) :=
      div_le_div_of_nonneg_left hbeta0.le (mul_pos (by norm_num) he0)
        hdenSigma
    unfold controlledSharpRadiusFloor
    dsimp only [den] at hdiv
    dsimp only [sigma,
      CyclicImprovedLocalDensityIteration.rankFreeExtractedRadius]
    have hmin1 : min 1 B.radius ≤ 1 := min_le_left _ _
    calc
      min 1 B.radius * beta /
          (2 ^ 40 * (↑M + 1) * ↑B.rank ^ 2) =
          min 1 B.radius *
            (beta / (2 ^ 40 * (↑M + 1) * ↑B.rank ^ 2)) := by ring
      _ ≤ 1 * (beta / (2 ^ 40 * (↑M + 1) * ↑B.rank ^ 2)) := by
        gcongr
      _ ≤ beta / (8192 * entropy) := by simpa using hdiv
      _ = 1 / 16 * beta / (512 * entropy) := by ring
  have hsmall0 : 0 < smallDen := by dsimp only [smallDen]; positivity
  have hbetaSmallDen : beta * smallDen ≤ den := by
    have hP0 : 0 ≤ (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 := by positivity
    calc
      beta * smallDen =
          320000 * (entropy : ℝ) * (B.rank : ℝ) ^ 2 *
            (beta * (ell : ℝ)) := by
        dsimp only [smallDen]
        ring
      _ ≤ 320000 * (M + 1 : ℝ) * (B.rank : ℝ) ^ 2 *
            (2 ^ 15 : ℝ) := by
        gcongr
      _ = (320000 * 2 ^ 15 : ℝ) *
          ((M + 1 : ℝ) * (B.rank : ℝ) ^ 2) := by ring
      _ ≤ (2 ^ 40 : ℝ) *
          ((M + 1 : ℝ) * (B.rank : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) hP0
      _ = den := by dsimp only [den]; ring
  have hratio : beta / den ≤ 1 / smallDen := by
    rw [div_le_div_iff₀ hden0 hsmall0]
    simpa only [one_mul] using hbetaSmallDen
  have hfloorSecond : controlledSharpRadiusFloor B beta M ≤
      (400 * (ell : ℝ) * (B.rank : ℝ))⁻¹ *
        (((2 /
          (CyclicSharpLocalChangSanders.sharpSmoothingLength
            (entropy - 1) : ℝ)) *
          (400 * (B.rank : ℝ))⁻¹) * B.radius) := by
    have hminRadius : min 1 B.radius ≤ B.radius := min_le_right _ _
    have hleft : controlledSharpRadiusFloor B beta M ≤
        B.radius * (1 / smallDen) := by
      unfold controlledSharpRadiusFloor
      rw [show min 1 B.radius * beta / den =
        min 1 B.radius * (beta / den) by ring]
      exact mul_le_mul hminRadius hratio (by positivity) (by positivity)
    calc
      controlledSharpRadiusFloor B beta M ≤
          B.radius * (1 / smallDen) := hleft
      _ = (400 * (ell : ℝ) * (B.rank : ℝ))⁻¹ *
          (((2 /
            (CyclicSharpLocalChangSanders.sharpSmoothingLength
              (entropy - 1) : ℝ)) *
            (400 * (B.rank : ℝ))⁻¹) * B.radius) := by
        rw [show CyclicSharpLocalChangSanders.sharpSmoothingLength
            (entropy - 1) = 4 * entropy by
          simp only [CyclicSharpLocalChangSanders.sharpSmoothingLength,
            hEntropySucc]]
        dsimp only [smallDen]
        push_cast
        field_simp
        <;> ring
  unfold CyclicSharpLocalChangSanders.sharpControllerRadius
  exact le_min hfloorB (le_min hfloorSigma hfloorSecond)

/-- Concise local density step with a supplied common logarithmic budget.
The two callback hypotheses isolate the only facts contributed by the nested
geometry: a bound for the sifting exponent and the support-cardinality
estimate.  All large Croot--Sisask witnesses are discharged here, keeping the
nested consumer below the default elaboration budget. -/
theorem exists_positive_density_increment_slice_with_controlled_rank
    (B R : CyclicBohr.Set N) (A S T : Finset (ZMod N))
    (m p mNext : ℕ) (L : ℝ)
    {t delta vr eta beta : ℝ}
    (hm : 0 < m) (hp : p ≠ 0)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1)
    (hRradius : 0 < R.radius) (hRrank : 0 < R.rank)
    (hmNext : 0 < mNext)
    (hdelta : 0 ≤ delta) (hinner : 0 ≤ t - delta)
    (heta : 0 < eta) (hetavr : eta ≤ vr)
    (hregular :
      (10 * m) * (B.dilate (t + delta)).carrier.card ≤
        (10 * m + 1) * (B.dilate (t - delta)).carrier.card)
    (hRregular :
      10 * (R.dilate (vr + eta)).carrier.card ≤
        11 * (R.dilate (vr - eta)).carrier.card)
    (hA : A.Nonempty)
    (hAB : A ⊆ (B.dilate t).carrier)
    (hdensity : beta * (B.dilate t).carrier.card = A.card)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hTinner : T = (R.dilate (vr - eta)).carrier)
    (hSsub : S ⊆ (B.dilate (delta / 4)).carrier)
    (hTsub : T ⊆ (B.dilate (delta / 4)).carrier)
    (hRsmall : (R.dilate eta).carrier ⊆
      (B.dilate (delta / 4)).carrier)
    (herror : 3 * (1 / ((5 * m : ℕ) * beta)) ≤ (1 / 16 : ℝ) / 4)
    (hlarge : (1 / 16 : ℝ) ≤
      ‖(B.dilate t).carrier.card •
        (CyclicRelativeLifting.relativeBalance A (B.dilate t).carrier ○ᵈ
          CyclicRelativeLifting.relativeBalance A
            (B.dilate t).carrier)‖_[p,
              CyclicPositiveDefiniteLifting.positiveDefiniteWeight S T])
    (hAfree : ThreeAPFree (A : Set (ZMod N)))
    (hL1 : 1 ≤ L) (hlogbeta : curLog beta ≤ 4 * L)
    (hqControl : ∀ p' q : ℕ,
      (p' : ℝ) ≤ 2 ^ 10 * (1 / 16 : ℝ)⁻¹ ^ 2 * p →
      q = max (2 * p')
        (2 ^ 4 * ⌈(1 / 16 : ℝ)⁻¹ *
          Real.log (256 / (1 / 16 : ℝ))⌉₊) →
      (q : ℝ) ≤ 2 ^ 26 * L)
    (hSupport : ∀ (x : ZMod N) (A₁ A₂ U : Finset (ZMod N)),
      A₁ ⊆ S →
      A₂ ⊆ CyclicLocalSifting.reflectedTranslate T x →
      U ⊆ A₁ - A₂ →
      (U.card : ℝ) ≤ 9 * S.card) :
    ∃ (C : CyclicBohr.Set N) (v xi : ℝ) (y : ZMod N),
      0 < C.radius ∧ R.rank ≤ C.rank ∧
      (C.rank : ℝ) ≤ (R.rank : ℝ) + 2 ^ 140 * L ^ 6 ∧
      controlledSharpRadiusFloor (R.dilate eta) beta
          ⌈2 ^ 140 * L ^ 6⌉₊ ≤ C.radius ∧
      1 / 2 ≤ v ∧ v ≤ 1 ∧
      xi = (400 * (mNext : ℝ) * (C.rank : ℝ))⁻¹ ∧
      0 < xi ∧ xi < v ∧
      (10 * mNext) * (C.dilate (v + xi)).carrier.card ≤
        (10 * mNext + 1) * (C.dilate (v - xi)).carrier.card ∧
      (C.dilate v).carrier ⊆ (B.dilate (delta / 4)).carrier ∧
      CyclicDensityIncrement.normalizedSlice A (C.dilate v).carrier y ⊆
        (C.dilate v).carrier ∧
      ThreeAPFree
        (CyclicDensityIncrement.normalizedSlice A (C.dilate v).carrier y :
          Set (ZMod N)) ∧
      (1 + (1 / 16 : ℝ) / 64) * beta ≤
        (CyclicDensityIncrement.normalizedSlice A
          (C.dilate v).carrier y).card /
          ((C.dilate v).carrier.card : ℝ) := by
  obtain ⟨p', q, x, A₁, A₂, U, C, v, xi, y, hp', hq,
      hA₁, hU, hA₁S, hA₂T, hUsub, hA₁dense, hCradius,
      hCpos, hRrankC, hCrank, hvlow, hvhigh, hxiFormula, hxi, hxiv,
      hCregular, hCsmall, hslice, hfree, hdense⟩ :=
    CyclicImprovedLocalDensityStep.exists_positive_density_increment_slice_of_large_norm_sharp_reflected_quantitative
      B R A S T m p mNext (t := t) (delta := delta) (vr := vr)
      (eta := eta) (beta := beta) (epsilon := (1 / 16 : ℝ))
      hm hp hbeta0 hbeta1 (by norm_num) (by norm_num) hRradius hRrank
      hmNext hdelta hinner heta hetavr hregular hRregular hA hAB hdensity
      hS hT hTinner hSsub hTsub hRsmall herror hlarge hAfree
  have hqL : (q : ℝ) ≤ 2 ^ 26 * L := hqControl p' q hp' hq
  have hA₁denseMul :
      (4 : ℝ)⁻¹ * beta ^ (2 * q) * (S.card : ℝ) ≤ A₁.card := by
    rw [le_div_iff₀ (by exact_mod_cast hS.card_pos)] at hA₁dense
    simpa only [mul_comm] using hA₁dense
  have hUcard : (U.card : ℝ) ≤ 9 * S.card :=
    hSupport x A₁ A₂ U hA₁S hA₂T hUsub
  have hentropy :
      (CyclicImprovedLocalDensityIteration.reflectedStableEntropy
        A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) (1 / 16) beta : ℝ) ≤
        2 ^ 140 * L ^ 6 :=
    reflectedStableEntropy_common_le S A₁ U q hbeta0 hbeta1 hL1
      hlogbeta hS hA₁ hU hqL hA₁denseMul hUcard
  have hCrankReal : (C.rank : ℝ) ≤ (R.rank : ℝ) +
      (CyclicImprovedLocalDensityIteration.reflectedStableEntropy
        A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) (1 / 16) beta : ℝ) := by
    exact_mod_cast hCrank
  have hcontrolled : (C.rank : ℝ) ≤
      (R.rank : ℝ) + 2 ^ 140 * L ^ 6 :=
    hCrankReal.trans (add_le_add le_rfl hentropy)
  let E := CyclicImprovedLocalDensityIteration.reflectedStableEntropy
    A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) (1 / 16) beta
  let M := ⌈2 ^ 140 * L ^ 6⌉₊
  have hEpos : 0 < E := by
    dsimp only [E]
    exact CyclicImprovedLocalDensityIteration.reflectedStableEntropy_pos
      (N := N) A₁ U ((4 : ℝ)⁻¹ * beta ^ (2 * q)) (1 / 16) beta
  have hEM : E ≤ M := by
    have hcast : (E : ℝ) ≤ (M : ℝ) := by
      calc
        (E : ℝ) ≤ 2 ^ 140 * L ^ 6 := by simpa only [E] using hentropy
        _ ≤ (M : ℝ) := by
          dsimp only [M]
          exact Nat.le_ceil _
    exact_mod_cast hcast
  have hradiusFloor : controlledSharpRadiusFloor (R.dilate eta) beta M ≤
      C.radius := by
    rw [hCradius]
    have hfloor := controlledSharpRadiusFloor_le_controller
      (R.dilate eta) E M
      (by simp only [CyclicBohr.Set.radius_dilate, abs_of_pos heta]; positivity)
      (by simpa only [CyclicBohr.Set.rank_dilate] using hRrank)
      hbeta0 hbeta1 hEpos hEM
    simpa only [E, CyclicBohr.Set.rank_dilate] using hfloor
  exact ⟨C, v, xi, y, hCpos, hRrankC, hcontrolled,
    by simpa only [M] using hradiusFloor, hvlow, hvhigh,
    hxiFormula, hxi, hxiv, hCregular, hCsmall, hslice, hfree, hdense⟩

end CyclicQuantitativeBounds

end Erdos721
