/- leanprover/lean4:v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

https://www.apache.org/licenses/LICENSE-2.0
-/

import ErdosProblems.Erdos721.NestedIteration
import ErdosProblems.Erdos721.Cardinality

/-!
# The quantitative cyclic Roth endpoint

This file starts the checked nested density iteration on the rank-one trivial
Bohr set and converts its terminal rank and radius certificates into a bound
for a three-progression-free subset of an odd cyclic group.
-/

namespace Erdos721

open Filter Finset Fintype Function MeasureTheory RCLike Real
open scoped BigOperators ENNReal Indicator mu NNReal Pointwise

namespace CyclicRothEndpoint

variable {N : ℕ} [NeZero N]

noncomputable def baseBohr : CyclicBohr.Set N :=
  CyclicBohr.Set.ofFrequencies {0} 1 (by norm_num)

@[simp] lemma baseBohr_rank : (baseBohr : CyclicBohr.Set N).rank = 1 := by
  simp [baseBohr]

@[simp] lemma baseBohr_radius : (baseBohr : CyclicBohr.Set N).radius = 1 := rfl

lemma baseBohr_dilate_carrier (t : ℝ) :
    ((baseBohr : CyclicBohr.Set N).dilate t).carrier = Finset.univ := by
  ext x
  simp [CyclicBohr.Set.carrier, baseBohr]

/-- Fine regularity parameter chosen from the initial density. -/
noncomputable def regularityParameter (beta : ℝ) : ℕ :=
  ⌈2 ^ 20 * beta⁻¹⌉₊

lemma regularityParameter_cast_lower {beta : ℝ} (hbeta : 0 < beta) :
    2 ^ 20 * beta⁻¹ ≤ (regularityParameter beta : ℝ) := by
  unfold regularityParameter
  exact Nat.le_ceil _

lemma regularityParameter_cast_lt {beta : ℝ} (hbeta : 0 < beta) :
    (regularityParameter beta : ℝ) < 2 ^ 20 * beta⁻¹ + 1 := by
  unfold regularityParameter
  exact Nat.ceil_lt_add_one (mul_nonneg (by positivity) (inv_pos.mpr hbeta).le)

lemma regularityParameter_large {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    8192 ≤ regularityParameter beta := by
  have hinv : (1 : ℝ) ≤ beta⁻¹ := (one_le_inv₀ hbeta0).2 hbeta1
  have hlower := regularityParameter_cast_lower hbeta0
  have hcast : (8192 : ℝ) ≤ (regularityParameter beta : ℝ) := by
    calc
      (8192 : ℝ) ≤ 2 ^ 20 * 1 := by norm_num
      _ ≤ 2 ^ 20 * beta⁻¹ := by gcongr
      _ ≤ regularityParameter beta := hlower
  exact_mod_cast hcast

lemma regularityParameter_error {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    3 * (1 / ((5 * regularityParameter beta : ℕ) *
        ((1 - 1 / 8192 : ℝ) * beta))) ≤ (1 / 16 : ℝ) / 4 := by
  have hm := regularityParameter_cast_lower hbeta0
  have hden : (192 : ℝ) ≤
      ((5 * regularityParameter beta : ℕ) : ℝ) *
        ((1 - 1 / 8192 : ℝ) * beta) := by
    push_cast
    have hmul := mul_le_mul_of_nonneg_right hm hbeta0.le
    have hbetaInv : beta⁻¹ * beta = 1 := inv_mul_cancel₀ hbeta0.ne'
    calc
      (192 : ℝ) ≤ 5 * (2 ^ 20 * beta⁻¹) *
          ((1 - 1 / 8192) * beta) := by
        rw [show 5 * (2 ^ 20 * beta⁻¹) *
          ((1 - 1 / 8192) * beta) =
            5 * 2 ^ 20 * (1 - 1 / 8192) * (beta⁻¹ * beta) by ring,
          hbetaInv]
        norm_num
      _ ≤ 5 * (regularityParameter beta : ℝ) *
          ((1 - 1 / 8192) * beta) := by
        have hfixed : 0 ≤ (1 - 1 / 8192 : ℝ) := by norm_num
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hm (by norm_num))
          (mul_nonneg hfixed hbeta0.le)
  have hden0 : 0 <
      ((5 * regularityParameter beta : ℕ) : ℝ) *
        ((1 - 1 / 8192 : ℝ) * beta) := lt_of_lt_of_le (by norm_num) hden
  rw [show (1 / 16 : ℝ) / 4 = 3 * (1 / 192) by norm_num]
  exact mul_le_mul_of_nonneg_left
    (one_div_le_one_div_of_le (by norm_num) hden) (by norm_num)

/-- The rank-one initial state on the whole cyclic group. -/
noncomputable def initialState (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set (ZMod N))) :
    CyclicNestedDensityStep.State N
      (regularityParameter ((A.card : ℝ) / N)) := by
  let beta : ℝ := (A.card : ℝ) / N
  let m := regularityParameter beta
  let delta : ℝ := (400 * (m : ℝ))⁻¹
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    exact div_pos (by exact_mod_cast hA.card_pos) hN0
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    rw [div_le_one hN0]
    exact_mod_cast (by simpa [ZMod.card] using A.card_le_univ)
  have hmNat : 0 < m := (regularityParameter_large hbeta0 hbeta1).trans_lt' (by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmNat
  have hdelta0 : 0 < delta := by dsimp only [delta]; positivity
  have hdelta1 : delta < 1 := by
    dsimp only [delta]
    apply inv_lt_one_of_one_lt₀
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmNat
    nlinarith
  refine {
    B := baseBohr
    t := 1
    delta := delta
    beta := beta
    A := A
    radius_pos := by simp
    rank_pos := by simp
    t_lower := by norm_num
    t_upper := le_rfl
    delta_pos := hdelta0
    delta_lt := hdelta1
    delta_formula := ?_
    regular := ?_
    A_nonempty := hA
    A_subset := ?_
    beta_pos := hbeta0
    beta_le_one := hbeta1
    density_eq := ?_
    threeAPFree := hfree }
  · dsimp only [delta]
    dsimp only [m, beta]
    simp
  · simp only [baseBohr_dilate_carrier, Finset.card_univ, ZMod.card]
    exact Nat.mul_le_mul_right N (Nat.le_succ _)
  · rw [baseBohr_dilate_carrier]
    exact Finset.subset_univ A
  · simp only [baseBohr_dilate_carrier, Finset.card_univ, ZMod.card]
    dsimp only [beta]
    field_simp

@[simp] lemma initialState_beta (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set (ZMod N))) :
    (initialState A hA hfree).beta = (A.card : ℝ) / N := rfl

@[simp] lemma initialState_bohr (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set (ZMod N))) :
    (initialState A hA hfree).B = baseBohr := rfl

/-- Quantitative terminal state obtained from a nonempty cyclic
three-progression-free set. -/
theorem exists_terminal_from_threeAPFree (hN : Odd N)
    (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set (ZMod N))) :
    ∃ st : CyclicNestedDensityStep.State N
        (regularityParameter ((A.card : ℝ) / N)),
      (1 - 1 / 8192 : ℝ) * ((A.card : ℝ) / N) ≤ st.beta ∧
      st.A.card ^ 2 < 2 * st.carrier.card ∧
      (st.B.rank : ℝ) ≤
        CyclicNestedIteration.rankCeiling (initialState A hA hfree) ∧
      CyclicNestedIteration.uniformRadiusFactor (initialState A hA hfree) ^
          CyclicNestedIteration.iterationBudget ((A.card : ℝ) / N) ≤
        min 1 st.B.radius := by
  let beta : ℝ := (A.card : ℝ) / N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    exact div_pos (by exact_mod_cast hA.card_pos) hN0
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    rw [div_le_one hN0]
    exact_mod_cast (by simpa [ZMod.card] using A.card_le_univ)
  have hm := regularityParameter_large hbeta0 hbeta1
  have herr := regularityParameter_error hbeta0 hbeta1
  obtain ⟨st, hdensity, hterminal, hrank, hradius⟩ :=
    CyclicNestedIteration.exists_quantitative_terminal_state hN
      (regularityParameter beta) hm (initialState A hA hfree) (by
        simpa only [initialState_beta, beta] using herr)
  refine ⟨st, ?_, hterminal, hrank, ?_⟩
  · simpa only [initialState, beta] using hdensity
  · simpa only [initialState, baseBohr_radius, min_self, mul_one, beta] using
      hradius

lemma terminal_carrier_upper
    {m : ℕ} (st : CyclicNestedDensityStep.State N m) {beta : ℝ}
    (hbeta : 0 < beta)
    (hdensity : (1 - 1 / 8192 : ℝ) * beta ≤ st.beta)
    (hterminal : st.A.card ^ 2 < 2 * st.carrier.card) :
    (st.carrier.card : ℝ) <
      2 / (((1 - 1 / 8192 : ℝ) * beta) ^ 2) := by
  let a : ℝ := (1 - 1 / 8192 : ℝ) * beta
  let C : ℝ := st.carrier.card
  have ha : 0 < a := by dsimp only [a]; positivity
  have hC : 0 < C := by
    dsimp only [C, CyclicNestedDensityStep.State.carrier]
    exact_mod_cast (st.B.dilate st.t).card_pos
  have hlow : a * C ≤ st.A.card := by
    calc
      a * C ≤ st.beta * C :=
        mul_le_mul_of_nonneg_right hdensity hC.le
      _ = st.A.card := by
        simpa only [a, C, CyclicNestedDensityStep.State.carrier] using
          st.density_eq
  have hsq : (a * C) ^ 2 ≤ (st.A.card : ℝ) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg ha.le hC.le) hlow 2
  have hterminalR : (st.A.card : ℝ) ^ 2 < 2 * C := by
    dsimp only [C]
    exact_mod_cast hterminal
  have hcancel : a ^ 2 * C < 2 := by
    apply lt_of_mul_lt_mul_right _ hC.le
    calc
      (a ^ 2 * C) * C = (a * C) ^ 2 := by ring
      _ ≤ (st.A.card : ℝ) ^ 2 := hsq
      _ < 2 * C := hterminalR
  dsimp only [a, C] at hcancel ⊢
  exact (lt_div_iff₀ (sq_pos_of_pos (mul_pos (by norm_num) hbeta))).2
    (by simpa [mul_comm] using hcancel)

noncomputable def radiusCode (r : ℝ) : ℕ := ⌈4 * Real.pi / r⌉₊

lemma radiusCode_pos {r : ℝ} (hr : 0 < r) : 0 < radiusCode r := by
  have hx : 0 < 4 * Real.pi / r := by positivity
  have hceil : (4 * Real.pi / r : ℝ) ≤ (radiusCode r : ℝ) := by
    exact Nat.le_ceil _
  have : (0 : ℝ) < radiusCode r := hx.trans_le hceil
  exact_mod_cast this

lemma radiusCode_cast_lt {r : ℝ} (hr : 0 < r) :
    (radiusCode r : ℝ) < 4 * Real.pi / r + 1 := by
  exact Nat.ceil_lt_add_one (by positivity)

lemma radiusCode_width {r : ℝ} (hr : 0 < r) :
    2 * Real.pi / radiusCode r ≤ r / 2 := by
  have hm := radiusCode_pos hr
  have hmR : (0 : ℝ) < radiusCode r := by exact_mod_cast hm
  have hceil : 4 * Real.pi / r ≤ (radiusCode r : ℝ) := Nat.le_ceil _
  rw [div_le_iff₀ hmR]
  have hrhalf : 0 ≤ r / 2 := div_nonneg hr.le (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hceil hrhalf
  calc
    2 * Real.pi = (r / 2) * (4 * Real.pi / r) := by
      field_simp [hr.ne']
      ring
    _ ≤ (r / 2) * (radiusCode r : ℝ) := hmul

lemma terminal_cardinality_lower
    {m : ℕ} (st : CyclicNestedDensityStep.State N m) {r : ℝ}
    (hr : 0 < r) (hradius : r ≤ min 1 st.B.radius) :
    N / (radiusCode r + 1) ^ st.B.rank ≤ st.carrier.card := by
  have hB : r ≤ st.B.radius := hradius.trans (min_le_right _ _)
  have ht0 : 0 < st.t := by linarith [st.t_lower]
  have hcarrierRadius : r / 2 ≤ (st.B.dilate st.t).radius := by
    simp only [CyclicBohr.Set.radius_dilate, abs_of_pos ht0]
    calc
      r / 2 = (1 / 2 : ℝ) * r := by ring
      _ ≤ st.t * st.B.radius :=
        mul_le_mul st.t_lower hB hr.le ht0.le
  apply CyclicBohr.natDiv_codeCard_le_card_carrier
    (st.B.dilate st.t) (radiusCode_pos hr)
  exact (radiusCode_width hr).trans hcarrierRadius

/-- Complete finite terminal package, before the logarithmic estimates are
simplified. -/
theorem exists_terminal_cardinality_package (hN : Odd N)
    (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set (ZMod N))) :
    ∃ st : CyclicNestedDensityStep.State N
        (regularityParameter ((A.card : ℝ) / N)),
      let s := initialState A hA hfree
      let q := CyclicNestedIteration.uniformRadiusFactor s
      let J := CyclicNestedIteration.iterationBudget ((A.card : ℝ) / N)
      let r := q ^ J
      (st.B.rank : ℝ) ≤ CyclicNestedIteration.rankCeiling s ∧
      (st.carrier.card : ℝ) <
        2 / (((1 - 1 / 8192 : ℝ) * ((A.card : ℝ) / N)) ^ 2) ∧
      r ≤ min 1 st.B.radius ∧
      N < (st.carrier.card + 1) * (radiusCode r + 1) ^ st.B.rank := by
  obtain ⟨st, hdensity, hterminal, hrank, hradius⟩ :=
    exists_terminal_from_threeAPFree hN A hA hfree
  let s := initialState A hA hfree
  let q := CyclicNestedIteration.uniformRadiusFactor s
  let J := CyclicNestedIteration.iterationBudget ((A.card : ℝ) / N)
  let r := q ^ J
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hbeta : 0 < (A.card : ℝ) / N :=
    div_pos (by exact_mod_cast hA.card_pos) hN0
  have hq : 0 < q := by
    dsimp only [q, s]
    exact CyclicNestedIteration.uniformRadiusFactor_pos _
  have hr : 0 < r := by dsimp only [r]; positivity
  have hcarrierUpper := terminal_carrier_upper st hbeta hdensity hterminal
  have hdiv := terminal_cardinality_lower st hr (by
    simpa only [r, q, J, s] using hradius)
  let D := (radiusCode r + 1) ^ st.B.rank
  have hD : 0 < D := by dsimp only [D]; positivity
  have hdivlt : N / D < st.carrier.card + 1 := by
    exact hdiv.trans_lt (Nat.lt_succ_self _)
  have hgroup : N < (st.carrier.card + 1) * D := by
    rw [Nat.div_lt_iff_lt_mul hD] at hdivlt
    simpa [Nat.mul_comm] using hdivlt
  refine ⟨st, ?_, hcarrierUpper, ?_, ?_⟩
  · simpa only [s] using hrank
  · simpa only [r, q, J, s] using hradius
  · simpa only [D] using hgroup

/-! ## Elementary exponential majorants -/

lemma two_pow_le_exp_nat_mul {k : ℕ} {L : ℝ} (hL : 1 ≤ L) :
    (2 : ℝ) ^ k ≤ Real.exp (k * L) := by
  calc
    (2 : ℝ) ^ k ≤ Real.exp 1 ^ k :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le k
    _ = Real.exp (k * 1) := by rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (k * L) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hL (by positivity)

lemma pow_le_exp_nat_mul {k : ℕ} {L : ℝ} (hL0 : 0 ≤ L) :
    L ^ k ≤ Real.exp (k * L) := by
  have hself : L ≤ Real.exp L := by
    linarith [Real.add_one_le_exp L]
  calc
    L ^ k ≤ Real.exp L ^ k := pow_le_pow_left₀ hL0 hself k
    _ = Real.exp (k * L) := by rw [← Real.exp_nat_mul]

lemma inv_eq_exp_curLog_sub_one {beta : ℝ} (hbeta : 0 < beta) :
    beta⁻¹ = Real.exp (CyclicQuantitativeBounds.curLog beta - 1) := by
  unfold CyclicQuantitativeBounds.curLog
  rw [add_sub_cancel_left, Real.exp_log (inv_pos.mpr hbeta)]

lemma regularityParameter_cast_upper {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    (regularityParameter beta : ℝ) ≤ 2 ^ 21 * beta⁻¹ := by
  have hinv : (1 : ℝ) ≤ beta⁻¹ := (one_le_inv₀ hbeta0).2 hbeta1
  have hlt := regularityParameter_cast_lt hbeta0
  calc
    (regularityParameter beta : ℝ) ≤ 2 ^ 20 * beta⁻¹ + 1 := hlt.le
    _ ≤ 2 ^ 20 * beta⁻¹ + beta⁻¹ := by gcongr
    _ ≤ 2 ^ 21 * beta⁻¹ := by nlinarith [inv_pos.mpr hbeta0]

lemma initial_entropy_cast_upper (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set (ZMod N))) :
    let beta : ℝ := (A.card : ℝ) / N
    let L := CyclicQuantitativeBounds.curLog beta
    ((initialState A hA hfree).entropyBudget : ℝ) ≤ 2 ^ 141 * L ^ 6 := by
  dsimp only
  let beta : ℝ := (A.card : ℝ) / N
  let L := CyclicQuantitativeBounds.curLog beta
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    exact div_pos (by exact_mod_cast hA.card_pos) hN0
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    rw [div_le_one hN0]
    exact_mod_cast (by simpa [ZMod.card] using A.card_le_univ)
  have hL1 : (1 : ℝ) ≤ L :=
    CyclicQuantitativeBounds.one_le_curLog hbeta0 hbeta1
  have hceil : ((initialState A hA hfree).entropyBudget : ℝ) <
      2 ^ 140 * L ^ 6 + 1 := by
    simp only [CyclicNestedDensityStep.State.entropyBudget, initialState_beta]
    exact Nat.ceil_lt_add_one (by positivity)
  calc
    ((initialState A hA hfree).entropyBudget : ℝ) ≤
        2 ^ 140 * L ^ 6 + 1 := hceil.le
    _ ≤ 2 ^ 140 * L ^ 6 + L ^ 6 := by
      have : (1 : ℝ) ≤ L ^ 6 := one_le_pow₀ hL1
      gcongr
    _ ≤ 2 ^ 141 * L ^ 6 := by
      have hL60 : 0 ≤ L ^ 6 := by positivity
      nlinarith

lemma iterationBudget_cast_upper {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    (CyclicNestedIteration.iterationBudget beta : ℝ) ≤
      2 ^ 18 * CyclicQuantitativeBounds.curLog beta := by
  have hL1 := CyclicQuantitativeBounds.one_le_curLog hbeta0 hbeta1
  have hlt := CyclicNestedIteration.iterationBudget_cast_lt hbeta0 hbeta1
  calc
    (CyclicNestedIteration.iterationBudget beta : ℝ) ≤
        2 ^ 17 * CyclicQuantitativeBounds.curLog beta + 1 := hlt.le
    _ ≤ 2 ^ 17 * CyclicQuantitativeBounds.curLog beta +
        CyclicQuantitativeBounds.curLog beta := by gcongr
    _ ≤ 2 ^ 18 * CyclicQuantitativeBounds.curLog beta := by
      nlinarith [show 0 ≤ CyclicQuantitativeBounds.curLog beta by positivity]

lemma initial_rankCeiling_upper (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set (ZMod N))) :
    let beta : ℝ := (A.card : ℝ) / N
    let L := CyclicQuantitativeBounds.curLog beta
    CyclicNestedIteration.rankCeiling (initialState A hA hfree) ≤
      2 ^ 159 * L ^ 7 := by
  dsimp only
  let beta : ℝ := (A.card : ℝ) / N
  let L := CyclicQuantitativeBounds.curLog beta
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    exact div_pos (by exact_mod_cast hA.card_pos) hN0
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    rw [div_le_one hN0]
    exact_mod_cast (by simpa [ZMod.card] using A.card_le_univ)
  have hL1 : (1 : ℝ) ≤ L :=
    CyclicQuantitativeBounds.one_le_curLog hbeta0 hbeta1
  have hJ := iterationBudget_cast_upper hbeta0 hbeta1
  unfold CyclicNestedIteration.rankCeiling
  simp only [initialState_bohr, baseBohr_rank, Nat.cast_one, initialState_beta]
  dsimp only [L, beta] at hJ ⊢
  calc
    1 + (CyclicNestedIteration.iterationBudget ((A.card : ℝ) / N) : ℝ) *
          (2 ^ 140 * CyclicQuantitativeBounds.curLog ((A.card : ℝ) / N) ^ 6) ≤
        1 + (2 ^ 18 * CyclicQuantitativeBounds.curLog ((A.card : ℝ) / N)) *
          (2 ^ 140 * CyclicQuantitativeBounds.curLog ((A.card : ℝ) / N) ^ 6) := by
      gcongr
    _ ≤ 2 ^ 159 * CyclicQuantitativeBounds.curLog ((A.card : ℝ) / N) ^ 7 := by
      have hL7 : (1 : ℝ) ≤
          CyclicQuantitativeBounds.curLog ((A.card : ℝ) / N) ^ 7 :=
        one_le_pow₀ hL1
      have hL0 : 0 ≤ CyclicQuantitativeBounds.curLog ((A.card : ℝ) / N) :=
        (by norm_num : (0 : ℝ) ≤ 1).trans hL1
      nlinarith [pow_nonneg hL0 6]

lemma regularityParameter_le_exp {beta : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) :
    (regularityParameter beta : ℝ) ≤
      Real.exp (22 * CyclicQuantitativeBounds.curLog beta) := by
  let L := CyclicQuantitativeBounds.curLog beta
  have hL1 : (1 : ℝ) ≤ L :=
    CyclicQuantitativeBounds.one_le_curLog hbeta0 hbeta1
  have htwo := two_pow_le_exp_nat_mul (k := 21) hL1
  have hinv : beta⁻¹ ≤ Real.exp L := by
    rw [inv_eq_exp_curLog_sub_one hbeta0]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    (regularityParameter beta : ℝ) ≤ 2 ^ 21 * beta⁻¹ :=
      regularityParameter_cast_upper hbeta0 hbeta1
    _ ≤ Real.exp (21 * L) * Real.exp L :=
      mul_le_mul htwo hinv (inv_pos.mpr hbeta0).le (Real.exp_pos _).le
    _ = Real.exp (22 * L) := by rw [← Real.exp_add]; congr 1 <;> ring

lemma initial_entropy_succ_le_exp (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set (ZMod N))) :
    let beta : ℝ := (A.card : ℝ) / N
    let L := CyclicQuantitativeBounds.curLog beta
    ((initialState A hA hfree).entropyBudget + 1 : ℝ) ≤
      Real.exp (149 * L) := by
  dsimp only
  let beta : ℝ := (A.card : ℝ) / N
  let L := CyclicQuantitativeBounds.curLog beta
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    exact div_pos (by exact_mod_cast hA.card_pos) hN0
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    rw [div_le_one hN0]
    exact_mod_cast (by simpa [ZMod.card] using A.card_le_univ)
  have hL1 : (1 : ℝ) ≤ L :=
    CyclicQuantitativeBounds.one_le_curLog hbeta0 hbeta1
  have hL0 : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans hL1
  have hM := initial_entropy_cast_upper A hA hfree
  have hM' : ((initialState A hA hfree).entropyBudget + 1 : ℝ) ≤
      2 ^ 142 * L ^ 6 := by
    have hL6 : (1 : ℝ) ≤ L ^ 6 := one_le_pow₀ hL1
    dsimp only [beta, L] at hM ⊢
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith [pow_nonneg hL0 6]
  have htwo := two_pow_le_exp_nat_mul (k := 142) hL1
  have hpow := pow_le_exp_nat_mul (k := 6) hL0
  calc
    ((initialState A hA hfree).entropyBudget + 1 : ℝ) ≤
        2 ^ 142 * L ^ 6 := hM'
    _ ≤ Real.exp (142 * L) * Real.exp (6 * L) :=
      mul_le_mul htwo hpow (by positivity) (Real.exp_pos _).le
    _ = Real.exp (148 * L) := by rw [← Real.exp_add]; congr 1 <;> ring
    _ ≤ Real.exp (149 * L) := Real.exp_le_exp.mpr (by nlinarith)

lemma initial_rankCeiling_le_exp (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set (ZMod N))) :
    let beta : ℝ := (A.card : ℝ) / N
    let L := CyclicQuantitativeBounds.curLog beta
    CyclicNestedIteration.rankCeiling (initialState A hA hfree) ≤
      Real.exp (167 * L) := by
  dsimp only
  let beta : ℝ := (A.card : ℝ) / N
  let L := CyclicQuantitativeBounds.curLog beta
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    exact div_pos (by exact_mod_cast hA.card_pos) hN0
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    rw [div_le_one hN0]
    exact_mod_cast (by simpa [ZMod.card] using A.card_le_univ)
  have hL1 : (1 : ℝ) ≤ L :=
    CyclicQuantitativeBounds.one_le_curLog hbeta0 hbeta1
  have hL0 : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans hL1
  have hR := initial_rankCeiling_upper A hA hfree
  have htwo := two_pow_le_exp_nat_mul (k := 159) hL1
  have hpow := pow_le_exp_nat_mul (k := 7) hL0
  calc
    CyclicNestedIteration.rankCeiling (initialState A hA hfree) ≤
        2 ^ 159 * L ^ 7 := hR
    _ ≤ Real.exp (159 * L) * Real.exp (7 * L) :=
      mul_le_mul htwo hpow (by positivity) (Real.exp_pos _).le
    _ = Real.exp (166 * L) := by rw [← Real.exp_add]; congr 1 <;> ring
    _ ≤ Real.exp (167 * L) := Real.exp_le_exp.mpr (by nlinarith)

lemma beta_eq_exp_one_sub_curLog {beta : ℝ} (hbeta : 0 < beta) :
    beta = Real.exp (1 - CyclicQuantitativeBounds.curLog beta) := by
  have hlog : Real.log beta = 1 - CyclicQuantitativeBounds.curLog beta := by
    unfold CyclicQuantitativeBounds.curLog
    rw [Real.log_inv]
    ring
  rw [← hlog, Real.exp_log hbeta]

lemma initial_uniformRadiusFactor_lower
    (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set (ZMod N))) :
    let beta : ℝ := (A.card : ℝ) / N
    let L := CyclicQuantitativeBounds.curLog beta
    Real.exp (-2048 * L) ≤
      CyclicNestedIteration.uniformRadiusFactor (initialState A hA hfree) := by
  dsimp only
  let beta : ℝ := (A.card : ℝ) / N
  let L := CyclicQuantitativeBounds.curLog beta
  let s := initialState A hA hfree
  let num : ℝ := (1 - 1 / 8192 : ℝ) * beta
  let den : ℝ :=
    2 ^ 51 * 400 ^ 5 * (regularityParameter beta : ℝ) ^ 3 *
      (s.entropyBudget + 1 : ℝ) *
        CyclicNestedIteration.rankCeiling s ^ 7
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    exact div_pos (by exact_mod_cast hA.card_pos) hN0
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    rw [div_le_one hN0]
    exact_mod_cast (by simpa [ZMod.card] using A.card_le_univ)
  have hL1 : (1 : ℝ) ≤ L :=
    CyclicQuantitativeBounds.one_le_curLog hbeta0 hbeta1
  have hL0 : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans hL1
  have hconst : (2 ^ 51 * 400 ^ 5 : ℝ) ≤ Real.exp (96 * L) := by
    calc
      (2 ^ 51 * 400 ^ 5 : ℝ) ≤ (2 : ℝ) ^ 96 := by norm_num
      _ ≤ Real.exp (96 * L) := two_pow_le_exp_nat_mul hL1
  have hm := regularityParameter_le_exp hbeta0 hbeta1
  have hm3 : (regularityParameter beta : ℝ) ^ 3 ≤
      Real.exp (66 * L) := by
    calc
      (regularityParameter beta : ℝ) ^ 3 ≤
          Real.exp (22 * L) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hm 3
      _ = Real.exp (66 * L) := by rw [← Real.exp_nat_mul]; congr 1 <;> ring
  have hM : (s.entropyBudget + 1 : ℝ) ≤ Real.exp (149 * L) := by
    dsimp only [s, beta, L]
    exact initial_entropy_succ_le_exp A hA hfree
  have hR := initial_rankCeiling_le_exp A hA hfree
  have hR7 : CyclicNestedIteration.rankCeiling s ^ 7 ≤
      Real.exp (1169 * L) := by
    calc
      CyclicNestedIteration.rankCeiling s ^ 7 ≤
          Real.exp (167 * L) ^ 7 :=
        pow_le_pow_left₀ (CyclicNestedIteration.rankCeiling_pos s).le
          (by simpa only [s, beta, L] using hR) 7
      _ = Real.exp (1169 * L) := by
        rw [← Real.exp_nat_mul]
        congr 1 <;> ring
  have hRpow0 : 0 ≤ CyclicNestedIteration.rankCeiling s ^ 7 :=
    pow_nonneg (CyclicNestedIteration.rankCeiling_pos s).le _
  have hden : den ≤ Real.exp (1480 * L) := by
    dsimp only [den]
    calc
      2 ^ 51 * 400 ^ 5 * (regularityParameter beta : ℝ) ^ 3 *
            (s.entropyBudget + 1 : ℝ) *
            CyclicNestedIteration.rankCeiling s ^ 7 ≤
          (Real.exp (96 * L) * Real.exp (66 * L)) *
            Real.exp (149 * L) * Real.exp (1169 * L) := by
        gcongr
      _ = Real.exp (1480 * L) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1 <;> ring
  have hden0 : 0 < den := by
    dsimp only [den, s]
    have hm0 : (0 : ℝ) < regularityParameter beta := by
      exact_mod_cast (regularityParameter_large hbeta0 hbeta1).trans_lt'
        (by omega)
    exact mul_pos (mul_pos (mul_pos (by positivity) (by positivity)) (by positivity))
      (pow_pos (CyclicNestedIteration.rankCeiling_pos _) _)
  have htwoL : (2 : ℝ) ≤ Real.exp L := by
    calc
      (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hL1
  have hhalf : Real.exp (-L) ≤ (1 / 2 : ℝ) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hmul := mul_le_mul_of_nonneg_right htwoL (Real.exp_pos (-L)).le
    rw [← Real.exp_add] at hmul
    norm_num at hmul ⊢
    simpa [add_comm, mul_comm] using hmul
  have hbetaExp : Real.exp (-L) ≤ beta := by
    rw [beta_eq_exp_one_sub_curLog hbeta0]
    exact Real.exp_le_exp.mpr (by linarith)
  have hnum : Real.exp (-2 * L) ≤ num := by
    dsimp only [num]
    calc
      Real.exp (-2 * L) = Real.exp (-L) * Real.exp (-L) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
      _ ≤ (1 / 2 : ℝ) * beta :=
        mul_le_mul hhalf hbetaExp (Real.exp_pos _).le (by norm_num)
      _ ≤ (1 - 1 / 8192 : ℝ) * beta := by
        exact mul_le_mul_of_nonneg_right (by norm_num) hbeta0.le
  have hratio : Real.exp (-2048 * L) ≤
      Real.exp (-2 * L) / Real.exp (1480 * L) := by
    rw [← Real.exp_sub]
    exact Real.exp_le_exp.mpr (by nlinarith)
  unfold CyclicNestedIteration.uniformRadiusFactor
  simp only [initialState_beta, initialState_bohr, baseBohr_rank]
  change Real.exp (-2048 * L) ≤ num / den
  calc
    Real.exp (-2048 * L) ≤
        Real.exp (-2 * L) / Real.exp (1480 * L) := hratio
    _ ≤ num / Real.exp (1480 * L) :=
      (div_le_div_iff_of_pos_right (Real.exp_pos _)).2 hnum
    _ ≤ num / den :=
      div_le_div_of_nonneg_left (by dsimp only [num]; positivity) hden0 hden

lemma initial_iteration_radius_lower
    (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set (ZMod N))) :
    let beta : ℝ := (A.card : ℝ) / N
    let L := CyclicQuantitativeBounds.curLog beta
    let q := CyclicNestedIteration.uniformRadiusFactor (initialState A hA hfree)
    let J := CyclicNestedIteration.iterationBudget beta
    Real.exp (-(2 ^ 29) * L ^ 2) ≤ q ^ J := by
  dsimp only
  let beta : ℝ := (A.card : ℝ) / N
  let L := CyclicQuantitativeBounds.curLog beta
  let q := CyclicNestedIteration.uniformRadiusFactor (initialState A hA hfree)
  let J := CyclicNestedIteration.iterationBudget beta
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    exact div_pos (by exact_mod_cast hA.card_pos) hN0
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    rw [div_le_one hN0]
    exact_mod_cast (by simpa [ZMod.card] using A.card_le_univ)
  have hL1 : (1 : ℝ) ≤ L :=
    CyclicQuantitativeBounds.one_le_curLog hbeta0 hbeta1
  have hL0 : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans hL1
  have hq : Real.exp (-2048 * L) ≤ q := by
    dsimp only [q, beta, L]
    exact initial_uniformRadiusFactor_lower A hA hfree
  have hJ : (J : ℝ) ≤ 2 ^ 18 * L := by
    dsimp only [J]
    exact iterationBudget_cast_upper hbeta0 hbeta1
  have hexponent : -(2 ^ 29 : ℝ) * L ^ 2 ≤
      (J : ℝ) * (-2048 * L) := by
    have hneg : -2048 * L ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by norm_num) hL0
    have hmul := mul_le_mul_of_nonpos_right hJ hneg
    nlinarith [sq_nonneg L]
  calc
    Real.exp (-(2 ^ 29) * L ^ 2) ≤
        Real.exp ((J : ℝ) * (-2048 * L)) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp (-2048 * L) ^ J := by rw [← Real.exp_nat_mul]
    _ ≤ q ^ J := pow_le_pow_left₀ (Real.exp_pos _).le hq J

lemma radiusCode_succ_le_exp {L r : ℝ}
    (hL : 1 ≤ L) (hr : 0 < r)
    (hrlower : Real.exp (-(2 ^ 29) * L ^ 2) ≤ r) :
    (radiusCode r + 1 : ℝ) ≤ Real.exp ((2 ^ 30) * L ^ 2) := by
  have hL20 : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL
  have hrExp : r⁻¹ ≤ Real.exp ((2 ^ 29) * L ^ 2) := by
    have hinv := inv_anti₀ (Real.exp_pos (-(2 ^ 29) * L ^ 2)) hrlower
    calc
      r⁻¹ ≤ (Real.exp (-(2 ^ 29) * L ^ 2))⁻¹ := hinv
      _ = Real.exp ((2 ^ 29) * L ^ 2) := by
        simpa only [neg_mul, neg_neg] using
          (Real.exp_neg (-((2 ^ 29) * L ^ 2))).symm
  have hcode := (radiusCode_cast_lt hr).le
  have hpi : 4 * Real.pi ≤ (16 : ℝ) := by nlinarith [Real.pi_lt_four]
  have hsum : (radiusCode r + 1 : ℝ) ≤
      32 * Real.exp ((2 ^ 29) * L ^ 2) := by
    norm_num only [Nat.cast_add, Nat.cast_one] at hcode
    calc
      (radiusCode r : ℝ) + 1 ≤ 4 * Real.pi / r + 2 := by linarith
      _ = (4 * Real.pi) * r⁻¹ + 2 := by rw [div_eq_mul_inv]
      _ ≤ 16 * Real.exp ((2 ^ 29) * L ^ 2) + 2 := by
        gcongr
      _ ≤ 32 * Real.exp ((2 ^ 29) * L ^ 2) := by
        have hexp1 : (1 : ℝ) ≤ Real.exp ((2 ^ 29) * L ^ 2) :=
          Real.one_le_exp (by positivity)
        nlinarith
  have h32 : (32 : ℝ) ≤ Real.exp (5 * L ^ 2) := by
    convert two_pow_le_exp_nat_mul (k := 5) hL20 using 1 <;> norm_num
  calc
    (radiusCode r + 1 : ℝ) ≤
        32 * Real.exp ((2 ^ 29) * L ^ 2) := hsum
    _ ≤ Real.exp (5 * L ^ 2) * Real.exp ((2 ^ 29) * L ^ 2) := by
      gcongr
    _ = Real.exp ((2 ^ 29 + 5) * L ^ 2) := by
      rw [← Real.exp_add]
      congr 1 <;> ring
    _ ≤ Real.exp ((2 ^ 30) * L ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg L]

lemma carrier_succ_le_exp {beta C : ℝ}
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1) (hC0 : 0 ≤ C)
    (hC : C < 2 / (((1 - 1 / 8192 : ℝ) * beta) ^ 2)) :
    C + 1 ≤ Real.exp (8 * CyclicQuantitativeBounds.curLog beta) := by
  let L := CyclicQuantitativeBounds.curLog beta
  have hL1 : (1 : ℝ) ≤ L :=
    CyclicQuantitativeBounds.one_le_curLog hbeta0 hbeta1
  have hL0 : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans hL1
  have htwoL : (2 : ℝ) ≤ Real.exp L := by
    calc
      (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hL1
  have hhalf : Real.exp (-L) ≤ (1 / 2 : ℝ) := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hmul := mul_le_mul_of_nonneg_right htwoL (Real.exp_pos (-L)).le
    rw [← Real.exp_add] at hmul
    norm_num at hmul ⊢
    simpa [mul_comm] using hmul
  have hbetaExp : Real.exp (-L) ≤ beta := by
    rw [beta_eq_exp_one_sub_curLog hbeta0]
    exact Real.exp_le_exp.mpr (by linarith)
  have halpha : (1 / 2 : ℝ) ≤ 1 - 1 / 8192 := by norm_num
  have hprod : Real.exp (-L) / 2 ≤
      (1 - 1 / 8192 : ℝ) * beta := by
    calc
      Real.exp (-L) / 2 = (1 / 2 : ℝ) * Real.exp (-L) := by ring
      _ ≤ (1 - 1 / 8192 : ℝ) * beta :=
        mul_le_mul halpha hbetaExp (Real.exp_pos _).le (by norm_num)
  have hsq : (Real.exp (-L) / 2) ^ 2 ≤
      ((1 - 1 / 8192 : ℝ) * beta) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hprod 2
  have hsmall0 : 0 < (Real.exp (-L) / 2) ^ 2 := by positivity
  have hdiv : 2 / (((1 - 1 / 8192 : ℝ) * beta) ^ 2) ≤
      8 * Real.exp (2 * L) := by
    calc
      2 / (((1 - 1 / 8192 : ℝ) * beta) ^ 2) ≤
          2 / (Real.exp (-L) / 2) ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) hsmall0 hsq
      _ = 8 * Real.exp (2 * L) := by
        rw [Real.exp_neg]
        field_simp [ne_of_gt (Real.exp_pos L)]
        norm_num
        rw [← Real.exp_nat_mul]
        congr 1 <;> ring
  have hC' : C + 1 ≤ 9 * Real.exp (2 * L) := by
    have hexp1 : (1 : ℝ) ≤ Real.exp (2 * L) :=
      Real.one_le_exp (by positivity)
    nlinarith
  have h16 : (16 : ℝ) ≤ Real.exp (4 * L) := by
    convert two_pow_le_exp_nat_mul (k := 4) hL1 using 1 <;> norm_num
  calc
    C + 1 ≤ 9 * Real.exp (2 * L) := hC'
    _ ≤ 16 * Real.exp (2 * L) := by gcongr <;> norm_num
    _ ≤ Real.exp (4 * L) * Real.exp (2 * L) := by gcongr
    _ = Real.exp (6 * L) := by rw [← Real.exp_add]; congr 1 <;> ring
    _ ≤ Real.exp (8 * L) := Real.exp_le_exp.mpr (by nlinarith)

/-- The quantitative cyclic Roth estimate in logarithmic form. -/
theorem threeAPFree_log_bound (hN : Odd N)
    (A : Finset (ZMod N)) (hA : A.Nonempty)
    (hfree : ThreeAPFree (A : Set (ZMod N))) :
    Real.log (N : ℝ) <
      2 ^ 190 *
        CyclicQuantitativeBounds.curLog ((A.card : ℝ) / N) ^ 9 := by
  let beta : ℝ := (A.card : ℝ) / N
  let L := CyclicQuantitativeBounds.curLog beta
  let s := initialState A hA hfree
  let q := CyclicNestedIteration.uniformRadiusFactor s
  let J := CyclicNestedIteration.iterationBudget beta
  let r := q ^ J
  obtain ⟨st, hrank, hcarrier, hradius, hgroup⟩ :=
    exists_terminal_cardinality_package hN A hA hfree
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (NeZero.pos N)
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    exact div_pos (by exact_mod_cast hA.card_pos) hN0
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    rw [div_le_one hN0]
    exact_mod_cast (by simpa [ZMod.card] using A.card_le_univ)
  have hL1 : (1 : ℝ) ≤ L :=
    CyclicQuantitativeBounds.one_le_curLog hbeta0 hbeta1
  have hL0 : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans hL1
  have hr0 : 0 < r := by
    dsimp only [r]
    exact pow_pos (by
      dsimp only [q]
      exact CyclicNestedIteration.uniformRadiusFactor_pos s) _
  have hrlower : Real.exp (-(2 ^ 29) * L ^ 2) ≤ r := by
    dsimp only [r, q, J, s, beta, L]
    exact initial_iteration_radius_lower A hA hfree
  have hcode : (radiusCode r + 1 : ℝ) ≤
      Real.exp ((2 ^ 30) * L ^ 2) := radiusCode_succ_le_exp hL1 hr0 hrlower
  have hrank' : (st.B.rank : ℝ) ≤ 2 ^ 159 * L ^ 7 := by
    exact hrank.trans (by
      dsimp only [s, beta, L]
      exact initial_rankCeiling_upper A hA hfree)
  let D : ℕ := (radiusCode r + 1) ^ st.B.rank
  have hD : (D : ℝ) ≤ Real.exp ((2 ^ 189) * L ^ 9) := by
    have hcode' : (((radiusCode r + 1 : ℕ) : ℝ)) ≤
        Real.exp ((2 ^ 30) * L ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hcode
    have hpow : ((radiusCode r + 1 : ℕ) : ℝ) ^ st.B.rank ≤
        Real.exp ((2 ^ 30) * L ^ 2) ^ st.B.rank :=
      pow_le_pow_left₀ (by positivity) hcode' st.B.rank
    have hexponent : (st.B.rank : ℝ) * ((2 ^ 30) * L ^ 2) ≤
        (2 ^ 189 : ℝ) * L ^ 9 := by
      have hmul := mul_le_mul_of_nonneg_right hrank' (by positivity :
        0 ≤ (2 ^ 30 : ℝ) * L ^ 2)
      nlinarith [pow_nonneg hL0 7, pow_nonneg hL0 9]
    calc
      (D : ℝ) = ((radiusCode r + 1 : ℕ) : ℝ) ^ st.B.rank := by
        simp only [D, Nat.cast_pow]
      _ ≤ Real.exp ((2 ^ 30) * L ^ 2) ^ st.B.rank := hpow
      _ = Real.exp ((st.B.rank : ℝ) * ((2 ^ 30) * L ^ 2)) := by
        rw [← Real.exp_nat_mul]
      _ ≤ Real.exp ((2 ^ 189) * L ^ 9) :=
        Real.exp_le_exp.mpr hexponent
  have hcarrier' : (st.carrier.card + 1 : ℝ) ≤ Real.exp (8 * L) := by
    apply carrier_succ_le_exp hbeta0 hbeta1 (by positivity)
    simpa only [beta] using hcarrier
  have hgroupR : (N : ℝ) < (st.carrier.card + 1 : ℝ) * (D : ℝ) := by
    exact_mod_cast (by simpa only [D] using hgroup)
  have hproduct : (N : ℝ) < Real.exp ((2 ^ 190) * L ^ 9) := by
    calc
      (N : ℝ) < (st.carrier.card + 1 : ℝ) * (D : ℝ) := hgroupR
      _ ≤ Real.exp (8 * L) * Real.exp ((2 ^ 189) * L ^ 9) :=
        mul_le_mul hcarrier' hD (by positivity) (Real.exp_pos _).le
      _ = Real.exp (8 * L + (2 ^ 189) * L ^ 9) := by rw [Real.exp_add]
      _ ≤ Real.exp ((2 ^ 190) * L ^ 9) := by
        apply Real.exp_le_exp.mpr
        have hLleL9 : L ≤ L ^ 9 := by
          calc
            L = L * 1 := by ring
            _ ≤ L * L ^ 8 := by
              gcongr
              exact one_le_pow₀ hL1
            _ = L ^ 9 := by ring
        nlinarith [pow_nonneg hL0 9]
  have hlog := Real.strictMonoOn_log hN0 (Real.exp_pos _) hproduct
  rw [Real.log_exp] at hlog
  simpa only [beta, L] using hlog

/-- Supersaturation in the native `ZMod` model used by the Bohr argument. -/
theorem cyclicZModSupersaturation :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ A : Finset (ZMod (2 * n + 1)),
          ((2 * n + 1 : ℕ) : ℝ) *
              Real.exp (-c * (Real.log (n : ℝ)) ^ (1 / 9 : ℝ)) <
            (A.card : ℝ) →
          ¬ ThreeAPFree (A : Set (ZMod (2 * n + 1))) := by
  let c : ℝ := 1 / 2 ^ 24
  refine ⟨c, by dsimp only [c]; positivity, ?_⟩
  have htend : Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ (1 / 9 : ℝ))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 9)).comp
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlargeRoot : ∀ᶠ n : ℕ in atTop,
      (2 ^ 24 : ℝ) ≤ (Real.log (n : ℝ)) ^ (1 / 9 : ℝ) :=
    (tendsto_atTop.1 htend (2 ^ 24))
  filter_upwards [hlargeRoot, eventually_ge_atTop (3 : ℕ)] with n hnroot hn
  intro A hA hfree
  let M := 2 * n + 1
  let beta : ℝ := (A.card : ℝ) / M
  let L := CyclicQuantitativeBounds.curLog beta
  let y : ℝ := (Real.log (n : ℝ)) ^ (1 / 9 : ℝ)
  change (M : ℝ) * Real.exp (-c * y) < (A.card : ℝ) at hA
  have hM0 : (0 : ℝ) < M := by dsimp only [M]; positivity
  have hthreshold : 0 < (M : ℝ) * Real.exp (-c * y) := by positivity
  have hAcard : 0 < A.card := by
    exact_mod_cast hthreshold.trans hA
  have hAnonempty : A.Nonempty := Finset.card_pos.mp hAcard
  have hbeta0 : 0 < beta := by
    dsimp only [beta]
    exact div_pos (by exact_mod_cast hAcard) hM0
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    rw [div_le_one hM0]
    exact_mod_cast (by simpa [M, ZMod.card] using A.card_le_univ)
  have hL1 : (1 : ℝ) ≤ L :=
    CyclicQuantitativeBounds.one_le_curLog hbeta0 hbeta1
  have hL0 : 0 ≤ L := (by norm_num : (0 : ℝ) ≤ 1).trans hL1
  have hdensity : Real.exp (-c * y) < beta := by
    dsimp only [beta, M] at hA ⊢
    exact (lt_div_iff₀ (by positivity : (0 : ℝ) < (2 * n + 1 : ℕ))).2
      (by simpa [mul_comm] using hA)
  have hlogDensity := Real.strictMonoOn_log (Real.exp_pos _) hbeta0 hdensity
  rw [Real.log_exp] at hlogDensity
  have hlogbeta : Real.log beta = 1 - L := by
    dsimp only [L, CyclicQuantitativeBounds.curLog]
    rw [Real.log_inv]
    ring
  have hLupper : L < 2 * c * y := by
    have hcy : (1 : ℝ) ≤ c * y := by
      dsimp only [c, y]
      have := hnroot
      norm_num at this ⊢
      nlinarith
    rw [hlogbeta] at hlogDensity
    nlinarith
  have hy0 : 0 ≤ y := by dsimp only [y]; positivity
  have hpow : L ^ 9 < (2 * c * y) ^ 9 := by
    exact pow_lt_pow_left₀ hLupper hL0 (by omega)
  have hlogn0 : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hyPow : y ^ 9 = Real.log (n : ℝ) := by
    dsimp only [y]
    convert Real.rpow_inv_natCast_pow hlogn0 (by norm_num : (9 : ℕ) ≠ 0) using 1
    norm_num
  have hquant := threeAPFree_log_bound (N := M)
    (by simpa only [M] using (odd_two_mul_add_one n)) A hAnonempty hfree
  have hsmall : (2 ^ 190 : ℝ) * L ^ 9 < Real.log (n : ℝ) := by
    calc
      (2 ^ 190 : ℝ) * L ^ 9 < 2 ^ 190 * (2 * c * y) ^ 9 := by
        exact mul_lt_mul_of_pos_left hpow (by positivity)
      _ = (1 / 2 ^ 17 : ℝ) * y ^ 9 := by
        dsimp only [c]
        ring
      _ ≤ Real.log (n : ℝ) := by
        rw [hyPow]
        exact mul_le_of_le_one_left hlogn0 (by norm_num)
  have hlognM : Real.log (n : ℝ) ≤ Real.log (M : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
    exact_mod_cast (show n ≤ M by dsimp only [M]; omega)
  exact (not_lt_of_ge hlognM) (hquant.trans hsmall)

end CyclicRothEndpoint
end Erdos721
