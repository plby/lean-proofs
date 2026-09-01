/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/
import ErdosProblems.Erdos55.UpperRobustBlock

/-!
# Sampling the arbitrary-color robust block

For fixed `r`, the enlarged sample still has only `O(r log x)` coordinates.
The inverse-superpolynomial cyclic failure estimate therefore beats the
coordinate union bound, and the supply of rough numbers beats the quadratic
collision term.  This file makes those two eventual comparisons explicit.
-/

namespace Erdos55

open Filter

/-- Every fixed cubic polynomial is eventually smaller than `2^u`. -/
theorem eventually_const_mul_cube_lt_two_pow (C : ℕ) :
    ∀ᶠ u : ℕ in atTop, C * u ^ 3 < 2 ^ u := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 3
    (show (1 : ℝ) < 2 by norm_num)
  have hpos : (0 : ℝ) < 1 / (C + 1) := by positivity
  filter_upwards [hlim.eventually_lt_const hpos] with u hu
  have hpow : (0 : ℝ) < (2 : ℝ) ^ u := by positivity
  have hC : (0 : ℝ) < C + 1 := by positivity
  have hu' : ((u : ℝ) ^ 3) < (1 / (C + 1 : ℝ)) * (2 : ℝ) ^ u := by
    rwa [div_lt_iff₀ hpow] at hu
  have hmul := mul_lt_mul_of_pos_left hu' hC
  have hreal : (C : ℝ) * (u : ℝ) ^ 3 < (2 : ℝ) ^ u := by
    have hsimp : (C + 1 : ℝ) *
        ((1 / (C + 1 : ℝ)) * (2 : ℝ) ^ u) = (2 : ℝ) ^ u := by
      field_simp
    rw [hsimp] at hmul
    nlinarith [show (0 : ℝ) ≤ (u : ℝ) ^ 3 by positivity]
  exact_mod_cast hreal

private theorem two_pow_pred_cyclicLogScale_lt {x : ℕ} (hx : 2 ≤ x) :
    2 ^ (Erdos54.cyclicLogScale x - 1) < x := by
  let u := Erdos54.cyclicLogScale x
  have hu : 0 < u := Erdos54.cyclicLogScale_pos hx
  have hlog0 : 0 ≤ Real.log (x : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have hu_lt : (u : ℝ) < Real.log (x : ℝ) + 1 :=
    Nat.ceil_lt_add_one hlog0
  have hpredlog : ((u - 1 : ℕ) : ℝ) < Real.log (x : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    nlinarith
  have hpowexp : ((2 ^ (u - 1) : ℕ) : ℝ) ≤ Real.exp (u - 1 : ℕ) := by
    push_cast
    rw [← Real.exp_one_pow]
    gcongr
    exact Real.exp_one_gt_two.le
  have hexplog : Real.exp (u - 1 : ℕ) < (x : ℝ) := by
    have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    calc
      Real.exp (u - 1 : ℕ) < Real.exp (Real.log (x : ℝ)) :=
        Real.exp_lt_exp.mpr hpredlog
      _ = x := Real.exp_log hxpos
  exact_mod_cast hpowexp.trans_lt hexplog

theorem r_cyclic_collision_supply_of_bounds {r x : ℕ}
    (h : Erdos54.CyclicGrowthParameterBounds x)
    (hexp : 2 ^ 32 * r ^ 2 * Erdos54.cyclicLogScale x ^ 3 <
      2 ^ Erdos54.cyclicLogScale x) :
    2 * (1280 * r * Erdos54.cyclicTupleLength x) ^ 2 <
      (Erdos54.roughNumbers x).card := by
  let u := Erdos54.cyclicLogScale x
  let v := Erdos54.cyclicSecondaryScale x
  let q := Erdos54.cyclicTupleLength x
  let M := (Erdos54.roughNumbers x).card
  let T := 2 * (1280 * r * q) ^ 2
  have hu : 0 < u := h.logScale_pos
  have hvle : v ≤ u := by
    have hv : 1 ≤ v := h.secondaryScale_pos
    have hvfour : v ≤ v ^ 4 := by
      simpa only [pow_one] using
        (pow_le_pow_right' hv (show 1 ≤ 4 by omega))
    calc
      v ≤ v ^ 4 := hvfour
      _ ≤ 2 ^ 30 * v ^ 4 := by
        have hcoef : 1 ≤ 2 ^ 30 := by norm_num
        nlinarith
      _ ≤ u := by simpa [u, v] using h.secondary_fourth_le
  have hq : q ≤ 6 * u := h.tupleLength_le_six_scale
  have hT : T ≤ 2 ^ 27 * r ^ 2 * u ^ 2 := by
    have hmul : 1280 * r * q ≤ 7680 * r * u := by nlinarith
    have hsq := pow_le_pow_left' hmul 2
    dsimp only [T]
    calc
      2 * (1280 * r * q) ^ 2 ≤ 2 * (7680 * r * u) ^ 2 :=
        Nat.mul_le_mul_left 2 hsq
      _ ≤ 2 ^ 27 * r ^ 2 * u ^ 2 := by
        rw [mul_pow, mul_pow]
        have hc : 2 * 7680 ^ 2 ≤ 2 ^ 27 := by norm_num
        nlinarith
  have hpoly : 16 * v * T ≤ 2 ^ 31 * r ^ 2 * u ^ 3 := by
    calc
      16 * v * T ≤ 16 * u * (2 ^ 27 * r ^ 2 * u ^ 2) := by gcongr
      _ = 2 ^ 31 * r ^ 2 * u ^ 3 := by ring
  have hpow_eq : 2 ^ u = 2 * 2 ^ (u - 1) := by
    calc
      2 ^ u = 2 ^ ((u - 1) + 1) := by
        congr 2
        omega
      _ = 2 * 2 ^ (u - 1) := by rw [pow_succ]; ring
  have hpred : 2 ^ 31 * r ^ 2 * u ^ 3 < 2 ^ (u - 1) := by
    have hscaled : 2 * (2 ^ 31 * r ^ 2 * u ^ 3) < 2 * 2 ^ (u - 1) := by
      calc
        2 * (2 ^ 31 * r ^ 2 * u ^ 3) = 2 ^ 32 * r ^ 2 * u ^ 3 := by ring
        _ < 2 ^ u := by simpa [u] using hexp
        _ = 2 * 2 ^ (u - 1) := hpow_eq
    exact (Nat.mul_lt_mul_left (by omega : 0 < 2)).mp hscaled
  have hfactorT : 16 * v * T < x :=
    (hpoly.trans_lt hpred).trans
      (by simpa [u] using two_pow_pred_cyclicLogScale_lt h.two_le_x)
  have hTM : T < M := by
    by_contra hnot
    have hMT : M ≤ T := Nat.le_of_not_gt hnot
    have hfac : 16 * v * M ≤ 16 * v * T := Nat.mul_le_mul_left _ hMT
    have hxM : x ≤ 16 * v * M := by simpa [v, M] using h.rough_card_lower
    omega
  simpa [T, M] using hTM

/-- For each fixed number of colors, rough numbers eventually supply a
collision-free enlarged sample. -/
theorem eventually_r_cyclic_collision_supply (r : ℕ) :
    ∀ᶠ x : ℕ in atTop,
      2 * (1280 * r * Erdos54.cyclicTupleLength x) ^ 2 <
        (Erdos54.roughNumbers x).card := by
  have hexpU := eventually_const_mul_cube_lt_two_pow (2 ^ 32 * r ^ 2)
  have hexpX := Erdos54.tendsto_cyclicLogScale.eventually hexpU
  filter_upwards [Erdos54.eventually_cyclicGrowthParameterBounds, hexpX]
      with x hp hexp
  exact r_cyclic_collision_supply_of_bounds hp (by
    simpa [Nat.mul_assoc] using hexp)

/-- Finite union-bound packaging for the sample of length `1280*r*q`. -/
theorem exists_rRobustBlock_of_bad_bound
    (hlev : Erdos54.FortySetIntervalPrinciple)
    {r x q B : ℕ} (hr : 1 ≤ r)
    (hx : 200 ≤ x) (hq : 1 ≤ q) (hw : 17 ≤ Erdos54.roughCutoff x)
    (hbad : ∀ m ∈ Erdos54.roughNumbers x,
      (Erdos54.badCyclicTuples x m q).card ≤ B)
    (hsmall :
      Fintype.card
          (Erdos54.CoordinateSubset (1280 * r * q) q ×
            ↑(Erdos54.roughNumbers x)) *
            (B * (Erdos54.roughNumbers x).card ^ ((1280 * r * q) - q)) +
        (1280 * r * q) * (1280 * r * q) *
            ((Erdos54.roughNumbers x).card ^ ((1280 * r * q) - 1)) <
          (Erdos54.roughNumbers x).card ^ (1280 * r * q)) :
    ∃ S : Finset ℕ, IsRRobustBlock r x q S := by
  classical
  obtain ⟨f, hf, hgood⟩ :=
    Erdos54.exists_universallyModularGood_sample_of_bad_bound hbad hsmall
  let S := Erdos54.sampleValueSet f
  have hfNat : Function.Injective (fun i ↦ (f i : ℕ)) := by
    intro i j hij
    exact hf (Subtype.ext hij)
  have hScard : S.card = 1280 * r * q := by
    calc
      S.card = (Finset.univ : Finset (Fin (1280 * r * q))).card := by
        exact Finset.card_image_of_injective _ hfNat
      _ = 1280 * r * q := by simp
  have hSrough : S ⊆ Erdos54.roughNumbersAt x (Erdos54.roughCutoff x) := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨i, -, rfl⟩
    exact (f i).property
  exact ⟨S, isRRobustBlock_of_modularGood hlev hr hx hq hw
    hSrough hScard (by simpa [S] using hgood)⟩

/-- One sufficiently large cyclic-parameter bundle produces the enlarged
robust block. -/
theorem exists_rRobustBlock_of_parameterBounds
    (hlev : Erdos54.FortySetIntervalPrinciple) {r x : ℕ} (hr : 1 ≤ r)
    (hp : Erdos54.CyclicGrowthParameterBounds x)
    (hx : 200 ≤ x) (hcut : 17 ≤ Erdos54.roughCutoff x)
    (hlarge : 2 ^ (4 * (7680 * r + 3)) ≤ Erdos54.cyclicLogScale x)
    (hcollision :
      2 * (1280 * r * Erdos54.cyclicTupleLength x) *
          (1280 * r * Erdos54.cyclicTupleLength x) <
        (Erdos54.roughNumbers x).card) :
    ∃ S : Finset ℕ,
      IsRRobustBlock r x (Erdos54.cyclicTupleLength x) S := by
  let q := Erdos54.cyclicTupleLength x
  let u := Erdos54.cyclicLogScale x
  let M := (Erdos54.roughNumbers x).card
  let scale := u ^ (u / 2)
  let B := M ^ q / scale
  have hM : 0 < M := by
    dsimp only [M]
    by_contra hzero
    have hz : (Erdos54.roughNumbers x).card = 0 := Nat.eq_zero_of_not_pos hzero
    have hrough := hp.rough_card_lower
    rw [hz, Nat.mul_zero] at hrough
    omega
  have hscale : 0 < scale := pow_pos hp.logScale_pos _
  have hfactor :
      2 * Fintype.card
          (Erdos54.CoordinateSubset (1280 * r * q) q ×
            ↑(Erdos54.roughNumbers x)) ≤ scale := by
    exact r_coordinate_modulus_factor_le_logScale_power hr
      hp.tupleLength_le_six_scale hp.scale_le_three_pow hlarge
  have hscaledBad : ∀ m ∈ Erdos54.roughNumbers x,
      scale * (Erdos54.badCyclicTuples x m q).card ≤ M ^ q := by
    intro m hm
    exact Erdos54.rough_cyclic_failure_scaled_card_le hp.two_le_x hm
      hp.logScale_pos hp.secondaryScale_pos hp.reciprocalScale_two_le
      hp.reciprocalScale_le_logScale hp.reciprocalScale_le_cutoff
      hp.scale_le_three_pow hp.scale_le_two_pow_secondary
      hp.reciprocal_mul_secondary_le hp.five_scale_le_tupleLength
      hp.tupleLength_le_six_scale hp.scale_le_sixteen_mul
      hp.rough_card_lower hp.secondary_fourth_le
  have hbad : ∀ m ∈ Erdos54.roughNumbers x,
      (Erdos54.badCyclicTuples x m q).card ≤ B := by
    intro m hm
    apply (Nat.le_div_iff_mul_le hscale).mpr
    simpa [Nat.mul_comm] using hscaledBad m hm
  have hevent :
      2 * Fintype.card
          (Erdos54.CoordinateSubset (1280 * r * q) q ×
            ↑(Erdos54.roughNumbers x)) * B ≤ M ^ q := by
    calc
      2 * Fintype.card
          (Erdos54.CoordinateSubset (1280 * r * q) q ×
            ↑(Erdos54.roughNumbers x)) * B ≤ scale * B :=
        Nat.mul_le_mul_right B hfactor
      _ ≤ M ^ q := Nat.mul_div_le (M ^ q) scale
  have hqpos : 0 < q := by
    have : 0 < 5 * Erdos54.cyclicLogScale x :=
      Nat.mul_pos (by omega) hp.logScale_pos
    exact this.trans_le hp.five_scale_le_tupleLength
  have hqN : q ≤ 1280 * r * q := by nlinarith
  have hN : 1 ≤ 1280 * r * q := by
    exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) hqpos
  have hsmall := Erdos54.sample_counting_inequality_of_two_budgets
    (x := x) (N := 1280 * r * q) (q := q) (B := B)
    hqN hN hM hevent hcollision
  exact exists_rRobustBlock_of_bad_bound hlev hr hx hqpos hcut hbad
    (by simpa [q, M, B, scale] using hsmall)

/-- For each fixed positive number of colors, all sufficiently large scales
contain an enlarged CFP robust block. -/
theorem eventually_exists_rRobustBlock (r : ℕ) (hr : 1 ≤ r) :
    ∀ᶠ x : ℕ in atTop,
      ∃ S : Finset ℕ, IsRRobustBlock r x (Erdos54.ceilSixLog x) S := by
  have hcoord := Erdos54.tendsto_cyclicLogScale.eventually
    (eventually_ge_atTop (2 ^ (4 * (7680 * r + 3))))
  filter_upwards [Erdos54.eventually_cyclicGrowthParameterBounds,
    eventually_r_cyclic_collision_supply r,
    eventually_ge_atTop 200, Erdos54.eventually_seventeen_le_roughCutoff,
    hcoord] with x hp hcollision hx hcut hlarge
  have hcollision' :
      2 * (1280 * r * Erdos54.cyclicTupleLength x) *
          (1280 * r * Erdos54.cyclicTupleLength x) <
        (Erdos54.roughNumbers x).card := by
    simpa [pow_two, Nat.mul_assoc] using hcollision
  simpa [Erdos54.cyclicTupleLength, Erdos54.ceilSixLog] using
    exists_rRobustBlock_of_parameterBounds Erdos54.fortySetIntervalPrinciple
      hr hp hx hcut hlarge hcollision'

end Erdos55
