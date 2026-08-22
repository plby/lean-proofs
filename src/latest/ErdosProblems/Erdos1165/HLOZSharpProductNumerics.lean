/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZCanonicalWindowProductClosure

/-!
# Sharp numerical bound for the thresholded HLOZ product tail

The crude finite envelope in `HLOZCanonicalWindowProductClosure` is useful
for checking the stopped-fibre disintegration, but it loses the exponential
tail.  This file records the numerical core of the sharp replacement.

The shell-centred local CLT gives a finite uniform adjacent-window ratio, but
that ratio need not be close to one.  The fixed growth factor is therefore
chosen larger than eight times that ratio.  The elementary logarithmic bound
`log (1-x) ≤ -x` then leaves both an exponential penalty in the next-shell
threshold and enough total-dependent slack to absorb the endpoint-rank
multiplicity.
-/

open Filter Real

namespace Erdos1165.HLOZSharpProductNumerics

open HLOZProposition48Candidates NearFavoriteShells NearFavoriteThresholded

noncomputable section

/-- The fixed logarithmic rate left by the uniform Chernoff calculation. -/
noncomputable def sharpProductRate : ℝ :=
  Real.log 2 / ((shellGrowth48 + 2 : ℕ) : ℝ)

/-- The integral coefficient underlying the endpoint-rank multiplicity
constant.  Keeping this natural-number form available avoids losing the
exact finite multiplicity when the estimate is transported to `ENNReal`. -/
def sharpRankNatConstant : ℕ :=
  4 * (shellGrowth48 + 2) + 1

/-- A fixed coefficient large enough to absorb the actual endpoint-rank
multiplicity from one copy of the total-dependent exponential slack. -/
noncomputable def sharpRankConstant : ℝ :=
  sharpRankNatConstant

@[simp] lemma sharpRankConstant_eq_natCast :
    sharpRankConstant = (sharpRankNatConstant : ℝ) := rfl

@[simp] lemma ofReal_sharpRankConstant :
    ENNReal.ofReal sharpRankConstant = (sharpRankNatConstant : ENNReal) := by
  rw [sharpRankConstant_eq_natCast, ENNReal.ofReal_natCast]

/-- The sharp deterministic cost assigned to one adjacent-shell interface. -/
noncomputable def sharpInterfaceCost (threshold : ℕ → ℕ) (j : ℕ) : ℝ :=
  Real.exp (-sharpProductRate * (threshold (j + 1) + 1 : ℕ))

lemma sharpProductRate_pos : 0 < sharpProductRate := by
  unfold sharpProductRate
  positivity

/-- The maximum defining the thresholded cut pays one next-threshold copy
and `shellGrowth48` total-occupancy copies. -/
lemma nextThreshold_add_growthTotal_le_growthAddTwo_mul_cut
    (threshold : ℕ → ℕ) (j total : ℕ) :
    threshold (j + 1) + 1 + shellGrowth48 * total ≤
      (shellGrowth48 + 2) *
        thresholdedGrowthCut threshold shellGrowth48 j total := by
  let cut := thresholdedGrowthCut threshold shellGrowth48 j total
  let A := threshold (j + 1) + 1
  have hA : A ≤ cut := by
    exact le_max_left _ _
  have hgrowthCut : growthCut shellGrowth48 total ≤ cut := by
    exact le_max_right _ _
  have hdiv : shellGrowth48 * total <
      (shellGrowth48 + 1) *
        (shellGrowth48 * total / (shellGrowth48 + 1) + 1) := by
    exact Nat.lt_mul_div_succ _ (by omega)
  have hgrowth : shellGrowth48 * total ≤
      (shellGrowth48 + 1) * cut := by
    apply (Nat.le_of_lt hdiv).trans
    unfold growthCut at hgrowthCut
    exact Nat.mul_le_mul_left (shellGrowth48 + 1) hgrowthCut
  calc
    A + shellGrowth48 * total ≤ cut + (shellGrowth48 + 1) * cut :=
      Nat.add_le_add hA hgrowth
    _ = (shellGrowth48 + 2) * cut := by ring

lemma shellGrowth48_ratio_margin :
    8 * (1 + positiveInterfaceRatioConstant) ≤
      (shellGrowth48 : ℝ) := by
  have hceil := Nat.le_ceil
    (8 * (1 + positiveInterfaceRatioConstant))
  unfold shellGrowth48
  push_cast
  linarith

/-- The moment base has four copies of logarithmic slack relative to the
chosen growth factor. -/
lemma momentBase_log_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : C ≤ positiveInterfaceRatioConstant) :
    Real.log (1 + C / (1 + C)) ≤
      (((shellGrowth48 : ℝ) - 2) /
          ((shellGrowth48 : ℝ) + 2)) * Real.log 2 := by
  let b : ℝ := 1 + C / (1 + C)
  let x : ℝ := 1 / (2 * (1 + C))
  have hdenC : 0 < 1 + C := by linarith
  have hx0 : 0 < x := by
    dsimp only [x]
    positivity
  have hx1 : x < 1 := by
    dsimp only [x]
    rw [div_lt_one (by positivity : (0 : ℝ) < 2 * (1 + C))]
    nlinarith
  have hb : b = 2 * (1 - x) := by
    dsimp only [b, x]
    field_simp
    ring
  have hlogSplit : Real.log b = Real.log 2 + Real.log (1 - x) := by
    rw [hb, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by linarith : (1 - x) ≠ 0)]
  have hlogOne : Real.log (1 - x) ≤ -x := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - x)
    linarith
  have hlogTwoLe : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hgrowth : 8 * (1 + C) ≤ (shellGrowth48 : ℝ) := by
    calc
      8 * (1 + C) ≤ 8 * (1 + positiveInterfaceRatioConstant) := by
        gcongr
      _ ≤ (shellGrowth48 : ℝ) := shellGrowth48_ratio_margin
  have hgrowthDen : 0 < (shellGrowth48 : ℝ) + 2 := by positivity
  have hCDen : 0 < 2 * (1 + C) := by positivity
  have hxRate : 4 * Real.log 2 /
        ((shellGrowth48 : ℝ) + 2) ≤ x := by
    dsimp only [x]
    apply (div_le_div_iff₀ hgrowthDen hCDen).2
    have hlogNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  rw [hlogSplit]
  calc
    Real.log 2 + Real.log (1 - x) ≤ Real.log 2 - x := by linarith
    _ ≤ Real.log 2 -
        4 * Real.log 2 / ((shellGrowth48 : ℝ) + 2) := by linarith
    _ = (((shellGrowth48 : ℝ) - 2) /
          ((shellGrowth48 : ℝ) + 2)) * Real.log 2 := by
      field_simp
      ring

/-- Uniform sharp envelope for the exact-total heterogeneous product cost.
Unlike the crude `2^bound` estimate, this is independent of the total bound
and decays exponentially in the next-shell threshold. -/
theorem thresholdedProductEnvelope_le_exp_nextThreshold
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : C ≤ positiveInterfaceRatioConstant)
    (threshold : ℕ → ℕ) (j total : ℕ) :
    (1 + C / (1 + C)) ^ total /
        (2 : ℝ) ^
          thresholdedGrowthCut threshold shellGrowth48 j total ≤
      Real.exp
        (-sharpProductRate * (threshold (j + 1) + 1 : ℕ) -
          2 * sharpProductRate * (total : ℕ)) := by
  let b : ℝ := 1 + C / (1 + C)
  let cut : ℕ :=
    thresholdedGrowthCut threshold shellGrowth48 j total
  let A : ℕ := threshold (j + 1) + 1
  let G : ℝ := shellGrowth48
  let K : ℝ := ((shellGrowth48 + 2 : ℕ) : ℝ)
  have hdenC : 0 < 1 + C := by linarith
  have hb0 : 0 < b := by
    dsimp only [b]
    have : 0 ≤ C / (1 + C) := div_nonneg hC0 hdenC.le
    linarith
  have hlogb : Real.log b ≤ ((G - 2) / (G + 2)) * Real.log 2 := by
    simpa only [b, G] using momentBase_log_le hC0 hC
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hKpos : 0 < K := by dsimp only [K]; positivity
  have htotalLog :
      K * (total : ℝ) * Real.log b ≤
        (G - 2) * (total : ℝ) * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_left hlogb (Nat.cast_nonneg total)
    have h' := mul_le_mul_of_nonneg_left h hKpos.le
    dsimp only [K, G] at h' ⊢
    push_cast at h' ⊢
    field_simp at h' ⊢
    nlinarith
  have hcutNat : A + shellGrowth48 * total ≤
      (shellGrowth48 + 2) * cut := by
    exact nextThreshold_add_growthTotal_le_growthAddTwo_mul_cut
      threshold j total
  have hcutReal :
      ((A : ℝ) + G * (total : ℝ)) * Real.log 2 ≤
        (K * (cut : ℝ)) * Real.log 2 := by
    apply mul_le_mul_of_nonneg_right _ hlog2
    dsimp only [G, K]
    exact_mod_cast hcutNat
  have hlogBound :
      (total : ℝ) * Real.log b - (cut : ℝ) * Real.log 2 ≤
        -sharpProductRate * (A : ℝ) -
          2 * sharpProductRate * (total : ℝ) := by
    have hscaled : K * ((total : ℝ) * Real.log b -
        (cut : ℝ) * Real.log 2) ≤
        -(A : ℝ) * Real.log 2 -
          2 * (total : ℝ) * Real.log 2 := by
      dsimp only [K, G] at htotalLog hcutReal ⊢
      push_cast at htotalLog hcutReal ⊢
      nlinarith
    calc
      (total : ℝ) * Real.log b - (cut : ℝ) * Real.log 2 ≤
          (-(A : ℝ) * Real.log 2 -
            2 * (total : ℝ) * Real.log 2) / K :=
        (le_div_iff₀ hKpos).2 (by simpa [mul_comm] using hscaled)
      _ = -sharpProductRate * (A : ℝ) -
          2 * sharpProductRate * (total : ℝ) := by
        unfold sharpProductRate
        dsimp only [K]
        push_cast
        ring
  have hleft : 0 < b ^ total / (2 : ℝ) ^ cut := by positivity
  rw [← Real.log_le_iff_le_exp hleft]
  rw [Real.log_div (pow_ne_zero _ hb0.ne') (pow_ne_zero _ (by norm_num)),
    Real.log_pow, Real.log_pow]
  simpa only [b, cut, A] using hlogBound

theorem thresholdedProductEnvelope_le_sharpInterfaceCost
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : C ≤ positiveInterfaceRatioConstant)
    (threshold : ℕ → ℕ) (j total : ℕ) :
    (1 + C / (1 + C)) ^ total /
        (2 : ℝ) ^
          thresholdedGrowthCut threshold shellGrowth48 j total ≤
      sharpInterfaceCost threshold j := by
  have h := thresholdedProductEnvelope_le_exp_nextThreshold
    C hC0 hC threshold j total
  refine h.trans ?_
  unfold sharpInterfaceCost
  apply Real.exp_le_exp.mpr
  have hnonneg : 0 ≤ sharpProductRate * (total : ℝ) :=
    mul_nonneg sharpProductRate_pos.le (Nat.cast_nonneg _)
  linarith

lemma sharpInterfaceCost_pos (threshold : ℕ → ℕ) (j : ℕ) :
    0 < sharpInterfaceCost threshold j := by
  unfold sharpInterfaceCost
  positivity

lemma sharpInterfaceCost_nonneg (threshold : ℕ → ℕ) (j : ℕ) :
    0 ≤ sharpInterfaceCost threshold j :=
  (sharpInterfaceCost_pos threshold j).le

lemma sharpRankConstant_pos : 0 < sharpRankConstant := by
  unfold sharpRankConstant sharpRankNatConstant
  positivity

/-- The two copies of total-dependent slack in the sharp envelope absorb the
linear endpoint-rank multiplicity uniformly in the realized pair total. -/
theorem rankMultiplicity_mul_thresholdedProductEnvelope_le_sharp
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : C ≤ positiveInterfaceRatioConstant)
    (threshold : ℕ → ℕ) (j total : ℕ) :
    ((2 * total + 1 : ℕ) : ℝ) *
        ((1 + C / (1 + C)) ^ total /
          (2 : ℝ) ^
            thresholdedGrowthCut threshold shellGrowth48 j total) ≤
      sharpRankConstant * sharpInterfaceCost threshold j := by
  let A : ℕ := threshold (j + 1) + 1
  let K : ℝ := ((shellGrowth48 + 2 : ℕ) : ℝ)
  have henvelope := thresholdedProductEnvelope_le_exp_nextThreshold
    C hC0 hC threshold j total
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 :=
    Real.log_two_gt_d9.le.trans' (by norm_num)
  have hKpos : 0 < K := by dsimp only [K]; positivity
  have hRpos : 0 < sharpRankConstant := sharpRankConstant_pos
  have hRrate : 2 ≤ sharpRankConstant * sharpProductRate := by
    have hscaled : 2 * K ≤ sharpRankConstant * Real.log 2 := by
      unfold sharpRankConstant sharpRankNatConstant
      dsimp only [K]
      push_cast
      nlinarith
    unfold sharpProductRate
    have hdiv := (le_div_iff₀ hKpos).2 hscaled
    calc
      2 ≤ sharpRankConstant * Real.log 2 / K := hdiv
      _ = sharpRankConstant * (Real.log 2 / K) := by ring
  have hmult : ((2 * total + 1 : ℕ) : ℝ) ≤
      sharpRankConstant *
        Real.exp (sharpProductRate * (total : ℝ)) := by
    have hexp := Real.add_one_le_exp
      (sharpProductRate * (total : ℝ))
    have hlinear : ((2 * total + 1 : ℕ) : ℝ) ≤
        sharpRankConstant *
          (1 + sharpProductRate * (total : ℝ)) := by
      have hRone : 1 ≤ sharpRankConstant := by
        rw [sharpRankConstant_eq_natCast]
        exact_mod_cast (show 1 ≤ sharpRankNatConstant by
          unfold sharpRankNatConstant
          omega)
      have hslope : 2 * (total : ℝ) ≤
          (sharpRankConstant * sharpProductRate) * (total : ℝ) :=
        mul_le_mul_of_nonneg_right hRrate (Nat.cast_nonneg _)
      push_cast
      nlinarith
    exact hlinear.trans
      (mul_le_mul_of_nonneg_left (by simpa [add_comm] using hexp) hRpos.le)
  have hdecay :
      Real.exp (sharpProductRate * (total : ℝ)) *
          Real.exp (-2 * sharpProductRate * (total : ℝ)) ≤ 1 := by
    rw [← Real.exp_add, Real.exp_le_one_iff]
    have hnonneg := mul_nonneg sharpProductRate_pos.le
      (Nat.cast_nonneg total)
    nlinarith
  calc
    ((2 * total + 1 : ℕ) : ℝ) *
        ((1 + C / (1 + C)) ^ total /
          (2 : ℝ) ^
            thresholdedGrowthCut threshold shellGrowth48 j total) ≤
      ((2 * total + 1 : ℕ) : ℝ) *
        Real.exp (-sharpProductRate * (A : ℝ) -
          2 * sharpProductRate * (total : ℝ)) := by
      simpa only [A] using
        mul_le_mul_of_nonneg_left henvelope (Nat.cast_nonneg _)
    _ ≤ (sharpRankConstant *
        Real.exp (sharpProductRate * (total : ℝ))) *
          Real.exp (-sharpProductRate * (A : ℝ) -
            2 * sharpProductRate * (total : ℝ)) :=
      mul_le_mul_of_nonneg_right hmult (Real.exp_pos _).le
    _ = sharpRankConstant * sharpInterfaceCost threshold j *
        (Real.exp (sharpProductRate * (total : ℝ)) *
          Real.exp (-2 * sharpProductRate * (total : ℝ))) := by
      unfold sharpInterfaceCost
      simp only [A]
      rw [show Real.exp (-sharpProductRate * (threshold (j + 1) + 1 : ℕ) -
          2 * sharpProductRate * (total : ℝ)) =
          Real.exp (-sharpProductRate * (threshold (j + 1) + 1 : ℕ)) *
            Real.exp (-2 * sharpProductRate * (total : ℝ)) by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring
    _ ≤ sharpRankConstant * sharpInterfaceCost threshold j * 1 :=
      mul_le_mul_of_nonneg_left hdecay
        (mul_nonneg sharpRankConstant_pos.le
          (sharpInterfaceCost_nonneg _ _))
    _ = sharpRankConstant * sharpInterfaceCost threshold j := by ring

end

end Erdos1165.HLOZSharpProductNumerics
