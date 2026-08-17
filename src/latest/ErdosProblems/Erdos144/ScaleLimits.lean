/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.Harmonic
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Asymptotics of the explicit harmonic scales for Erdős Problem 144

This file collects elementary growth estimates for the scales in
`Erdos144.Harmonic`.  Keeping them separate from the finite probability
model makes the analytic and prime-transfer files able to use the estimates
without unfolding the scale definitions repeatedly.
-/

open Filter Topology

namespace Erdos144.Harmonic

/-- The scale parameter is eventually positive. -/
theorem eventually_one_le_scaleParameter : ∀ᶠ s : ℕ in atTop, 1 ≤ s :=
  eventually_ge_atTop 1

/-- The auxiliary loss parameter tends to infinity. -/
theorem tendsto_xi_atTop : Tendsto xi atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (9 : ℕ)))
  filter_upwards with s
  simp [xi]

/-- The selected-cardinality cutoff tends to infinity. -/
theorem tendsto_cardinalCutoff_atTop : Tendsto cardinalCutoff atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_xi_atTop
  filter_upwards with s
  have hfac : 1 ≤ 20 * lowerExponent s + stageStride s * stageCount s + 1 := by omega
  simpa [cardinalCutoff] using Nat.mul_le_mul_left (xi s) hfac

/-- The real-valued selected-cardinality cutoff tends to infinity. -/
theorem tendsto_cardinalCutoff_natCast_atTop :
    Tendsto (fun s ↦ (cardinalCutoff s : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_cardinalCutoff_atTop

/-- The exponent defining the lower scale tends to infinity. -/
theorem tendsto_lowerExponent_atTop : Tendsto lowerExponent atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_id
  filter_upwards with s
  have hsq : 1 ≤ stageCount s ^ 2 := by
    exact Nat.one_le_pow 2 _ (stageCount_pos s)
  simpa [lowerExponent] using Nat.mul_le_mul_left s hsq

/-- The final eight-adic exponent is at most twenty-four times the lower
exponent. -/
theorem finalExponent_le_twenty_four_mul_lowerExponent (s : ℕ) :
    20 * lowerExponent s + stageStride s * stageCount s ≤
      24 * lowerExponent s := by
  have hJ : stageCount s ≤ stageCount s ^ 2 := by
    have hpos := stageCount_pos s
    nlinarith
  rw [lowerExponent, stageStride]
  calc
    20 * (s * stageCount s ^ 2) + (4 * s) * stageCount s ≤
        20 * (s * stageCount s ^ 2) + 4 * (s * stageCount s ^ 2) :=
      Nat.add_le_add_left (by
        calc
          (4 * s) * stageCount s ≤ (4 * s) * stageCount s ^ 2 :=
            Nat.mul_le_mul_left (4 * s) hJ
          _ = 4 * (s * stageCount s ^ 2) := by ring) _
    _ = 24 * (s * stageCount s ^ 2) := by ring

/-- A uniform polynomial upper bound for the selected-cardinality cutoff. -/
theorem cardinalCutoff_le_twenty_five_mul_lowerExponent_sq
    {s : ℕ} (hs : 1 ≤ s) :
    cardinalCutoff s ≤ 25 * lowerExponent s ^ 2 := by
  have hJ : stageCount s ≤ stageCount s ^ 2 := by
    have hpos := stageCount_pos s
    nlinarith
  have hLpos : 0 < lowerExponent s := by
    simp only [lowerExponent]
    exact Nat.mul_pos hs (pow_pos (stageCount_pos s) 2)
  have hxiJ : xi s ≤ stageCount s := by
    simp only [stageCount]
    exact le_self_pow₀ (xi_pos s) (by norm_num)
  have hxiL : xi s ≤ lowerExponent s := by
    calc
      xi s ≤ stageCount s := hxiJ
      _ ≤ stageCount s ^ 2 := hJ
      _ ≤ s * stageCount s ^ 2 := by
        simpa using Nat.mul_le_mul_right (stageCount s ^ 2) hs
      _ = lowerExponent s := by rw [lowerExponent]
  have hstride : stageStride s * stageCount s ≤ 4 * lowerExponent s := by
    rw [stageStride, lowerExponent]
    calc
      (4 * s) * stageCount s ≤ (4 * s) * stageCount s ^ 2 :=
        Nat.mul_le_mul_left (4 * s) hJ
      _ = 4 * (s * stageCount s ^ 2) := by ring
  have hfac :
      20 * lowerExponent s + stageStride s * stageCount s + 1 ≤
        25 * lowerExponent s := by omega
  calc
    cardinalCutoff s = xi s *
        (20 * lowerExponent s + stageStride s * stageCount s + 1) := rfl
    _ ≤ lowerExponent s * (25 * lowerExponent s) :=
      Nat.mul_le_mul hxiL hfac
    _ = 25 * lowerExponent s ^ 2 := by ring

/-- Every fixed power of the mesh is bounded by a fixed polynomial in the
lower exponent. -/
theorem transferMesh_pow_le_scaleMajorant (m : ℕ) {s : ℕ} (hs : 1 ≤ s) :
    transferMesh s ^ m ≤
      25 ^ (2 * m) * lowerExponent s ^ (4 * m) := by
  rw [transferMesh_eq, ← pow_mul]
  calc
    cardinalCutoff s ^ (2 * m) ≤
        (25 * lowerExponent s ^ 2) ^ (2 * m) :=
      Nat.pow_le_pow_left (cardinalCutoff_le_twenty_five_mul_lowerExponent_sq hs) _
    _ = 25 ^ (2 * m) * lowerExponent s ^ (4 * m) := by
      rw [mul_pow, ← pow_mul]
      congr 2
      omega

/-- Every fixed power of the transfer mesh is negligible compared with the
lower scale. -/
theorem tendsto_transferMesh_pow_div_lowerScale_zero (m : ℕ) :
    Tendsto (fun s ↦ (transferMesh s ^ m : ℝ) / lowerScale s)
      atTop (𝓝 0) := by
  have hmajor : Tendsto
      (fun s ↦ (25 : ℝ) ^ (2 * m) *
        ((lowerExponent s : ℝ) ^ (4 * m) / 8 ^ lowerExponent s))
      atTop (𝓝 0) := by
    simpa using ((tendsto_pow_const_div_const_pow_of_one_lt (4 * m)
      (by norm_num : (1 : ℝ) < 8)).comp tendsto_lowerExponent_atTop).const_mul
        ((25 : ℝ) ^ (2 * m))
  apply squeeze_zero' (g := fun s ↦ (25 : ℝ) ^ (2 * m) *
    ((lowerExponent s : ℝ) ^ (4 * m) / 8 ^ lowerExponent s))
  · exact Eventually.of_forall (fun s ↦ by positivity)
  · filter_upwards [eventually_one_le_scaleParameter] with s hs
    have hnat := transferMesh_pow_le_scaleMajorant m hs
    rw [lowerScale]
    push_cast
    rw [← mul_div_assoc]
    gcongr
    exact_mod_cast hnat
  · exact hmajor

/-- The mesh itself is negligible compared with the lower scale. -/
theorem tendsto_transferMesh_div_lowerScale_zero :
    Tendsto (fun s ↦ (transferMesh s : ℝ) / lowerScale s)
      atTop (𝓝 0) := by
  simpa using tendsto_transferMesh_pow_div_lowerScale_zero 1

/-- The reciprocal scale ratio tends to infinity. -/
theorem tendsto_lowerScale_div_transferMesh_atTop :
    Tendsto (fun s ↦ (lowerScale s : ℝ) / transferMesh s) atTop atTop := by
  have hpos : ∀ᶠ s : ℕ in atTop,
      0 < (transferMesh s : ℝ) / lowerScale s := by
    filter_upwards with s
    apply div_pos
    · exact_mod_cast (cardinalCutoff_pos s).trans
        (cardinalCutoff_lt_transferMesh s)
    · exact_mod_cast (by simp [lowerScale] : 0 < lowerScale s)
  have hwithin : Tendsto
      (fun s ↦ (transferMesh s : ℝ) / lowerScale s) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_transferMesh_div_lowerScale_zero, hpos⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  change Tendsto (fun s ↦ ((transferMesh s : ℝ) / lowerScale s)⁻¹)
    atTop atTop at hinv
  simpa only [inv_div] using hinv

/-- Exponentiating the reciprocal scale ratio still tends to infinity. -/
theorem tendsto_exp_lowerScale_div_transferMesh_atTop :
    Tendsto (fun s ↦ Real.exp ((lowerScale s : ℝ) / transferMesh s))
      atTop atTop :=
  Real.tendsto_exp_atTop.comp tendsto_lowerScale_div_transferMesh_atTop

/-- Every fixed natural endpoint threshold is eventually below the natural
floor of the exponential scale ratio. -/
theorem eventually_nat_le_floor_exp_lowerScale_div_transferMesh (X₀ : ℕ) :
    ∀ᶠ s : ℕ in atTop,
      X₀ ≤ ⌊Real.exp ((lowerScale s : ℝ) / transferMesh s)⌋₊ := by
  filter_upwards [tendsto_exp_lowerScale_div_transferMesh_atTop.eventually
    (eventually_ge_atTop (X₀ : ℝ))] with s hs
  exact Nat.le_floor hs

/-- The square of the lower exponent is no larger than the transfer mesh. -/
theorem lowerExponent_sq_le_transferMesh (s : ℕ) :
    lowerExponent s ^ 2 ≤ transferMesh s := by
  rw [transferMesh_eq]
  apply Nat.pow_le_pow_left _ 2
  have hxi : 1 ≤ xi s := xi_pos s
  have hfac : lowerExponent s ≤
      20 * lowerExponent s + stageStride s * stageCount s + 1 := by omega
  simpa [cardinalCutoff] using Nat.mul_le_mul hxi hfac

/-- The harmonic mass of the full reservoir is at most a fixed multiple of
the lower exponent. -/
theorem harmonicIntervalMass_le {s : ℕ} (hs : 1 ≤ s) :
    (∑ i ∈ Finset.Ioc (lowerScale s) (finalTop s), (1 : ℝ) / i) ≤
      169 * lowerExponent s := by
  have hsubset : Finset.Ioc (lowerScale s) (finalTop s) ⊆
      Finset.Icc 1 (finalTop s) := by
    intro i hi
    have hi' := Finset.mem_Ioc.mp hi
    exact Finset.mem_Icc.mpr ⟨by
      have hscale : 1 ≤ lowerScale s := by
        simp only [lowerScale]
        exact Nat.one_le_pow _ _ (by norm_num)
      omega, hi'.2⟩
  have hsum :
      (∑ i ∈ Finset.Ioc (lowerScale s) (finalTop s), (1 : ℝ) / i) ≤
        (harmonic (finalTop s) : ℝ) := by
    calc
      (∑ i ∈ Finset.Ioc (lowerScale s) (finalTop s), (1 : ℝ) / i) ≤
          ∑ i ∈ Finset.Icc 1 (finalTop s), (1 : ℝ) / i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
          intro i _ _
          positivity)
      _ = (harmonic (finalTop s) : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
          Rat.cast_natCast, one_div]
  have hharm : (harmonic (finalTop s) : ℝ) ≤
      1 + Real.log (finalTop s) := harmonic_le_one_add_log _
  have hlog8nonneg : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog8 : Real.log (8 : ℝ) ≤ 7 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    norm_num at h
    exact h
  have hexpR :
      (20 * lowerExponent s + stageStride s * stageCount s : ℝ) ≤
        24 * lowerExponent s := by
    exact_mod_cast finalExponent_le_twenty_four_mul_lowerExponent s
  have hlog : Real.log (finalTop s) ≤ 168 * lowerExponent s := by
    rw [finalTop, stageTop]
    push_cast
    rw [Real.log_pow]
    push_cast
    have hmul := mul_le_mul_of_nonneg_right hexpR hlog8nonneg
    have hmul8 := mul_le_mul_of_nonneg_left hlog8
      (by positivity : (0 : ℝ) ≤ 24 * lowerExponent s)
    nlinarith
  have hL : (1 : ℝ) ≤ lowerExponent s := by
    have hsquare : 1 ≤ stageCount s ^ 2 :=
      Nat.one_le_pow 2 _ (stageCount_pos s)
    have : 1 ≤ lowerExponent s := by
      simp only [lowerExponent]
      simpa using Nat.mul_le_mul hs hsquare
    exact_mod_cast this
  linarith

/-- The total harmonic mass of the reservoir, divided by the transfer mesh,
tends to zero. -/
theorem tendsto_harmonicIntervalMass_div_transferMesh_zero :
    Tendsto
      (fun s ↦
        (∑ i ∈ Finset.Ioc (lowerScale s) (finalTop s), (1 : ℝ) / i) /
          transferMesh s)
      atTop (𝓝 0) := by
  have hLreal : Tendsto (fun s ↦ (lowerExponent s : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_lowerExponent_atTop
  have hmajor : Tendsto (fun s ↦ (169 : ℝ) / lowerExponent s)
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hLreal
  apply squeeze_zero' (g := fun s ↦ (169 : ℝ) / lowerExponent s)
  · exact Eventually.of_forall (fun s ↦ div_nonneg (Finset.sum_nonneg fun _ _ ↦ by
      positivity) (by positivity))
  · filter_upwards [eventually_one_le_scaleParameter] with s hs
    have hmass := harmonicIntervalMass_le hs
    have hmesh := lowerExponent_sq_le_transferMesh s
    have hLpos : (0 : ℝ) < lowerExponent s := by
      exact_mod_cast (by
        simp only [lowerExponent]
        exact Nat.mul_pos hs (pow_pos (stageCount_pos s) 2))
    have hmeshR : (lowerExponent s : ℝ) ^ 2 ≤ transferMesh s := by
      exact_mod_cast hmesh
    calc
      (∑ i ∈ Finset.Ioc (lowerScale s) (finalTop s), (1 : ℝ) / i) /
          transferMesh s ≤ (169 * lowerExponent s) / transferMesh s := by
        gcongr
      _ ≤ (169 * lowerExponent s) / (lowerExponent s : ℝ) ^ 2 := by
        gcongr
      _ = 169 / lowerExponent s := by
        field_simp
  · exact hmajor

/-- Squaring the cutoff makes its relative mesh width exactly reciprocal
to the cutoff. -/
theorem two_mul_cardinalCutoff_div_transferMesh (s : ℕ) :
    (2 : ℝ) * cardinalCutoff s / transferMesh s =
      2 / cardinalCutoff s := by
  rw [transferMesh_eq]
  have hne : (cardinalCutoff s : ℝ) ≠ 0 := by
    exact_mod_cast (cardinalCutoff_pos s).ne'
  push_cast
  field_simp

/-- The relative width of a two-sided mesh window tends to zero. -/
theorem tendsto_two_mul_cardinalCutoff_div_transferMesh_zero :
    Tendsto (fun s ↦ (2 : ℝ) * cardinalCutoff s / transferMesh s)
      atTop (𝓝 0) := by
  have hdiv : Tendsto (fun s ↦ (2 : ℝ) / cardinalCutoff s) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_cardinalCutoff_natCast_atTop
  simpa only [two_mul_cardinalCutoff_div_transferMesh] using hdiv

/-- In particular the relative mesh width is eventually below `log 2`. -/
theorem eventually_two_mul_cardinalCutoff_div_transferMesh_lt_log_two :
    ∀ᶠ s : ℕ in atTop,
      (2 : ℝ) * cardinalCutoff s / transferMesh s < Real.log 2 := by
  exact (tendsto_order.1 tendsto_two_mul_cardinalCutoff_div_transferMesh_zero).2
    _ (Real.log_pos (by norm_num))

/-- The entire reservoir lies below the twenty-fourth power of its lower
scale. -/
theorem finalTop_le_lowerScale_pow_twenty_four (s : ℕ) :
    finalTop s ≤ lowerScale s ^ 24 := by
  rw [finalTop, stageTop, lowerScale, ← pow_mul]
  exact Nat.pow_le_pow_right (by norm_num)
    (by simpa [Nat.mul_comm] using
      finalExponent_le_twenty_four_mul_lowerExponent s)

/-- A twenty-fifth power of the relative mesh absorbs the length of the
entire reservoir.  This is the coarse endpoint-tail estimate used after
summing a uniform pointwise transfer error. -/
theorem tendsto_finalTop_mul_transferRatio_pow_twenty_five_zero :
    Tendsto
      (fun s ↦ (finalTop s : ℝ) *
        ((transferMesh s : ℝ) / lowerScale s) ^ 25)
      atTop (𝓝 0) := by
  have hmajor := tendsto_transferMesh_pow_div_lowerScale_zero 25
  apply squeeze_zero' (g := fun s ↦ (transferMesh s ^ 25 : ℝ) / lowerScale s)
  · exact Eventually.of_forall (fun s ↦ by positivity)
  · filter_upwards with s
    have htop : (finalTop s : ℝ) ≤ (lowerScale s : ℝ) ^ 24 := by
      exact_mod_cast finalTop_le_lowerScale_pow_twenty_four s
    have hC : (0 : ℝ) < lowerScale s := by
      exact_mod_cast (by simp [lowerScale] : 0 < lowerScale s)
    calc
      (finalTop s : ℝ) * ((transferMesh s : ℝ) / lowerScale s) ^ 25 =
          (finalTop s : ℝ) * (transferMesh s : ℝ) ^ 25 /
            (lowerScale s : ℝ) ^ 25 := by rw [div_pow, mul_div_assoc]
      _ ≤ (lowerScale s : ℝ) ^ 24 * (transferMesh s : ℝ) ^ 25 /
            (lowerScale s : ℝ) ^ 25 := by gcongr
      _ = (transferMesh s : ℝ) ^ 25 / lowerScale s := by
        field_simp
  · exact hmajor

/-- Every still higher fixed power of the relative mesh also absorbs the
length of the reservoir. -/
theorem tendsto_finalTop_mul_transferRatio_pow_zero (m : ℕ) (hm : 25 ≤ m) :
    Tendsto
      (fun s ↦ (finalTop s : ℝ) *
        ((transferMesh s : ℝ) / lowerScale s) ^ m)
      atTop (𝓝 0) := by
  have hratio : ∀ᶠ s : ℕ in atTop,
      (transferMesh s : ℝ) / lowerScale s ≤ 1 := by
    exact ((tendsto_order.1 tendsto_transferMesh_div_lowerScale_zero).2
      1 (by norm_num)).mono fun _ h ↦ h.le
  apply squeeze_zero'
    (g := fun s ↦ (finalTop s : ℝ) *
      ((transferMesh s : ℝ) / lowerScale s) ^ 25)
  · exact Eventually.of_forall (fun s ↦ by positivity)
  · filter_upwards [hratio] with s hs
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (by positivity) hs hm) (by positivity)
  · exact tendsto_finalTop_mul_transferRatio_pow_twenty_five_zero

end Erdos144.Harmonic
