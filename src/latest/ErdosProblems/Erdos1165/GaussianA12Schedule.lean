/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.GaussianMultiBlockProfile

/-!
# An explicit late-block schedule for HLOZ (A.12)

The multiblock factorization is most economical when applied to one growing
block.  It starts at `n / 2`, ends at `n`, and has the largest convenient
integer radius below `n^(1+delta) / 16`.  The fixed factor `16` leaves enough
room to compare the radius with the envelope at the left endpoint.

The spectral cost of this schedule is at most
`1310720 * n^(1-2*delta)`.  Thus there is no connector cost and no logarithmic
loss in this implementation of (A.12).
-/

namespace Erdos1165.GaussianA12Schedule

noncomputable section

open GaussianSmallBall GaussianBlockFactorization GaussianMultiBlockProfile
  AppendixFirstMoment

/-- The left endpoint of the explicit late block. -/
def lateBlockStart (n : ℕ) : ℕ := n / 2

/-- Integer radius of the explicit late block. -/
def lateBlockRadius (n : ℕ) (delta : ℝ) : ℕ :=
  ⌊(n : ℝ) ^ (1 + delta) / 16⌋₊

/-- The explicit growing block occupying all scales from `n/2` through `n`. -/
def lateBlock (n : ℕ) (delta : ℝ) : GaussianBlock where
  start := lateBlockStart n
  steps := n - lateBlockStart n
  radius := lateBlockRadius n delta

/-- The explicit singleton consecutive-block schedule. -/
def lateBlockSchedule (n : ℕ) (delta : ℝ) : List GaussianBlock :=
  [lateBlock n delta]

@[simp] lemma lateBlock_start (n : ℕ) (delta : ℝ) :
    (lateBlock n delta).start = n / 2 := rfl

@[simp] lemma lateBlock_steps (n : ℕ) (delta : ℝ) :
    (lateBlock n delta).steps = n - n / 2 := rfl

@[simp] lemma lateBlock_radius (n : ℕ) (delta : ℝ) :
    (lateBlock n delta).radius = lateBlockRadius n delta := rfl

@[simp] lemma lateBlock_end (n : ℕ) (delta : ℝ) :
    (lateBlock n delta).start + (lateBlock n delta).steps = n := by
  simp only [lateBlock, lateBlockStart]
  omega

@[simp] lemma lateBlockSchedule_consecutive (n : ℕ) (delta : ℝ) :
    ConsecutiveBlocks (lateBlockSchedule n delta) := by
  simp [lateBlockSchedule, ConsecutiveBlocks]

@[simp] lemma lateBlockSchedule_end (n : ℕ) (delta : ℝ) :
    gaussianBlocksEnd (lateBlockSchedule n delta) = n := by
  change (lateBlock n delta).start + (lateBlock n delta).steps = n
  exact lateBlock_end n delta

lemma lateBlockStart_ge_two {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ lateBlockStart n := by
  unfold lateBlockStart
  omega

lemma quarter_le_lateBlockStart {n : ℕ} (hn : 4 ≤ n) :
    (n : ℝ) / 4 ≤ lateBlockStart n := by
  have hnat : n ≤ 4 * (n / 2) := by omega
  have hcast : (n : ℝ) ≤ 4 * (n / 2 : ℕ) := by exact_mod_cast hnat
  unfold lateBlockStart
  nlinarith

private lemma rpow_one_add_sq {x delta : ℝ} (hx : 0 < x) :
    (x ^ (1 + delta)) ^ 2 = x ^ (2 + 2 * delta) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx.le]
  congr 1
  ring

private lemma rpow_three_div_rpow_two_add {x delta : ℝ} (hx : 0 < x) :
    1280 * x * x ^ 2 / (x ^ (1 + delta) / 32) ^ 2 =
      1310720 * x ^ (1 - 2 * delta) := by
  rw [div_pow, rpow_one_add_sq hx]
  have hpow : 0 < x ^ (2 + 2 * delta) := Real.rpow_pos_of_pos hx _
  rw [div_eq_iff (div_pos hpow (by norm_num : (0 : ℝ) < 32 ^ 2)).ne']
  field_simp
  have hmul : x ^ (1 - 2 * delta) * x ^ (2 * (1 + delta)) = x ^ 3 := by
    rw [← Real.rpow_add hx]
    convert Real.rpow_natCast x 3 using 1 <;> ring_nf
  calc
    1280 * x ^ 3 * 32 ^ 2 = 1310720 * x ^ 3 := by ring
    _ = 1310720 *
        (x ^ (1 - 2 * delta) * x ^ (2 * (1 + delta))) := by rw [hmul]
    _ = 1310720 * x ^ (1 - 2 * delta) * x ^ (2 * (1 + delta)) := by ring

lemma lateBlockRadius_lower {n : ℕ} {delta : ℝ}
    (hn : 32 ≤ n) (hdelta : 0 ≤ delta) :
    (n : ℝ) ^ (1 + delta) / 32 ≤ lateBlockRadius n delta := by
  let y : ℝ := (n : ℝ) ^ (1 + delta) / 16
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ (1 + delta) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnOne (by linarith : (1 : ℝ) ≤ 1 + delta)
  have hyTwo : 2 ≤ y := by
    dsimp only [y]
    have hnReal : (32 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hfloor := Nat.lt_floor_add_one y
  have hfloorOneNat : 1 ≤ ⌊y⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hfloorOne : (1 : ℝ) ≤ (⌊y⌋₊ : ℕ) := by exact_mod_cast hfloorOneNat
  have hy : y / 2 ≤ (⌊y⌋₊ : ℕ) := by linarith
  change (n : ℝ) ^ (1 + delta) / 32 ≤
    (⌊(n : ℝ) ^ (1 + delta) / 16⌋₊ : ℕ)
  convert hy using 1 <;> simp only [y] <;> ring

lemma lateBlockRadius_le_power {n : ℕ} {delta : ℝ}
    (hdelta : 0 ≤ delta) :
    (lateBlockRadius n delta : ℝ) ≤ (n : ℝ) ^ (1 + delta) / 16 := by
  exact Nat.floor_le (by positivity)

/-- The radius fits in the `l^(1+delta)` envelope everywhere in the late
block. -/
lemma lateBlock_radius_le_envelope {n l : ℕ} {delta : ℝ}
    (hn : 4 ≤ n) (hdelta : 0 ≤ delta) (hdeltaOne : delta ≤ 1)
    (hl : BlockContains (lateBlock n delta) l) :
    (lateBlock n delta).radius ≤ (l : ℝ) ^ (1 + delta) := by
  have halpha0 : 0 ≤ 1 + delta := by linarith
  have halpha2 : 1 + delta ≤ 2 := by linarith
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hquarter : (n : ℝ) / 4 ≤ (lateBlockStart n : ℝ) :=
    quarter_le_lateBlockStart hn
  have hstartlNat : lateBlockStart n ≤ l := hl.1
  have hstartl : (lateBlockStart n : ℝ) ≤ l := by exact_mod_cast hstartlNat
  have hbase : (n : ℝ) / 4 ≤ l := hquarter.trans hstartl
  have hmono := Real.rpow_le_rpow (by positivity) hbase halpha0
  have hfour : (4 : ℝ) ^ (1 + delta) ≤ 16 := by
    calc
      (4 : ℝ) ^ (1 + delta) ≤ (4 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) halpha2
      _ = 16 := by norm_num [Real.rpow_two]
  calc
    ((lateBlock n delta).radius : ℝ) ≤
        (n : ℝ) ^ (1 + delta) / 16 := lateBlockRadius_le_power hdelta
    _ ≤ (n : ℝ) ^ (1 + delta) / (4 : ℝ) ^ (1 + delta) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hn0 _) (by positivity) hfour
    _ = ((n : ℝ) / 4) ^ (1 + delta) := by
      rw [Real.div_rpow hn0 (by norm_num : (0 : ℝ) ≤ 4)]
    _ ≤ (l : ℝ) ^ (1 + delta) := hmono

/-- The late-block radius is also below the parabolic profile centre. -/
lemma lateBlock_radius_le_center {n l : ℕ} {delta : ℝ}
    (hn : 4 ≤ n) (hdelta : 0 ≤ delta) (hdeltaOne : delta ≤ 1)
    (hl : BlockContains (lateBlock n delta) l) :
    (lateBlock n delta).radius ≤ profileCenter l := by
  have hw := lateBlock_radius_le_envelope hn hdelta hdeltaOne hl
  have hs := lateBlockStart_ge_two hn
  have hsl : lateBlockStart n ≤ l := hl.1
  have hlNat : 1 ≤ l := by omega
  have hlOne : (1 : ℝ) ≤ l := by exact_mod_cast hlNat
  have hp : (l : ℝ) ^ (1 + delta) ≤ (l : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlOne (by linarith)
  rw [Real.rpow_two] at hp
  have hr : ((lateBlock n delta).radius : ℝ) ≤
      ((profileCenter l : ℕ) : ℝ) := by
    rw [show ((profileCenter l : ℕ) : ℝ) = 2 * (l : ℝ) ^ 2 by
      simp [profileCenter]]
    nlinarith [sq_nonneg (l : ℝ)]
  exact_mod_cast hr

/-- A simple explicit large-`n` condition implies the scale hypothesis of
the killed-lattice Gaussian estimate. -/
lemma lateBlock_scale {n : ℕ} {delta : ℝ}
    (hn : 32 ≤ n) (hdelta : 0 ≤ delta)
    (hlarge : (2560 * 1024 : ℝ) ≤ (n : ℝ) ^ (2 * delta)) :
    (2560 : ℝ) * ((lateBlock n delta).start +
        (lateBlock n delta).steps : ℕ) ^ 2 ≤
      ((lateBlock n delta).radius : ℝ) ^ 2 := by
  rw [lateBlock_end]
  have hnpos : (0 : ℝ) < n := by positivity
  have hR := lateBlockRadius_lower hn hdelta
  have hRnonneg : 0 ≤ ((lateBlock n delta).radius : ℝ) := by positivity
  have hRsq : ((n : ℝ) ^ (1 + delta) / 32) ^ 2 ≤
      ((lateBlock n delta).radius : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hR 2
  have hpow : ((n : ℝ) ^ (1 + delta) / 32) ^ 2 =
      (n : ℝ) ^ 2 * (n : ℝ) ^ (2 * delta) / 1024 := by
    rw [div_pow, rpow_one_add_sq hnpos]
    rw [show 2 + 2 * delta = 2 + (2 * delta) by ring,
      Real.rpow_add hnpos, Real.rpow_two]
    norm_num
  rw [hpow] at hRsq
  calc
    (2560 : ℝ) * (n : ℝ) ^ 2 ≤
        (n : ℝ) ^ 2 * (n : ℝ) ^ (2 * delta) / 1024 := by
      nlinarith [sq_nonneg (n : ℝ)]
    _ ≤ ((lateBlock n delta).radius : ℝ) ^ 2 := hRsq

/-- Exact polynomial/rpow upper bound for the complete cost of the explicit
schedule.  Since the schedule is a singleton, the total cost is purely the
spectral cost. -/
theorem lateBlockSchedule_totalCost_le {n : ℕ} {delta : ℝ}
    (hn : 32 ≤ n) (hdelta : 0 ≤ delta) :
    gaussianBlockTotalCost (lateBlockSchedule n delta) ≤
      1310720 * (n : ℝ) ^ (1 - 2 * delta) := by
  simp only [lateBlockSchedule, gaussianBlockTotalCost,
    gaussianBlockSpectralCost, lateBlock_end]
  have hnpos : (0 : ℝ) < n := by positivity
  have hR := lateBlockRadius_lower hn hdelta
  have hRpos : 0 < ((lateBlock n delta).radius : ℝ) :=
    lt_of_lt_of_le (by positivity) hR
  have hsteps : (((lateBlock n delta).steps : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n (lateBlockStart n)
  have hnum :
      1280 * (((lateBlock n delta).steps : ℕ) : ℝ) * (n : ℝ) ^ 2 ≤
        1280 * (n : ℝ) * (n : ℝ) ^ 2 := by
    gcongr
  have hden : ((n : ℝ) ^ (1 + delta) / 32) ^ 2 ≤
      ((lateBlock n delta).radius : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hR 2
  calc
    1280 * (((lateBlock n delta).steps : ℕ) : ℝ) * (n : ℝ) ^ 2 /
          ((lateBlock n delta).radius : ℝ) ^ 2 ≤
        1280 * (n : ℝ) * (n : ℝ) ^ 2 /
          ((n : ℝ) ^ (1 + delta) / 32) ^ 2 := by
      exact div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 1310720 * (n : ℝ) ^ (1 - 2 * delta) :=
      rpow_three_div_rpow_two_add hnpos

/-- Fully instantiated finite A.12 for the explicit late-block schedule. -/
theorem lateBlock_exp_cost_le_constrainedGaussianDeviationWeight
    {n : ℕ} {delta : ℝ}
    (hn : 32 ≤ n) (hdelta : 0 ≤ delta) (hdeltaOne : delta ≤ 1)
    (hlarge : (2560 * 1024 : ℝ) ≤ (n : ℝ) ^ (2 * delta)) :
    gaussianCenteredPrefixProduct (lateBlockStart n) *
        Real.exp (-gaussianBlockTotalCost (lateBlockSchedule n delta)) ≤
      constrainedGaussianDeviationWeight n delta := by
  have hn2 : 2 ≤ n := by omega
  apply prefix_mul_exp_neg_totalCost_le_constrainedGaussianDeviationWeight
    hn2 (lateBlockStart_ge_two (by omega))
    (lateBlockSchedule_consecutive n delta)
    (lateBlockSchedule_end n delta)
  · intro c hc
    simp only [lateBlockSchedule, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    simp only [lateBlock_start]
    omega
  · intro c hc
    simp only [lateBlockSchedule, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    exact lateBlock_scale hn hdelta hlarge
  · intro c hc l hl
    simp only [lateBlockSchedule, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    exact lateBlock_radius_le_center (by omega) hdelta hdeltaOne hl
  · intro c hc l hl
    simp only [lateBlockSchedule, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst c
    exact lateBlock_radius_le_envelope (by omega) hdelta hdeltaOne hl

/-- Exponent-only form of the explicit A.12 lower bound. -/
theorem lateBlock_rpow_exp_le_constrainedGaussianDeviationWeight
    {n : ℕ} {delta : ℝ}
    (hn : 32 ≤ n) (hdelta : 0 ≤ delta) (hdeltaOne : delta ≤ 1)
    (hlarge : (2560 * 1024 : ℝ) ≤ (n : ℝ) ^ (2 * delta)) :
    gaussianCenteredPrefixProduct (lateBlockStart n) *
        Real.exp (-(1310720 * (n : ℝ) ^ (1 - 2 * delta))) ≤
      constrainedGaussianDeviationWeight n delta := by
  apply le_trans ?_ (lateBlock_exp_cost_le_constrainedGaussianDeviationWeight
    hn hdelta hdeltaOne hlarge)
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (neg_le_neg (lateBlockSchedule_totalCost_le hn hdelta)))
    (gaussianCenteredPrefixProduct_nonneg (lateBlockStart n))

end

end Erdos1165.GaussianA12Schedule
