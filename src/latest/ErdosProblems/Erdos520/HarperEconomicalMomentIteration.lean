import ErdosProblems.Erdos520.HarperDirectMomentRecursion
import ErdosProblems.Erdos520.HarperEconomicalScaleComparison
import Mathlib.Analysis.SpecificLimits.Normed

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos
namespace Problem520

/-!
# Numerical endpoints for the economical Harper iteration

The direct fractional-moment recursion may be stopped at any depth for which
`(1-q_L) * N <= 2`.  In the applications `N` is the square root of a
positive natural path length.  Taking the path length itself as the stopping
depth is deliberately wasteful but completely uniform, and avoids adding a
second logarithmic scheduling parameter.
-/

/-- Along Harper's exponent ladder, a nonnegative scalar power is bounded
uniformly by the sum of its initial `2/3` power and its first power.  This
form retains small volume factors while remaining linear for large entropy
factors. -/
theorem rpow_le_rpow_twoThird_add_self
    {z q : ℝ} (hz : 0 ≤ z)
    (hqLower : harperTwoThird ≤ q) (hqUpper : q ≤ 1) :
    z ^ q ≤ z ^ harperTwoThird + z := by
  rcases hz.eq_or_lt with rfl | hzPos
  · have htwo : 0 < harperTwoThird := by norm_num [harperTwoThird]
    have hq : 0 < q := htwo.trans_le hqLower
    simp [Real.zero_rpow hq.ne', Real.zero_rpow htwo.ne']
  by_cases hzOne : z ≤ 1
  · have hpow : z ^ q ≤ z ^ harperTwoThird :=
      Real.rpow_le_rpow_of_exponent_ge hzPos hzOne hqLower
    exact hpow.trans (le_add_of_nonneg_right hz)
  · have hzGe : 1 ≤ z := le_of_not_ge hzOne
    have hpow : z ^ q ≤ z ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hzGe hqUpper
    rw [Real.rpow_one] at hpow
    exact hpow.trans (le_add_of_nonneg_left (Real.rpow_nonneg hz _))

/-- A positive natural path length is always a valid stopping depth for the
dyadic moment iteration at square-root scale. -/
theorem harperDyadicMomentGap_mul_sqrt_nat_le_two_at_length
    {n : ℕ} (hn : 1 ≤ n) :
    harperDyadicMomentGap n * Real.sqrt (n : ℝ) ≤ 2 := by
  rw [harperDyadic_paper_stop_iff]
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith
  have hpowNat : n ≤ 2 ^ n := harper_self_le_two_pow n
  have hpowReal : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast hpowNat
  calc
    Real.sqrt (n : ℝ) / 6 ≤ (n : ℝ) := by nlinarith
    _ ≤ (2 : ℝ) ^ n := hpowReal

/-- The initial dyadic weight at an economical path is bounded by the target
negative one-third power of any positive scale controlled by four times that
path. -/
theorem harperDyadicMomentWeight_sqrt_nat_initial_le_of_scale
    {scale : ℝ} {n : ℕ}
    (hscale : 0 < scale) (hn : 1 ≤ n)
    (hcompare : scale ≤ 4 * (n : ℝ)) :
    harperDyadicMomentWeight (Real.sqrt (n : ℝ)) 0 ≤
      (3 : ℝ) ^ (2 / 3 : ℝ) * 4 ^ ((1 : ℝ) / 3) *
        scale ^ (-(1 : ℝ) / 3) := by
  have hnPos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  rw [harperDyadicMomentWeight_sqrt_initial hnPos]
  have hpath := rpow_neg_one_third_le_of_scale_le_four_mul_path
    hscale hnPos hcompare
  calc
    (3 : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 3) ≤
        (3 : ℝ) ^ (2 / 3 : ℝ) *
          (4 ^ ((1 : ℝ) / 3) * scale ^ (-(1 : ℝ) / 3)) :=
      mul_le_mul_of_nonneg_left hpath (by positivity)
    _ = (3 : ℝ) ^ (2 / 3 : ℝ) * 4 ^ ((1 : ℝ) / 3) *
        scale ^ (-(1 : ℝ) / 3) := by ring

/-- A `2/3`-power truncation tail at a positive natural path length is
stronger than the target negative one-third power of any scale controlled
by four times that path. -/
theorem rpow_div_nat_twoThird_le_of_scale_le_four_mul
    {A scale : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hscale : 0 < scale) (hn : 1 ≤ n)
    (hcompare : scale ≤ 4 * (n : ℝ)) :
    (A / (n : ℝ)) ^ harperTwoThird ≤
      A ^ harperTwoThird * 4 ^ ((1 : ℝ) / 3) *
        scale ^ (-(1 : ℝ) / 3) := by
  have hnPos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpowCompare :
      (n : ℝ) ^ (-(2 : ℝ) / 3) ≤
        (n : ℝ) ^ (-(1 : ℝ) / 3) := by
    exact Real.rpow_le_rpow_of_exponent_le hnOne (by norm_num)
  have hscalePow := rpow_neg_one_third_le_of_scale_le_four_mul_path
    hscale hnPos hcompare
  have hdenPowPos : 0 < (n : ℝ) ^ harperTwoThird :=
    Real.rpow_pos_of_pos hnPos _
  rw [Real.div_rpow hA (Nat.cast_nonneg n) harperTwoThird]
  calc
    A ^ harperTwoThird / (n : ℝ) ^ harperTwoThird =
        A ^ harperTwoThird * (n : ℝ) ^ (-(2 : ℝ) / 3) := by
      rw [harperTwoThird, div_eq_mul_inv,
        ← Real.rpow_neg hnPos.le]
      ring_nf
    _ ≤ A ^ harperTwoThird * (n : ℝ) ^ (-(1 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_left hpowCompare (Real.rpow_nonneg hA _)
    _ ≤ A ^ harperTwoThird *
        (4 ^ ((1 : ℝ) / 3) * scale ^ (-(1 : ℝ) / 3)) :=
      mul_le_mul_of_nonneg_left hscalePow (Real.rpow_nonneg hA _)
    _ = A ^ harperTwoThird * 4 ^ ((1 : ℝ) / 3) *
        scale ^ (-(1 : ℝ) / 3) := by ring

/-- Factor-parametric form of the preceding tail conversion. -/
theorem rpow_div_nat_twoThird_le_of_scale_le_mul
    {A scale factor : ℝ} {n : ℕ}
    (hA : 0 ≤ A) (hscale : 0 < scale) (hfactor : 0 < factor)
    (hn : 1 ≤ n) (hcompare : scale ≤ factor * (n : ℝ)) :
    (A / (n : ℝ)) ^ harperTwoThird ≤
      A ^ harperTwoThird * factor ^ ((1 : ℝ) / 3) *
        scale ^ (-(1 : ℝ) / 3) := by
  have hnPos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpowCompare :
      (n : ℝ) ^ (-(2 : ℝ) / 3) ≤
        (n : ℝ) ^ (-(1 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_exponent_le hnOne (by norm_num)
  have hquotient : scale / factor ≤ (n : ℝ) := by
    exact (div_le_iff₀ hfactor).2 (by simpa [mul_comm] using! hcompare)
  have hquotientPos : 0 < scale / factor := div_pos hscale hfactor
  have hmono :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (show (-(1 : ℝ) / 3) ≤ 0 by norm_num)
  have hscalePow :
      (n : ℝ) ^ (-(1 : ℝ) / 3) ≤
        factor ^ ((1 : ℝ) / 3) *
          scale ^ (-(1 : ℝ) / 3) := by
    calc
      (n : ℝ) ^ (-(1 : ℝ) / 3) ≤
          (scale / factor) ^ (-(1 : ℝ) / 3) :=
        hmono hquotientPos hnPos hquotient
      _ = scale ^ (-(1 : ℝ) / 3) /
          factor ^ (-(1 : ℝ) / 3) := by
        rw [Real.div_rpow hscale.le hfactor.le]
      _ = factor ^ ((1 : ℝ) / 3) *
          scale ^ (-(1 : ℝ) / 3) := by
        rw [show (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) by ring,
          Real.rpow_neg hfactor.le, div_eq_mul_inv, inv_inv]
        ring
  rw [Real.div_rpow hA (Nat.cast_nonneg n) harperTwoThird]
  calc
    A ^ harperTwoThird / (n : ℝ) ^ harperTwoThird =
        A ^ harperTwoThird * (n : ℝ) ^ (-(2 : ℝ) / 3) := by
      rw [harperTwoThird, div_eq_mul_inv,
        ← Real.rpow_neg hnPos.le]
      ring_nf
    _ ≤ A ^ harperTwoThird * (n : ℝ) ^ (-(1 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_left hpowCompare (Real.rpow_nonneg hA _)
    _ ≤ A ^ harperTwoThird *
        (factor ^ ((1 : ℝ) / 3) *
          scale ^ (-(1 : ℝ) / 3)) :=
      mul_le_mul_of_nonneg_left hscalePow (Real.rpow_nonneg hA _)
    _ = A ^ harperTwoThird * factor ^ ((1 : ℝ) / 3) *
        scale ^ (-(1 : ℝ) / 3) := by ring

/-! ## Summable terminal budgets for the shrinking central bands -/

/-- The generic budget left by a central band after the direct moment
iteration.  Its dyadic volume is retained both in the good-event term and
in the terminal first-moment term. -/
noncomputable def harperCentralDyadicBudgetTerm
    (a b : ℝ) (d : ℕ) : ℝ :=
  let z := (1 / 2 : ℝ) ^ (d + 2) * (a * ((d : ℝ) + 1) + b)
  z ^ harperTwoThird + z

private theorem summable_geometric_shift_two
    {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun d : ℕ ↦ r ^ (d + 2)) := by
  have h := summable_geometric_of_norm_lt_one hr
  exact (summable_nat_add_iff (f := fun d : ℕ ↦ r ^ d) 2).2 h

private theorem summable_natCast_succ_mul_geometric_shift_two
    {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun d : ℕ ↦ ((d : ℝ) + 1) * r ^ (d + 2)) := by
  have hpow : Summable (fun d : ℕ ↦ (d : ℝ) ^ 1 * r ^ d) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hgeom : Summable (fun d : ℕ ↦ r ^ d) :=
    summable_geometric_of_norm_lt_one hr
  have h := (hpow.add hgeom).mul_left (r ^ 2)
  refine h.congr ?_
  intro d
  simp only [pow_one, pow_add]
  ring

/-- Dyadic volume to the `2/3` power is a geometric sequence. -/
private theorem summable_harperCentralDyadicVolume_twoThird :
    Summable (fun d : ℕ ↦
      ((1 / 2 : ℝ) ^ (d + 2)) ^ harperTwoThird) := by
  have hbase0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have htwo : 0 < harperTwoThird := by norm_num [harperTwoThird]
  have hrPos : 0 < (1 / 2 : ℝ) ^ harperTwoThird :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrLt : ‖(1 / 2 : ℝ) ^ harperTwoThird‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hrPos]
    exact Real.rpow_lt_one hbase0 (by norm_num) htwo
  have hshift := summable_geometric_shift_two hrLt
  refine hshift.congr ?_
  intro d
  exact Real.rpow_pow_comm hbase0 harperTwoThird (d + 2)

/-- The same geometric sequence remains summable after one affine factor in
the dyadic depth. -/
private theorem summable_harperCentralDyadicVolume_twoThird_mul_depth :
    Summable (fun d : ℕ ↦
      ((d : ℝ) + 1) *
        ((1 / 2 : ℝ) ^ (d + 2)) ^ harperTwoThird) := by
  have hbase0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have htwo : 0 < harperTwoThird := by norm_num [harperTwoThird]
  have hrPos : 0 < (1 / 2 : ℝ) ^ harperTwoThird :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hrLt : ‖(1 / 2 : ℝ) ^ harperTwoThird‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hrPos]
    exact Real.rpow_lt_one hbase0 (by norm_num) htwo
  have hshift :=
    summable_natCast_succ_mul_geometric_shift_two hrLt
  refine hshift.congr ?_
  intro d
  rw [Real.rpow_pow_comm hbase0 harperTwoThird (d + 2)]

/-- The complete central-band budget is summable for every fixed
nonnegative affine entropy envelope. -/
theorem summable_harperCentralDyadicBudgetTerm
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Summable (harperCentralDyadicBudgetTerm a b) := by
  let volume : ℕ → ℝ := fun d ↦ (1 / 2 : ℝ) ^ (d + 2)
  let loss : ℕ → ℝ := fun d ↦ a * ((d : ℝ) + 1) + b
  have hvolume0 (d : ℕ) : 0 ≤ volume d := by
    dsimp only [volume]
    positivity
  have hloss0 (d : ℕ) : 0 ≤ loss d := by
    dsimp only [loss]
    positivity
  have hvolumePow := summable_harperCentralDyadicVolume_twoThird
  have hvolumePowDepth :=
    summable_harperCentralDyadicVolume_twoThird_mul_depth
  have hmajorPow : Summable (fun d : ℕ ↦
      volume d ^ harperTwoThird * (1 + loss d)) := by
    have hdepth := hvolumePowDepth.mul_left a
    have hconstant := hvolumePow.mul_left (1 + b)
    refine (hdepth.add hconstant).congr ?_
    intro d
    dsimp only [volume, loss]
    ring
  have hhalf : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have hvolume := summable_geometric_shift_two hhalf
  have hvolumeDepth :=
    summable_natCast_succ_mul_geometric_shift_two hhalf
  have hmajorLinear : Summable (fun d : ℕ ↦
      volume d * loss d) := by
    have hdepth := hvolumeDepth.mul_left a
    have hconstant := hvolume.mul_left b
    refine (hdepth.add hconstant).congr ?_
    intro d
    dsimp only [volume, loss]
    ring
  have hmajor := hmajorPow.add hmajorLinear
  apply Summable.of_nonneg_of_le
    (fun d ↦ add_nonneg
      (Real.rpow_nonneg (mul_nonneg (hvolume0 d) (hloss0 d)) _)
      (mul_nonneg (hvolume0 d) (hloss0 d)))
  · intro d
    have hlossPow : loss d ^ harperTwoThird ≤ 1 + loss d :=
      rpow_le_one_add_self (hloss0 d)
        (by norm_num [harperTwoThird]) (by norm_num [harperTwoThird])
    have hmul :
        (volume d * loss d) ^ harperTwoThird =
          volume d ^ harperTwoThird * loss d ^ harperTwoThird :=
      Real.mul_rpow (hvolume0 d) (hloss0 d)
    change (volume d * loss d) ^ harperTwoThird + volume d * loss d ≤
      volume d ^ harperTwoThird * (1 + loss d) + volume d * loss d
    rw [hmul]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hlossPow
        (Real.rpow_nonneg (by positivity) _)) le_rfl
  · exact hmajor

/-- Uniform finite-sum form of central-band summability, ready for the exact
dyadic decomposition. -/
theorem exists_pos_bound_finset_sum_harperCentralDyadicBudgetTerm
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ,
      (∑ d ∈ Finset.range m, harperCentralDyadicBudgetTerm a b d) ≤ K := by
  let K : ℝ := 1 + ∑' d : ℕ, harperCentralDyadicBudgetTerm a b d
  have hterm0 (d : ℕ) : 0 ≤ harperCentralDyadicBudgetTerm a b d := by
    unfold harperCentralDyadicBudgetTerm
    exact add_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
  have hsum := summable_harperCentralDyadicBudgetTerm ha hb
  have htsum0 : 0 ≤ ∑' d : ℕ, harperCentralDyadicBudgetTerm a b d :=
    tsum_nonneg hterm0
  refine ⟨K, by dsimp only [K]; linarith, ?_⟩
  intro m
  have hpartial :
      (∑ d ∈ Finset.range m, harperCentralDyadicBudgetTerm a b d) ≤
        ∑' d : ℕ, harperCentralDyadicBudgetTerm a b d :=
    Summable.sum_le_tsum (Finset.range m)
      (fun d hd ↦ hterm0 d) hsum
  dsimp only [K]
  linarith

end Problem520
end Erdos

#print axioms Erdos.Problem520.harperDyadicMomentGap_mul_sqrt_nat_le_two_at_length
#print axioms Erdos.Problem520.harperDyadicMomentWeight_sqrt_nat_initial_le_of_scale
#print axioms Erdos.Problem520.rpow_div_nat_twoThird_le_of_scale_le_four_mul
#print axioms Erdos.Problem520.rpow_div_nat_twoThird_le_of_scale_le_mul
#print axioms Erdos.Problem520.rpow_le_rpow_twoThird_add_self
#print axioms Erdos.Problem520.summable_harperCentralDyadicBudgetTerm
#print axioms Erdos.Problem520.exists_pos_bound_finset_sum_harperCentralDyadicBudgetTerm
