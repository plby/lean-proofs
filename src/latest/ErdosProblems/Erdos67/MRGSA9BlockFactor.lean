import ErdosProblems.Erdos67.MRGSExponentialCosine
import ErdosProblems.Erdos67.MRHalaszBandLocalMass

/-!
# The prime-block factor in the GS A.9 argument

This packages the exact consequence of source inequality (A.12) used in
equation (A.11): the hyperbolic-sine factor of a complex block sum is
cancelled by the exponential of its absolute reciprocal mass.
-/

namespace Erdos67

noncomputable section

/-- The linear prime sum over one A.9 deletion block. -/
def gsA9PrimeBlockSum
    (f : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P]
    (N : ℕ) (sigma t : ℝ) : ℂ :=
  ∑ p ∈ primesUpTo N with P p,
    f p * (p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))

/-- Its absolute reciprocal mass on the same vertical line. -/
def gsA9PrimeBlockRadius
    (P : ℕ → Prop) [DecidablePred P] (N : ℕ) (sigma : ℝ) : ℝ :=
  ∑ p ∈ primesUpTo N with P p, (p : ℝ) ^ (-sigma)

/-- A complex hyperbolic-sine difference is bounded by the radial
exponential. -/
theorem norm_exp_half_sub_exp_neg_half_le_exp_sqrt (a t : ℝ) :
    ‖Complex.exp (((a : ℂ) + Complex.I * (t : ℂ)) / 2) -
        Complex.exp (-(((a : ℂ) + Complex.I * (t : ℂ)) / 2))‖ ≤
      Real.exp (Real.sqrt (a ^ 2 + t ^ 2) / 2) := by
  have hnonneg (b s : ℝ) (hb : 0 ≤ b) :
      ‖Complex.exp (((b : ℂ) + Complex.I * (s : ℂ)) / 2) -
          Complex.exp (-(((b : ℂ) + Complex.I * (s : ℂ)) / 2))‖ ≤
        Real.exp (Real.sqrt (b ^ 2 + s ^ 2) / 2) := by
    let z : ℂ := (b : ℂ) + Complex.I * (s : ℂ)
    have hfactor :
        Complex.exp (z / 2) - Complex.exp (-(z / 2)) =
          Complex.exp (z / 2) * (1 - Complex.exp (-z)) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 1
      ring_nf
    have hneg :
        -z = ((-b : ℝ) : ℂ) + Complex.I * ((-s : ℝ) : ℂ) := by
      dsimp only [z]
      push_cast
      ring_nf
    have hone := norm_one_sub_exp_neg_add_mul_I_le b (-s) hb
    have hone' :
        ‖1 - Complex.exp (-z)‖ ≤
          Real.exp ((-b + Real.sqrt (b ^ 2 + (-s) ^ 2)) / 2) := by
      rw [hneg]
      simpa only [Complex.ofReal_neg] using hone
    rw [hfactor, norm_mul, Complex.norm_exp]
    have hre : (z / 2).re = b / 2 := by
      dsimp only [z]
      simp
    rw [hre]
    calc
      Real.exp (b / 2) * ‖1 - Complex.exp (-z)‖ ≤
          Real.exp (b / 2) *
            Real.exp ((-b + Real.sqrt (b ^ 2 + (-s) ^ 2)) / 2) :=
        mul_le_mul_of_nonneg_left hone' (Real.exp_pos _).le
      _ = Real.exp (Real.sqrt (b ^ 2 + s ^ 2) / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
  by_cases ha : 0 ≤ a
  · exact hnonneg a t ha
  · have ha' : 0 ≤ -a := neg_nonneg.mpr (le_of_not_ge ha)
    have h := hnonneg (-a) (-t) ha'
    have harg :
        (((-a : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) =
          -((a : ℂ) + Complex.I * (t : ℂ)) := by
      push_cast
      ring_nf
    rw [harg, neg_div, neg_neg, norm_sub_rev] at h
    simpa only [neg_sq] using h

/-- Source equation (A.11), in abstract block-sum form. -/
theorem norm_exp_half_sub_exp_neg_half_mul_exp_neg_le_one
    (a t R : ℝ) (hR : Real.sqrt (a ^ 2 + t ^ 2) ≤ R) :
    ‖Complex.exp (((a : ℂ) + Complex.I * (t : ℂ)) / 2) -
        Complex.exp (-(((a : ℂ) + Complex.I * (t : ℂ)) / 2))‖ *
          Real.exp (-R / 2) ≤ 1 := by
  have hmain := norm_exp_half_sub_exp_neg_half_le_exp_sqrt a t
  calc
    ‖Complex.exp (((a : ℂ) + Complex.I * (t : ℂ)) / 2) -
        Complex.exp (-(((a : ℂ) + Complex.I * (t : ℂ)) / 2))‖ *
          Real.exp (-R / 2) ≤
      Real.exp (Real.sqrt (a ^ 2 + t ^ 2) / 2) *
          Real.exp (-R / 2) :=
      mul_le_mul_of_nonneg_right hmain (Real.exp_pos _).le
    _ = Real.exp ((Real.sqrt (a ^ 2 + t ^ 2) - R) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)

/-- Coordinate-free form of the A.11 block estimate. -/
theorem norm_exp_half_sub_exp_neg_half_mul_exp_neg_le_one_of_norm
    (z : ℂ) (R : ℝ) (hz : ‖z‖ ≤ R) :
    ‖Complex.exp (z / 2) - Complex.exp (-(z / 2))‖ *
        Real.exp (-R / 2) ≤ 1 := by
  have hcoords : ((z.re : ℂ) + Complex.I * (z.im : ℂ)) = z := by
    apply Complex.ext <;> simp
  have hradius : Real.sqrt (z.re ^ 2 + z.im ^ 2) ≤ R := by
    calc
      Real.sqrt (z.re ^ 2 + z.im ^ 2) = ‖z‖ := by
        rw [Complex.norm_def, Complex.normSq_apply]
        congr 1
        ring
      _ ≤ R := hz
  simpa only [hcoords] using
    norm_exp_half_sub_exp_neg_half_mul_exp_neg_le_one z.re z.im R hradius

/-- Triangle inequality for the actual prime-block linear form. -/
theorem norm_gsA9PrimeBlockSum_le_radius
    {f : ℕ → ℂ} (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P]
    (N : ℕ) (sigma t : ℝ) :
    ‖gsA9PrimeBlockSum f P N sigma t‖ ≤
      gsA9PrimeBlockRadius P N sigma := by
  unfold gsA9PrimeBlockSum gsA9PrimeBlockRadius
  calc
    ‖∑ p ∈ primesUpTo N with P p,
        f p * (p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      ∑ p ∈ primesUpTo N with P p,
        ‖f p * (p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ primesUpTo N with P p,
        (p : ℝ) ^ (-sigma) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpprime := (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
      rw [norm_mul,
        HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul hpprime.pos]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg p) _)
        (hbound p)

/-- Actual prime-block specialization of source equation (A.11). -/
theorem gsA9PrimeBlockFactor_le_one
    {f : ℕ → ℂ} (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (P : ℕ → Prop) [DecidablePred P]
    (N : ℕ) (sigma t : ℝ) :
    ‖Complex.exp (gsA9PrimeBlockSum f P N sigma t / 2) -
        Complex.exp (-(gsA9PrimeBlockSum f P N sigma t / 2))‖ *
      Real.exp (-(gsA9PrimeBlockRadius P N sigma) / 2) ≤ 1 := by
  exact norm_exp_half_sub_exp_neg_half_mul_exp_neg_le_one_of_norm
    (gsA9PrimeBlockSum f P N sigma t)
    (gsA9PrimeBlockRadius P N sigma)
    (norm_gsA9PrimeBlockSum_le_radius hbound P N sigma t)

/-- The product of the two concrete deletion-block factors used by the
two-block typical coefficient is still at most one.  This is the exact
two-block specialization of the last line of source equation (A.11). -/
theorem gsA9TwoPrimeBlockFactors_le_one
    {f : ℕ → ℂ} (hbound : ∀ n : ℕ, ‖f n‖ ≤ 1)
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (N : ℕ) (sigma t : ℝ) :
    (‖Complex.exp (gsA9PrimeBlockSum f P N sigma t / 2) -
          Complex.exp (-(gsA9PrimeBlockSum f P N sigma t / 2))‖ *
        Real.exp (-(gsA9PrimeBlockRadius P N sigma) / 2)) *
      (‖Complex.exp (gsA9PrimeBlockSum f Q N sigma t / 2) -
          Complex.exp (-(gsA9PrimeBlockSum f Q N sigma t / 2))‖ *
        Real.exp (-(gsA9PrimeBlockRadius Q N sigma) / 2)) ≤ 1 := by
  let a : ℝ :=
    ‖Complex.exp (gsA9PrimeBlockSum f P N sigma t / 2) -
        Complex.exp (-(gsA9PrimeBlockSum f P N sigma t / 2))‖ *
      Real.exp (-(gsA9PrimeBlockRadius P N sigma) / 2)
  let b : ℝ :=
    ‖Complex.exp (gsA9PrimeBlockSum f Q N sigma t / 2) -
        Complex.exp (-(gsA9PrimeBlockSum f Q N sigma t / 2))‖ *
      Real.exp (-(gsA9PrimeBlockRadius Q N sigma) / 2)
  have ha : a ≤ 1 := gsA9PrimeBlockFactor_le_one hbound P N sigma t
  have hb : b ≤ 1 := gsA9PrimeBlockFactor_le_one hbound Q N sigma t
  have ha0 : 0 ≤ a := by unfold a; positivity
  have hb0 : 0 ≤ b := by unfold b; positivity
  change a * b ≤ 1
  calc
    a * b ≤ 1 * b := mul_le_mul_of_nonneg_right ha hb0
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = 1 := by ring

/-- The product of all normalized prime-block factors in (A.11) is at most
one.  This is the finite product form used after inclusion--exclusion. -/
theorem prod_norm_exp_half_sub_exp_neg_half_mul_exp_neg_le_one
    {ι : Type*} (S : Finset ι) (z : ι → ℂ) (R : ι → ℝ)
    (hz : ∀ j ∈ S, ‖z j‖ ≤ R j) :
    ∏ j ∈ S,
        (‖Complex.exp (z j / 2) - Complex.exp (-(z j / 2))‖ *
          Real.exp (-R j / 2)) ≤ 1 := by
  apply Finset.prod_le_one
  · intro j hj
    positivity
  · intro j hj
    exact norm_exp_half_sub_exp_neg_half_mul_exp_neg_le_one_of_norm
      (z j) (R j) (hz j hj)

end

end Erdos67
