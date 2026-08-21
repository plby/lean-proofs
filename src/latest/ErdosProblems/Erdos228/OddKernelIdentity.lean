import ErdosProblems.Erdos228.OddSine
import ErdosProblems.Erdos228.Kernel

/-!
# The exact finite odd-kernel identity

This file records the algebraic identity behind the odd-sine target in
`OddSine`.  In particular, it does not assume any of the analytic kernel
estimates packaged by `OddSine.KernelCertificate`.
-/

namespace Erdos228.OddKernelIdentity

open scoped BigOperators Interval
open Set MeasureTheory

noncomputable section

/-- The finite odd sine kernel, with the normalization used in BBMST
Section 5. -/
def oddKernel (n : ℕ) (x theta : ℝ) : ℝ :=
  4 * ∑ j ∈ Finset.range n,
    Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * x) *
      Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * theta)

/-- The odd kernel integrated over an oriented real interval. -/
def integratedOddKernel (n : ℕ) (I : Erdos228.OddSine.RealInterval)
    (theta : ℝ) : ℝ :=
  ∫ x in I.1..I.2, oddKernel n x theta

/-- Integrating the finite odd kernel is the same as integrating its
individual sine modes. -/
theorem integratedOddKernel_eq_sum (n : ℕ)
    (I : Erdos228.OddSine.RealInterval) (theta : ℝ) :
    integratedOddKernel n I theta =
      4 * ∑ j ∈ Finset.range n,
        (∫ x in I.1..I.2,
          Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * x)) *
            Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * theta) := by
  classical
  simp only [integratedOddKernel, oddKernel,
    intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_mul_const]
  · intro j hj
    exact (by fun_prop : Continuous (fun x : ℝ ↦
      Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * x) *
        Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * theta))).intervalIntegrable _ _

/-- Exact reconstruction of `OddSine.targetSine` from the integrated finite
odd kernel on the coloured base intervals.  This identity is valid even for
`n = 0`; positivity is needed only when dividing by the normalization. -/
theorem targetSine_eq_sum_integratedOddKernel {n : ℕ}
    (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    Erdos228.OddSine.targetSine F alpha theta =
      (Erdos228.OddSine.K * Real.sqrt n) *
        ∑ I : (↑F.base : Type), alpha I * integratedOddKernel n I.1 theta := by
  classical
  rw [show Erdos228.OddSine.targetSine F alpha theta =
      ∑ j ∈ Finset.range n,
        (∑ I : (↑F.base : Type),
          alpha I * (4 * Erdos228.OddSine.K * Real.sqrt n *
            ∫ x in I.1.1..I.1.2,
              Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * x))) *
          Real.sin ((Erdos228.Rounding.oddFrequency j : ℝ) * theta) by
    simp only [Erdos228.OddSine.targetSine,
      Erdos228.Rounding.oddSineSum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Erdos228.OddSine.fourierTarget,
      dif_pos (Finset.mem_range.mp hj)]
  ]
  simp_rw [integratedOddKernel_eq_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The normalized target is exactly the signed sum of integrated finite odd
kernels. -/
theorem targetSine_div_eq_sum_integratedOddKernel {n : ℕ} (hn : 0 < n)
    (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) (theta : ℝ) :
    Erdos228.OddSine.targetSine F alpha theta /
        (Erdos228.OddSine.K * Real.sqrt n) =
      ∑ I : (↑F.base : Type), alpha I * integratedOddKernel n I.1 theta := by
  rw [targetSine_eq_sum_integratedOddKernel]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num [Erdos228.OddSine.K])
    (Real.sqrt_ne_zero'.2 (by exact_mod_cast hn)))

/-- Away from its removable singularities, the finite odd kernel has the
usual quotient form. -/
theorem oddKernel_eq_quotient (n : ℕ) {x theta : ℝ}
    (hsub : Real.sin (x - theta) ≠ 0)
    (hadd : Real.sin (x + theta) ≠ 0) :
    oddKernel n x theta =
      Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
        Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta) := by
  simpa [oddKernel, Erdos228.Rounding.oddFrequency, mul_comm] using
    (Erdos228.Kernel.odd_dirichlet_kernel n
      (θ := x) (θ₀ := theta) hsub hadd)

/-- If `x` is in the open first quadrant and `theta` is in the closed first
quadrant, the only possible singularity of the quotient form is the diagonal
`x = theta`. -/
theorem oddKernel_eq_quotient_of_theta_mem_Icc (n : ℕ) {x theta : ℝ}
    (hx₀ : 0 < x) (hx₁ : x < Real.pi / 2)
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2))
    (hxt : x ≠ theta) :
    oddKernel n x theta =
      Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
        Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta) := by
  rcases htheta with ⟨ht₀, ht₁⟩
  apply oddKernel_eq_quotient
  · intro hzero
    have hdiff : x - theta = 0 :=
      (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])).mp hzero
    exact hxt (sub_eq_zero.mp hdiff)
  · intro hzero
    have hsum : x + theta = 0 :=
      (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])).mp hzero
    linarith

/-- Open-first-quadrant specialization of
`oddKernel_eq_quotient_of_theta_mem_Icc`. -/
theorem oddKernel_eq_quotient_of_firstQuadrant (n : ℕ) {x theta : ℝ}
    (hx₀ : 0 < x) (hx₁ : x < Real.pi / 2)
    (ht₀ : 0 < theta) (ht₁ : theta < Real.pi / 2)
    (hxt : x ≠ theta) :
    oddKernel n x theta =
      Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
        Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta) :=
  oddKernel_eq_quotient_of_theta_mem_Icc n hx₀ hx₁ ⟨ht₀.le, ht₁.le⟩ hxt

/-- The quotient form may be integrated over an interval lying strictly in
the first quadrant while the evaluation angle ranges over the closed first
quadrant.  The diagonal singularity is discarded as a null singleton. -/
theorem integral_oddKernel_eq_quotient_of_theta_mem_Icc (n : ℕ)
    {a b theta : ℝ} (hab : a ≤ b) (ha : 0 < a) (hb : b < Real.pi / 2)
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    (∫ x in a..b, oddKernel n x theta) =
      ∫ x in a..b,
        (Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
          Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta)) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume theta] with x hxt hx
  rw [uIoc_of_le hab] at hx
  exact oddKernel_eq_quotient_of_theta_mem_Icc n
    (ha.trans hx.1) (hx.2.trans_lt hb) htheta hxt

/-- The quotient form may be integrated over any interval lying strictly in
the first quadrant.  The diagonal singularity is discarded as a null
singleton. -/
theorem integral_oddKernel_eq_quotient_of_firstQuadrant (n : ℕ)
    {a b theta : ℝ} (hab : a ≤ b) (ha : 0 < a) (hb : b < Real.pi / 2)
    (ht₀ : 0 < theta) (ht₁ : theta < Real.pi / 2) :
    (∫ x in a..b, oddKernel n x theta) =
      ∫ x in a..b,
        (Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
          Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta)) :=
  integral_oddKernel_eq_quotient_of_theta_mem_Icc n hab ha hb
    ⟨ht₀.le, ht₁.le⟩

/-- Every base interval of a suitable family admits the integrated quotient
form for evaluation angles in the closed first quadrant. -/
theorem integratedOddKernel_eq_quotient_of_mem_base_theta_mem_Icc {n : ℕ}
    (hn : 0 < n) (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (I : Erdos228.OddSine.RealInterval) (hI : I ∈ F.base)
    {theta : ℝ} (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    integratedOddKernel n I theta =
      ∫ x in I.1..I.2,
        (Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
          Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta)) := by
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hmesh : 0 < 100 * Real.pi / (n : ℝ) := by positivity
  apply integral_oddKernel_eq_quotient_of_theta_mem_Icc n
  · exact F.ordered I hI
  · linarith [F.away_from_axes I hI |>.1]
  · linarith [F.away_from_axes I hI |>.2]
  · exact htheta

/-- Closed-first-quadrant quotient-integral form of the normalized target.
This is the direct form consumed by kernel estimates on the base intervals. -/
theorem targetSine_div_eq_sum_quotientIntegral_of_theta_mem_Icc {n : ℕ}
    (hn : 0 < n) (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (alpha : (↑F.base : Type) → ℝ) {theta : ℝ}
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    Erdos228.OddSine.targetSine F alpha theta /
        (Erdos228.OddSine.K * Real.sqrt n) =
      ∑ I : (↑F.base : Type), alpha I *
        ∫ x in I.1.1..I.1.2,
          (Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
            Real.sin ((2 * n : ℕ) * (x + theta)) /
              Real.sin (x + theta)) := by
  rw [targetSine_div_eq_sum_integratedOddKernel hn]
  apply Finset.sum_congr rfl
  intro I hI
  rw [integratedOddKernel_eq_quotient_of_mem_base_theta_mem_Icc
    hn F I.1 I.2 htheta]

/-- Every base interval of a suitable family admits the integrated quotient
form when `n` is positive and the evaluation angle lies in the open first
quadrant. -/
theorem integratedOddKernel_eq_quotient_of_mem_base {n : ℕ} (hn : 0 < n)
    (F : Erdos228.OddSine.SuitableIntervalFamily n)
    (I : Erdos228.OddSine.RealInterval) (hI : I ∈ F.base)
    {theta : ℝ} (ht₀ : 0 < theta) (ht₁ : theta < Real.pi / 2) :
    integratedOddKernel n I theta =
      ∫ x in I.1..I.2,
        (Real.sin ((2 * n : ℕ) * (x - theta)) / Real.sin (x - theta) -
          Real.sin ((2 * n : ℕ) * (x + theta)) / Real.sin (x + theta)) :=
  integratedOddKernel_eq_quotient_of_mem_base_theta_mem_Icc hn F I hI
    ⟨ht₀.le, ht₁.le⟩

end

end Erdos228.OddKernelIdentity
