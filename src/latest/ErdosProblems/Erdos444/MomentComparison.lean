import ErdosProblems.Erdos444.Moment

/-!
# Extracting a large divisor count from a sparse representation support

This file contains the purely algebraic last step of the finite moment
argument.  It is deliberately independent of how the representation support
was proved small.
-/

namespace Erdos444

/-- Abstract real form of the moment comparison.  If a positive moment is at
least `N/2 * f^r`, at most `S * D^r`, and the support size satisfies
`2*S*(2*Z)^r ≤ N`, then `D` is at least `2*Z*f`.

The factor two is kept explicit so that a later estimate `F ≤ 2*f` gives the
clean conclusion `Z*F ≤ D`. -/
theorem two_mul_mul_le_of_moment_bounds
    {N f S D Z T : ℝ} {r : ℕ}
    (hr : 0 < r) (hN : 0 < N) (hf : 0 < f)
    (hS : 0 ≤ S) (hD : 0 ≤ D) (hZ : 0 < Z)
    (hlow : N / 2 * f ^ r ≤ T)
    (hupp : T ≤ S * D ^ r)
    (hsupport : 2 * S * (2 * Z) ^ r ≤ N) :
    2 * Z * f ≤ D := by
  by_contra hnot
  have hlt : D < 2 * Z * f := lt_of_not_ge hnot
  have htargetpos : 0 < 2 * Z * f := mul_pos (mul_pos (by norm_num) hZ) hf
  have hpowlt : D ^ r < (2 * Z * f) ^ r := by
    exact pow_lt_pow_left₀ hlt hD hr.ne'
  by_cases hSz : S = 0
  · rw [hSz, zero_mul] at hupp
    have hTpos : 0 < T := (mul_pos (div_pos hN (by norm_num)) (pow_pos hf r)).trans_le hlow
    linarith
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hSz)
  have hupperlt : S * D ^ r < S * (2 * Z * f) ^ r :=
    mul_lt_mul_of_pos_left hpowlt hSpos
  have hscale : S * (2 * Z) ^ r ≤ N / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [hsupport]
  have hfactor : (2 * Z * f) ^ r = (2 * Z) ^ r * f ^ r := by
    rw [mul_pow]
  have hfinal : S * (2 * Z * f) ^ r ≤ N / 2 * f ^ r := by
    rw [hfactor, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hscale (pow_nonneg hf.le r)
  exact (not_lt_of_ge (hlow.trans hupp)) (hupperlt.trans_le hfinal)

/-- Version with the reciprocal mass before discarding the bad part. -/
theorem mul_le_of_moment_bounds
    {N F f S D Z T : ℝ} {r : ℕ}
    (hr : 0 < r) (hN : 0 < N) (hf : 0 < f)
    (hS : 0 ≤ S) (hD : 0 ≤ D) (hZ : 0 < Z) (_hF : 0 ≤ F)
    (hretain : F ≤ 2 * f)
    (hlow : N / 2 * f ^ r ≤ T)
    (hupp : T ≤ S * D ^ r)
    (hsupport : 2 * S * (2 * Z) ^ r ≤ N) :
    Z * F ≤ D := by
  have hZF : Z * F ≤ 2 * Z * f := by
    calc
      Z * F ≤ Z * (2 * f) := mul_le_mul_of_nonneg_left hretain hZ.le
      _ = 2 * Z * f := by ring
  exact hZF.trans (two_mul_mul_le_of_moment_bounds hr hN hf hS hD hZ
    hlow hupp hsupport)

/-- Finite tuple-moment specialization.  All number-theoretic work is reduced
to the single support-cardinality hypothesis in the last line. -/
theorem large_maxDivisorCountNat_of_support_bound
    {A : Set ℕ} {Astar : Finset ℕ} {r U : ℕ} {F Z : ℝ}
    (hr : 0 < r) (hU : 0 < U)
    (hpos : ∀ a ∈ Astar, 0 < a)
    (hle : ∀ a ∈ Astar, a ≤ U)
    (hsub : ∀ a ∈ Astar, a ∈ A)
    (_hF : 0 ≤ F)
    (hretain : F ≤ 2 * ∑ a ∈ Astar, ((a : ℝ)⁻¹))
    (hstar : 0 < ∑ a ∈ Astar, ((a : ℝ)⁻¹))
    (hZ : 0 < Z)
    (hsupport : 2 * ((representationSupport Astar r (U ^ r)).card : ℝ) *
      (2 * Z) ^ r ≤ (U : ℝ) ^ r) :
    Z * F ≤ (maxDivisorCountNat A (U ^ r + 1) : ℝ) := by
  let f : ℝ := ∑ a ∈ Astar, ((a : ℝ)⁻¹)
  let S : ℝ := (representationSupport Astar r (U ^ r)).card
  let D : ℝ := maxDivisorCountNat A (U ^ r + 1)
  let T : ℝ := ∑ n ∈ Finset.Ioc 0 (U ^ r),
    (representationCount Astar r n : ℝ)
  have hlow : (U : ℝ) ^ r / 2 * f ^ r ≤ T :=
    half_pow_mul_sum_inv_pow_le_sum_representationCount Astar r U hpos hle
  have huppNat := sum_representationCount_powCutoff_le (Astar := Astar)
    (A := A) r U hsub
  have hupp : T ≤ S * D ^ r := by
    dsimp [T, S, D]
    exact_mod_cast huppNat
  apply mul_le_of_moment_bounds hr (pow_pos (Nat.cast_pos.mpr hU) r) hstar
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hZ _hF hretain hlow hupp
  simpa [S] using hsupport

end Erdos444
