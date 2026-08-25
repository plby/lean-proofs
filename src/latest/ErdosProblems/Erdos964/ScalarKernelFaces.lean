import ErdosProblems.Erdos964.ScalarKernelPolynomial

/-!
# The two polynomial faces of the scalar kernel
-/

namespace Erdos964

def scalarSmallKernelPolynomial (z v : ℝ) : ℝ := ((7 - 6 * v) * z - 3 * z ^ 2) ^ 2

def scalarLargeKernelPolynomial (v : ℝ) : ℝ := (4 - 7 * v + 3 * v ^ 2) ^ 2

theorem scalarSmallKernelPolynomial_expand (z v : ℝ) :
    scalarSmallKernelPolynomial z v = 36 * z ^ 2 * v ^ 2 +
      (36 * z ^ 3 - 84 * z ^ 2) * v + (9 * z ^ 4 - 42 * z ^ 3 + 49 * z ^ 2) := by
  unfold scalarSmallKernelPolynomial
  ring

theorem scalarLargeKernelPolynomial_expand (v : ℝ) :
    scalarLargeKernelPolynomial v = 9 * v ^ 4 - 42 * v ^ 3 + 73 * v ^ 2 - 56 * v + 16 := by
  unfold scalarLargeKernelPolynomial
  ring

theorem scalarTransformPolynomial_reflection (R r : ℕ) (hr : 0 < r) (hrR : r < R) :
    scalarTransformPolynomial R r = Real.log R *
      (4 - 7 * (Real.log r / Real.log R) + 3 * (Real.log r / Real.log R) ^ 2) := by
  rw [scalarTransformPolynomial, if_pos (show 1 ≤ r ∧ r < R from ⟨hr, hrR⟩)]
  unfold ggpyPolynomialPrimitive
  ring

theorem scalarTransformPolynomial_difference_small (R p r : ℕ)
    (hp : 0 < p) (hr : 0 < r) (hrR : r < R) (hprR : p * r < R) :
    scalarTransformPolynomial R r - scalarTransformPolynomial R (p * r) =
      Real.log R * ((7 - 6 * (Real.log r / Real.log R)) * (Real.log p / Real.log R) -
        3 * (Real.log p / Real.log R) ^ 2) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hrR' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [scalarTransformPolynomial_reflection R r hr hrR,
    scalarTransformPolynomial_reflection R (p * r) (Nat.mul_pos hp hr) hprR,
    Nat.cast_mul, Real.log_mul hpR.ne' hrR'.ne']
  ring

theorem scalarTransformPolynomial_difference_large (R p r : ℕ)
    (hr : 0 < r) (hrR : r < R) (hRpr : R ≤ p * r) :
    scalarTransformPolynomial R r - scalarTransformPolynomial R (p * r) =
      Real.log R * (4 - 7 * (Real.log r / Real.log R) +
        3 * (Real.log r / Real.log R) ^ 2) := by
  rw [scalarTransformPolynomial_eq_zero R (p * r) hRpr, sub_zero,
    scalarTransformPolynomial_reflection R r hr hrR]

theorem mul_lt_radius_iff_le_quotient (R p r : ℕ) (hR : 1 ≤ R) (hp : 0 < p) :
    p * r < R ↔ r ≤ (R - 1) / p := by
  rw [Nat.le_div_iff_mul_le hp, Nat.mul_comm r p]
  omega

theorem sum_Ico_if_mul_lt_radius (R p : ℕ) (hR : 1 ≤ R) (hp : 0 < p)
    (F : ℕ → ℝ) (hF : F 0 = 0) :
    (∑ r ∈ Finset.Ico 1 R, if p * r < R then F r else 0) =
      ∑ r ∈ Finset.Icc 0 ((R - 1) / p), F r := by
  classical
  have hQ : (R - 1) / p ≤ R - 1 := Nat.div_le_self _ _
  have hset : (Finset.Ico 1 R).filter (fun r => p * r < R) =
      Finset.Icc 1 ((R - 1) / p) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc,
      mul_lt_radius_iff_le_quotient R p r hR hp]
    omega
  rw [← Finset.sum_filter, hset]
  have hinterval (Q : ℕ) : Finset.Icc 0 Q = insert 0 (Finset.Icc 1 Q) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hinterval, Finset.sum_insert (by simp), hF, zero_add]

end Erdos964
