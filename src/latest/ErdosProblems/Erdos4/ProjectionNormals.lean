import ErdosProblems.Erdos4.IdealProjection
import ErdosProblems.Erdos4.LocalCharacterMatrix
import ErdosProblems.Erdos4.RestrictedTensor

/-!
# True and ideal local projection normals

The true normal is the normalized occupied-state evaluation vector. Its
empty coordinate agrees exactly with the ideal normal, and each occupied
coordinate differs by at most `1 / ell`. This is the extra local saving
used in the coefficient-sensitive projection comparison.
-/

open scoped BigOperators

namespace Erdos4.ProjectionNormals

open LocalOrthogonality

variable {k : ℕ}

noncomputable def trueNormal (ell : ℝ) (j : Fin k) (a : Option (Fin k)) : ℝ :=
  extendedBasis ell a (some j) / Real.sqrt ell

theorem trueNormal_norm_one {ell : ℝ} (hell : (k : ℝ) < ell) (j : Fin k) :
    (∑ a, trueNormal ell j a ^ 2) = 1 := by
  have he : 0 < ell := lt_of_le_of_lt (Nat.cast_nonneg _) hell
  simp only [trueNormal, div_pow]
  rw [← Finset.sum_div, sum_evaluation_sq hell j, Real.sq_sqrt he.le, div_self he.ne']

theorem mean_deletionMask_eq_sub (ell : ℝ) (j : Fin k) (f : Option (Fin k) → ℝ) :
    mean ell (fun s => LocalCharacterMatrix.deletionMask j s * f s) =
      mean ell f - f (some j) / ell := by
  rw [LocalCharacterMatrix.mean_deletionMask]
  unfold mean
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin k))
    (fun i => f (some i)) (Finset.mem_univ j)]
  ring

/-- The actual principal kernel is the deletion of `trueNormal`. -/
theorem true_kernel_eq {ell : ℝ} (hell : (k : ℝ) < ell) (j : Fin k)
    (a b : Option (Fin k)) :
    RestrictedTensor.localKernel ell (LocalCharacterMatrix.deletionMask j) a b =
      ProjectionKernel.kernel (trueNormal ell j) a b := by
  have he : 0 < ell := lt_of_le_of_lt (Nat.cast_nonneg _) hell
  unfold RestrictedTensor.localKernel
  rw [mean_deletionMask_eq_sub, mean_extendedBasis_mul hell]
  simp only [ProjectionKernel.kernel, trueNormal]
  rw [div_mul_div_comm, Real.mul_self_sqrt he.le]

theorem coupling_nonneg (ell : ℝ) : 0 ≤ coupling ell k := by
  unfold coupling
  positivity

theorem coupling_le_inv_sqrt {ell : ℝ} (hell : (k : ℝ) < ell) :
    coupling ell k ≤ 1 / Real.sqrt ell := by
  have hs := LocalOrthogonality.sqrt_pos hell
  have hc := coupling_nonneg (k := k) ell
  have heq : coupling ell k * (Real.sqrt ell + Real.sqrt (ell - k)) = 1 := by
    exact inv_mul_cancel₀ (by positivity)
  apply (le_div_iff₀ hs).mpr
  nlinarith [mul_nonneg hc (Real.sqrt_nonneg (ell - k))]

theorem sqrt_difference_le {ell : ℝ} (hell : 1 < ell) :
    Real.sqrt ell - Real.sqrt (ell - 1) ≤ 1 / Real.sqrt ell := by
  have he : 0 < ell := lt_trans zero_lt_one hell
  have hs : 0 < Real.sqrt ell := Real.sqrt_pos.mpr he
  have hle : Real.sqrt (ell - 1) ≤ Real.sqrt ell := Real.sqrt_le_sqrt (by linarith)
  have hmul := mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg (ell - 1))
  have he2 := Real.sq_sqrt he.le
  have hd2 := Real.sq_sqrt (sub_pos.mpr hell).le
  apply (le_div_iff₀ hs).mpr
  nlinarith

theorem normal_difference_none (ell : ℝ) (j : Fin k) :
    trueNormal ell j none - IdealProjection.normal ell j none = 0 := by
  simp [trueNormal, extendedBasis, IdealProjection.normal]

/-- The occupied normal coordinates have an extra inverse-prime saving. -/
theorem normal_difference_some_le {ell : ℝ} (hell : (k : ℝ) < ell)
    (j i : Fin k) :
    |trueNormal ell j (some i) - IdealProjection.normal ell j (some i)| ≤ 1 / ell := by
  have hk : 1 ≤ k := by have := j.isLt; omega
  have he1 : 1 < ell := lt_of_le_of_lt (by exact_mod_cast hk) hell
  have hs : 0 < Real.sqrt ell := LocalOrthogonality.sqrt_pos hell
  have he : 0 < ell := lt_trans zero_lt_one he1
  have hdelta0 : 0 ≤ Real.sqrt ell - Real.sqrt (ell - 1) :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hdelta1 := sqrt_difference_le he1
  have hc0 := coupling_nonneg (k := k) ell
  have hc1 := coupling_le_inv_sqrt hell
  have hsmall0 : 0 ≤ if i = j then Real.sqrt ell - Real.sqrt (ell - 1) else 0 := by
    split_ifs <;> positivity
  have hsmall1 : (if i = j then Real.sqrt ell - Real.sqrt (ell - 1) else 0) ≤ 1 / Real.sqrt ell := by
    split_ifs
    · exact hdelta1
    · positivity
  have hnum : |coupling ell k - (if i = j then Real.sqrt ell - Real.sqrt (ell - 1) else 0)| ≤
      1 / Real.sqrt ell := abs_le.mpr ⟨by linarith, by linarith⟩
  have heq : trueNormal ell j (some i) - IdealProjection.normal ell j (some i) =
      (coupling ell k - (if i = j then Real.sqrt ell - Real.sqrt (ell - 1) else 0)) / Real.sqrt ell := by
    by_cases hij : i = j
    · subst i
      simp only [trueNormal, extendedBasis, basis, IdealProjection.normal, ↓reduceIte]
      ring
    · simp only [trueNormal, extendedBasis, basis, IdealProjection.normal,
        if_neg hij, if_neg (Ne.symm hij), sub_zero]
  rw [heq, abs_div, abs_of_pos hs]
  exact (div_le_div_of_nonneg_right hnum hs.le).trans_eq
    (by rw [div_div, Real.mul_self_sqrt he.le])

noncomputable def weightedSize {A : Type*} [Fintype A] (c u : A → ℝ) : ℝ :=
  ∑ a, |u a| * c a

theorem trueNormal_weightedSize_le {ell : ℕ} (hell : k + 2 ≤ ell) (j : Fin k) :
    weightedSize (DivisorCoefficients.localWeight ell) (trueNormal (ell : ℝ) j) ≤
      (1 + 2 * k) / Real.sqrt (ell : ℝ) := by
  have he : 0 < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  have hs : 0 < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr he
  unfold weightedSize trueNormal
  simp only [abs_div, abs_of_pos hs]
  have heq : (∑ a, |extendedBasis (ell : ℝ) a (some j)| / Real.sqrt (ell : ℝ) *
      DivisorCoefficients.localWeight ell a) =
      (∑ a, |extendedBasis (ell : ℝ) a (some j)| * DivisorCoefficients.localWeight ell a) /
        Real.sqrt (ell : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun a _ha => by ring)
  rw [heq]
  exact div_le_div_of_nonneg_right (LocalFourier.sum_weighted_evaluation_le hell (some j)) hs.le

theorem idealNormal_weightedSize {ell : ℕ} (hell : 2 ≤ ell) (j : Fin k) :
    weightedSize (DivisorCoefficients.localWeight ell) (IdealProjection.normal (ell : ℝ) j) =
      2 / Real.sqrt (ell : ℝ) := by
  have he : (1 : ℝ) < ell := by exact_mod_cast hell
  have hs : 0 < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hd : 0 < Real.sqrt ((ell : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  unfold weightedSize
  rw [Fintype.sum_option]
  simp only [IdealProjection.normal, DivisorCoefficients.localWeight,
    abs_div, abs_of_pos hs, abs_one, mul_one]
  have hterm (i : Fin k) :
      |if i = j then -Real.sqrt ((ell : ℝ) - 1) / Real.sqrt (ell : ℝ) else 0| *
        (Real.sqrt ((ell : ℝ) - 1))⁻¹ = if i = j then 1 / Real.sqrt (ell : ℝ) else 0 := by
    split_ifs
    · rw [abs_div, abs_neg, abs_of_pos hd, abs_of_pos hs]
      field_simp
    · simp
  simp_rw [hterm]
  simp
  ring

theorem normal_difference_weightedSize_le {ell : ℕ} (hell : k + 2 ≤ ell) (j : Fin k) :
    weightedSize (DivisorCoefficients.localWeight ell)
      (fun a => trueNormal (ell : ℝ) j a - IdealProjection.normal (ell : ℝ) j a) ≤
        2 * k / ((ell : ℝ) * Real.sqrt (ell : ℝ)) := by
  have he : 0 < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  have hk : (k : ℝ) < ell := by exact_mod_cast (show k < ell by omega)
  have hs : 0 < Real.sqrt (ell : ℝ) := Real.sqrt_pos.mpr he
  have hweight (i : Fin k) : DivisorCoefficients.localWeight ell (some i) ≤
      2 / Real.sqrt (ell : ℝ) := by
    apply (le_div_iff₀ hs).mpr
    simpa only [mul_comm] using LocalFourier.sqrt_mul_localWeight_le_two (by omega) i
  have hterm (i : Fin k) :
      |trueNormal (ell : ℝ) j (some i) - IdealProjection.normal (ell : ℝ) j (some i)| *
        DivisorCoefficients.localWeight ell (some i) ≤ 2 / ((ell : ℝ) * Real.sqrt (ell : ℝ)) := by
    have hh := mul_le_mul (normal_difference_some_le hk j i) (hweight i)
      (DivisorCoefficients.localWeight_nonneg ell (some i)) (one_div_pos.mpr he).le
    exact hh.trans_eq (by ring)
  unfold weightedSize
  rw [Fintype.sum_option]
  simp only [normal_difference_none, abs_zero, zero_mul, zero_add]
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) (fun i _hi => hterm i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  exact hh.trans_eq (by ring)

end Erdos4.ProjectionNormals
