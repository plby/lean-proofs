import ErdosProblems.Erdos1038.PolynomialBridge

/-!
# The extremizing polynomial family

This module proves, directly in Mathlib, that `(X^2 - 1)^m` is admissible
for every positive `m` and that its strict unit sublevel set has Lebesgue
measure `2 * sqrt 2`.  This is the easy (attainment) direction of the sharp
upper theorem and is independent of Tao's difficult universal bound.
-/

open scoped ENNReal Real
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

/-- The family asserted to attain the upper extremum. -/
def extremalPolynomial (m : ℕ) : Polynomial ℝ := (X ^ 2 - 1) ^ m

theorem extremalBase_monic : (X ^ 2 - 1 : Polynomial ℝ).Monic := by
  simpa using!
    Polynomial.monic_X_pow_sub_C (1 : ℝ) (by norm_num : (2 : ℕ) ≠ 0)

theorem extremalBase_factor :
    (X ^ 2 - 1 : Polynomial ℝ) = (X - C (-1)) * (X - C 1) := by
  norm_num
  ring

theorem extremalBase_splits : (X ^ 2 - 1 : Polynomial ℝ).Splits := by
  rw [extremalBase_factor]
  exact (Polynomial.Splits.X_sub_C (-1)).mul
    (Polynomial.Splits.X_sub_C 1)

theorem extremalPolynomial_monic (m : ℕ) : (extremalPolynomial m).Monic :=
  extremalBase_monic.pow m

theorem extremalPolynomial_ne_one {m : ℕ} (hm : 0 < m) :
    extremalPolynomial m ≠ 1 := by
  intro heq
  have hbasedegree : (X ^ 2 - 1 : Polynomial ℝ).natDegree = 2 := by
    simpa using!
      (Polynomial.natDegree_X_pow_sub_C (R := ℝ) (n := 2) (r := 1))
  have hdegree : (extremalPolynomial m).natDegree = m * 2 := by
    rw [extremalPolynomial, extremalBase_monic.natDegree_pow, hbasedegree]
  have hzero : (extremalPolynomial m).natDegree = 0 := by
    rw [heq]
    simp
  omega

theorem extremalPolynomial_splits (m : ℕ) :
    (extremalPolynomial m).Splits :=
  extremalBase_splits.pow m

theorem extremalPolynomial_root_mem {m : ℕ} {r : ℝ}
    (hr : r ∈ (extremalPolynomial m).roots) : r ∈ Set.Icc (-1 : ℝ) 1 := by
  have hprod :
      (X - C (-1) : Polynomial ℝ) * (X - C 1) ≠ 0 :=
    mul_ne_zero (Polynomial.monic_X_sub_C (-1 : ℝ)).ne_zero
      (Polynomial.monic_X_sub_C (1 : ℝ)).ne_zero
  rw [extremalPolynomial, extremalBase_factor, Polynomial.roots_pow,
    Polynomial.roots_mul hprod, Polynomial.roots_X_sub_C,
    Polynomial.roots_X_sub_C] at hr
  simp at hr
  rcases hr with ⟨_, hr | hr⟩ <;> simp [hr]

theorem extremalPolynomial_admissible {m : ℕ} (hm : 0 < m) :
    IsAdmissible (extremalPolynomial m) := by
  refine ⟨extremalPolynomial_monic m, extremalPolynomial_ne_one hm, ?_⟩
  have hfilter :
      (extremalPolynomial m).roots.filter
          (fun x => x ∈ Set.Icc (-1 : ℝ) 1) =
        (extremalPolynomial m).roots := by
    exact Multiset.filter_eq_self.mpr fun _ hr =>
      extremalPolynomial_root_mem hr
  rw [hfilter]
  exact (extremalPolynomial_splits m).natDegree_eq_card_roots.symm

theorem extremalPolynomial_eval (m : ℕ) (x : ℝ) :
    (extremalPolynomial m).eval x = (x ^ 2 - 1) ^ m := by
  simp [extremalPolynomial]

theorem mem_sublevel_extremal_iff {m : ℕ} (hm : 0 < m) (x : ℝ) :
    x ∈ sublevelSet (extremalPolynomial m) ↔ |x ^ 2 - 1| < 1 := by
  rw [sublevelSet, Set.mem_ofPred_eq, extremalPolynomial_eval, abs_pow]
  exact pow_lt_one_iff_of_nonneg (abs_nonneg _) (Nat.ne_of_gt hm)

theorem abs_sq_sub_one_lt_one_iff (x : ℝ) :
    |x ^ 2 - 1| < 1 ↔
      x ∈ Ioo (-Real.sqrt 2) 0 ∪ Ioo 0 (Real.sqrt 2) := by
  rw [abs_lt]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hx2pos : 0 < x ^ 2 := by linarith
    have hxne : x ≠ 0 := by nlinarith
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have habs : |x| < Real.sqrt 2 := by
      rw [← sq_lt_sq₀ (abs_nonneg x) (le_of_lt hsqrt)]
      rw [sq_abs, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    rw [abs_lt] at habs
    rcases lt_or_gt_of_ne hxne with hx | hx
    · exact Or.inl ⟨habs.1, hx⟩
    · exact Or.inr ⟨hx, habs.2⟩
  · rintro (hx | hx)
    · rcases hx with ⟨hxlo, hxhi⟩
      have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      have habs : |x| < Real.sqrt 2 := (abs_lt).2 ⟨hxlo, by linarith⟩
      have hsq : x ^ 2 < (Real.sqrt 2) ^ 2 :=
        (sq_lt_sq).2 (by
          simpa [abs_of_nonneg (le_of_lt hsqrt)] using! habs)
      have hx2lt : x ^ 2 < 2 := by
        simpa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using! hsq
      constructor <;> nlinarith [sq_pos_of_neg hxhi]
    · rcases hx with ⟨hxlo, hxhi⟩
      have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      have habs : |x| < Real.sqrt 2 := (abs_lt).2 ⟨by linarith, hxhi⟩
      have hsq : x ^ 2 < (Real.sqrt 2) ^ 2 :=
        (sq_lt_sq).2 (by
          simpa [abs_of_nonneg (le_of_lt hsqrt)] using! habs)
      have hx2lt : x ^ 2 < 2 := by
        simpa [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] using! hsq
      constructor <;> nlinarith [sq_pos_of_pos hxlo]

theorem sublevelSet_extremal {m : ℕ} (hm : 0 < m) :
    sublevelSet (extremalPolynomial m) =
      Ioo (-Real.sqrt 2) 0 ∪ Ioo 0 (Real.sqrt 2) := by
  ext x
  rw [mem_sublevel_extremal_iff hm, abs_sq_sub_one_lt_one_iff]

theorem sublevelVolume_extremal {m : ℕ} (hm : 0 < m) :
    sublevelVolume (extremalPolynomial m) =
      ENNReal.ofReal (2 * Real.sqrt 2) := by
  rw [sublevelVolume, sublevelSet_extremal hm]
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hd :
      Disjoint (Ioo (-Real.sqrt 2) 0) (Ioo 0 (Real.sqrt 2)) := by
    rw [Set.Ioo_disjoint_Ioo]
    simp [hsqrt]
  rw [MeasureTheory.measure_union hd measurableSet_Ioo, Real.volume_Ioo,
    Real.volume_Ioo]
  rw [show (0 : ℝ) - -Real.sqrt 2 = Real.sqrt 2 by ring,
    show Real.sqrt 2 - 0 = Real.sqrt 2 by ring]
  rw [← ENNReal.ofReal_add hsqrt hsqrt]
  congr 1
  ring

/-- Each positive member of the displayed family is admissible and has the
claimed extremal length. -/
theorem extremalPolynomial_attains (m : ℕ) (hm : 0 < m) :
    IsAdmissible ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ m) ∧
      sublevelVolume ((Polynomial.X ^ 2 - 1 : Polynomial ℝ) ^ m) =
        ENNReal.ofReal (2 * Real.sqrt 2) := by
  change IsAdmissible (extremalPolynomial m) ∧
    sublevelVolume (extremalPolynomial m) =
      ENNReal.ofReal (2 * Real.sqrt 2)
  exact ⟨extremalPolynomial_admissible hm, sublevelVolume_extremal hm⟩

/-- The explicit examples already prove the easy inequality in the sharp
supremum identity. -/
theorem proposedSupremum_le_supremumLength :
    ENNReal.ofReal (2 * Real.sqrt 2) ≤ supremumLength := by
  let f : AdmissiblePolynomial :=
    ⟨extremalPolynomial 1, extremalPolynomial_admissible (by decide)⟩
  have hle : sublevelVolume f.1 ≤ supremumLength := by
    exact le_iSup (fun g : AdmissiblePolynomial => sublevelVolume g.1) f
  rw [show f.1 = extremalPolynomial 1 by rfl,
    sublevelVolume_extremal (by decide)] at hle
  exact hle

end

end Erdos1038
