import ErdosProblems.Erdos4.ProjectionReplacement
import ErdosProblems.Erdos4.LocalProjectionComparison

/-!
# Comparing the complete true and ideal principal projections

Replace one prime coordinate at a time. Every intermediate product is
contractive, and the same original coefficient energy bounds every slice.
Thus the total error is the sum of the local reciprocal-square errors.
-/

open scoped BigOperators

namespace Erdos4.ProductProjectionComparison

open DivisorCoefficients RestrictedProductNorm ProjectionReplacement

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

def mixedNormals (S : Finset P) (u v : P → Option (Fin k) → ℝ) (p : P) : Option (Fin k) → ℝ :=
  if p ∈ S then u p else v p

omit [Fintype P] in
theorem mixedNormals_insert (S : Finset P) (u v : P → Option (Fin k) → ℝ) (p : P) :
    mixedNormals (insert p S) u v = Function.update (mixedNormals S u v) p (u p) := by
  funext q
  by_cases hq : q = p
  · subst q
    simp [mixedNormals]
  · simp [mixedNormals, hq]

theorem norm_quadratic_difference_le {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p)
    (u v : P → Option (Fin k) → ℝ)
    (hu : ∀ p, ∑ a, u p a ^ 2 = 1) (hv : ∀ p, ∑ a, v p a ^ 2 = 1)
    (δ : P → ℝ)
    (hδ : ∀ p, LocalFourier.weightedMatrixNorm (localWeight (ell p))
      (fun a b => (ProjectionKernel.kernel (u p) a b : ℂ) -
        (ProjectionKernel.kernel (v p) a b : ℂ)) ≤ δ p) :
    ‖quadratic (coefficient m R ell) u - quadratic (coefficient m R ell) v‖ ≤
      energy (coefficient (k := k) m R ell) * ∑ p, δ p := by
  let N := energy (coefficient (k := k) m R ell)
  have hN : 0 ≤ N := energy_nonneg _
  have hempty : mixedNormals ∅ u v = v := by funext p; simp [mixedNormals]
  have huniv : mixedNormals Finset.univ u v = u := by funext p; simp [mixedNormals]
  have hmix (S : Finset P) : ∀ p, ∑ a, mixedNormals S u v p a ^ 2 = 1 := by
    intro p
    by_cases hp : p ∈ S
    · simpa only [mixedNormals, if_pos hp] using hu p
    · simpa only [mixedNormals, if_neg hp] using hv p
  have hfinite (S : Finset P) :
      ‖quadratic (coefficient m R ell) (mixedNormals S u v) - quadratic (coefficient m R ell) v‖ ≤
        N * ∑ p ∈ S, δ p := by
    induction S using Finset.induction_on with
    | empty => simp [hempty]
    | @insert p S hp ih =>
      have hstep := norm_single_replacement_le hm hR ell hell
        (mixedNormals S u v) (hmix S) p (u p)
      rw [← mixedNormals_insert S u v p] at hstep
      have hbase : mixedNormals S u v p = v p := by simp [mixedNormals, hp]
      rw [hbase] at hstep
      have hstep' :
          ‖quadratic (coefficient m R ell) (mixedNormals (insert p S) u v) -
            quadratic (coefficient m R ell) (mixedNormals S u v)‖ ≤ N * δ p :=
        hstep.trans (mul_le_mul_of_nonneg_left (hδ p) hN)
      calc
        _ = ‖(quadratic (coefficient m R ell) (mixedNormals (insert p S) u v) -
              quadratic (coefficient m R ell) (mixedNormals S u v)) +
            (quadratic (coefficient m R ell) (mixedNormals S u v) -
              quadratic (coefficient m R ell) v)‖ := by congr 1; ring
        _ ≤ ‖quadratic (coefficient m R ell) (mixedNormals (insert p S) u v) -
              quadratic (coefficient m R ell) (mixedNormals S u v)‖ +
            ‖quadratic (coefficient m R ell) (mixedNormals S u v) -
              quadratic (coefficient m R ell) v‖ := norm_add_le _ _
        _ ≤ N * δ p + N * ∑ q ∈ S, δ q := add_le_add hstep' ih
        _ = _ := by rw [Finset.sum_insert hp]; ring
  simpa only [huniv, N] using hfinite Finset.univ

/-- The complete projection comparison retains the exact original
coefficient energy and has a summable prime error. -/
theorem true_ideal_difference_le {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, k + 2 ≤ ell p) (j : Fin k) :
    ‖quadratic (coefficient m R ell) (fun p => ProjectionNormals.trueNormal (ell p : ℝ) j) -
      quadratic (coefficient m R ell) (fun p => IdealProjection.normal (ell p : ℝ) j)‖ ≤
        energy (coefficient (k := k) m R ell) * ∑ p, 10 * (k : ℝ) ^ 2 / (ell p : ℝ) ^ 2 := by
  apply norm_quadratic_difference_le hm hR ell (fun p => by have := hell p; omega)
    (fun p => ProjectionNormals.trueNormal (ell p : ℝ) j)
    (fun p => IdealProjection.normal (ell p : ℝ) j)
  · intro p
    exact ProjectionNormals.trueNormal_norm_one
      (by exact_mod_cast (show k < ell p by have := hell p; omega)) j
  · intro p
    exact IdealProjection.normal_norm_one
      (by exact_mod_cast (show 1 < ell p by have := hell p; omega)) j
  · intro p
    simpa only [Complex.ofReal_sub, IdealProjection.kernel] using
      LocalProjectionComparison.local_comparison_le (hell p) j

theorem true_form_eq_restricted (ell : P → ℕ) (hell : ∀ p, (k : ℝ) < ell p) (j : Fin k)
    (v : (P → Option (Fin k)) → ℝ) :
    ProjectionSliceBound.form (fun p => ProjectionNormals.trueNormal (ell p : ℝ) j) v v =
      restrictedForm (fun p => (ell p : ℝ))
        (fun s => ∏ p, LocalCharacterMatrix.deletionMask j (s p)) v v := by
  rw [ProjectionSliceBound.form_eq_sum, RestrictedTensor.restrictedForm_productMask_eq]
  simp_rw [ProjectionNormals.true_kernel_eq (hell _) j]

/-- Lower-bound transfer from the positive ideal projection to the actual
principal coefficient. -/
theorem ideal_form_sub_error_le_true {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, k + 2 ≤ ell p) (j : Fin k) :
    ProjectionSliceBound.form (fun p => IdealProjection.normal (ell p : ℝ) j)
      (coefficient m R ell) (coefficient m R ell) -
        energy (coefficient (k := k) m R ell) * ∑ p, 10 * (k : ℝ) ^ 2 / (ell p : ℝ) ^ 2 ≤
      restrictedForm (fun p => (ell p : ℝ))
        (fun s => ∏ p, LocalCharacterMatrix.deletionMask j (s p))
        (coefficient m R ell) (coefficient m R ell) := by
  have hh := true_ideal_difference_le hm hR ell hell j
  rw [quadratic_eq_form, quadratic_eq_form, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at hh
  rw [true_form_eq_restricted ell (fun p => by
    exact_mod_cast (show k < ell p by have := hell p; omega)) j] at hh
  have hlow := (abs_le.mp hh).1
  linarith

end Erdos4.ProductProjectionComparison
