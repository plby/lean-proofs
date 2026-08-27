import ErdosProblems.Erdos4.FGKMTProjectionReplacement
import ErdosProblems.Erdos4.FGKMTIdealPairs
import ErdosProblems.Erdos4.ProductProjectionComparison

/-! Transferring the rational-profile gain from ideal to true principal projections. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open DivisorCoefficients RestrictedProductNorm ProjectionReplacement ProductProjectionComparison

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

theorem norm_rational_quadratic_difference_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p)
    (u v : P → Option (Fin k) → ℝ)
    (hu : ∀ p, ∑ a, u p a ^ 2 = 1) (hv : ∀ p, ∑ a, v p a ^ 2 = 1)
    (δ : P → ℝ)
    (hδ : ∀ p, LocalFourier.weightedMatrixNorm (localWeight (ell p))
      (fun a c => (ProjectionKernel.kernel (u p) a c : ℂ) -
        (ProjectionKernel.kernel (v p) a c : ℂ)) ≤ δ p) :
    ‖quadratic (rationalCoefficient b R ell) u - quadratic (rationalCoefficient b R ell) v‖ ≤
      energy (rationalCoefficient (k := k) b R ell) * ∑ p, δ p := by
  let N := energy (rationalCoefficient (k := k) b R ell)
  have hN : 0 ≤ N := energy_nonneg _
  have hempty : mixedNormals ∅ u v = v := by funext p; simp [mixedNormals]
  have huniv : mixedNormals Finset.univ u v = u := by funext p; simp [mixedNormals]
  have hmix (S : Finset P) : ∀ p, ∑ a, mixedNormals S u v p a ^ 2 = 1 := by
    intro p
    by_cases hp : p ∈ S
    · simpa only [mixedNormals, if_pos hp] using hu p
    · simpa only [mixedNormals, if_neg hp] using hv p
  have hfinite (S : Finset P) :
      ‖quadratic (rationalCoefficient b R ell) (mixedNormals S u v) -
        quadratic (rationalCoefficient b R ell) v‖ ≤ N * ∑ p ∈ S, δ p := by
    induction S using Finset.induction_on with
    | empty => simp [hempty]
    | @insert p S hp ih =>
      have hstep := norm_rational_single_replacement_le hb R ell hell
        (mixedNormals S u v) (hmix S) p (u p)
      rw [← mixedNormals_insert S u v p] at hstep
      have hbase : mixedNormals S u v p = v p := by simp [mixedNormals, hp]
      rw [hbase] at hstep
      have hstep' :
          ‖quadratic (rationalCoefficient b R ell) (mixedNormals (insert p S) u v) -
            quadratic (rationalCoefficient b R ell) (mixedNormals S u v)‖ ≤ N * δ p :=
        hstep.trans (mul_le_mul_of_nonneg_left (hδ p) hN)
      calc
        _ = ‖(quadratic (rationalCoefficient b R ell) (mixedNormals (insert p S) u v) -
              quadratic (rationalCoefficient b R ell) (mixedNormals S u v)) +
            (quadratic (rationalCoefficient b R ell) (mixedNormals S u v) -
              quadratic (rationalCoefficient b R ell) v)‖ := by congr 1; ring
        _ ≤ ‖quadratic (rationalCoefficient b R ell) (mixedNormals (insert p S) u v) -
              quadratic (rationalCoefficient b R ell) (mixedNormals S u v)‖ +
            ‖quadratic (rationalCoefficient b R ell) (mixedNormals S u v) -
              quadratic (rationalCoefficient b R ell) v‖ := norm_add_le _ _
        _ ≤ N * δ p + N * ∑ q ∈ S, δ q := add_le_add hstep' ih
        _ = _ := by rw [Finset.sum_insert hp]; ring
  simpa only [huniv, N] using hfinite Finset.univ

theorem rational_true_ideal_difference_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, k + 2 ≤ ell p) (j : Fin k) :
    ‖quadratic (rationalCoefficient b R ell) (fun p => ProjectionNormals.trueNormal (ell p : ℝ) j) -
      quadratic (rationalCoefficient b R ell) (fun p => IdealProjection.normal (ell p : ℝ) j)‖ ≤
        energy (rationalCoefficient (k := k) b R ell) * ∑ p, 10 * (k : ℝ) ^ 2 / (ell p : ℝ) ^ 2 := by
  apply norm_rational_quadratic_difference_le hb R ell (fun p => by have := hell p; omega)
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

theorem rationalIdealForm_eq_projection (b : ℝ) (R : ℕ) (ell : P → ℕ) (j : Fin k) :
    rationalIdealForm b R ell j =
      ProjectionSliceBound.form (fun p => IdealProjection.normal (ell p : ℝ) j)
        (rationalCoefficient b R ell) (rationalCoefficient b R ell) := by
  rw [ProjectionSliceBound.form_eq_sum]
  rfl

noncomputable def rationalTrueForm (b : ℝ) (R : ℕ) (ell : P → ℕ) (j : Fin k) : ℝ :=
  restrictedForm (fun p => (ell p : ℝ))
    (fun s => ∏ p, LocalCharacterMatrix.deletionMask j (s p))
    (rationalCoefficient b R ell) (rationalCoefficient b R ell)

theorem rational_ideal_sub_error_le_true {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, k + 2 ≤ ell p) (j : Fin k) :
    rationalIdealForm b R ell j -
      energy (rationalCoefficient (k := k) b R ell) * ∑ p, 10 * (k : ℝ) ^ 2 / (ell p : ℝ) ^ 2 ≤
      rationalTrueForm b R ell j := by
  have hh := rational_true_ideal_difference_le hb R ell hell j
  rw [quadratic_eq_form, quadratic_eq_form, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, ← rationalIdealForm_eq_projection] at hh
  rw [true_form_eq_restricted ell (fun p => by
    exact_mod_cast (show k < ell p by have := hell p; omega)) j] at hh
  have hlow := (abs_le.mp hh).1
  change _ ≤ rationalTrueForm b R ell j - rationalIdealForm b R ell j at hlow
  linarith

end Erdos4.FGKMT
