import ErdosProblems.Erdos4.FGKMTProjectionSlices
import ErdosProblems.Erdos4.ProjectionReplacement

/-! Changing one local projection while preserving the exact rational coefficient energy. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open DivisorCoefficients DivisorSlices RestrictedProductNorm RestrictedTensor ProjectionReplacement

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

theorem norm_rational_block_difference_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (J : Finset P)
    (u : {p : P // p ∉ J} → Option (Fin k) → ℝ) (hu : ∀ p, ∑ a, u p a ^ 2 = 1)
    (M N : J → Option (Fin k) → Option (Fin k) → ℂ) :
    ‖ConductorSupport.tensorForm (rationalCoefficient b R ell)
        (mixedMatrix J M (fun p a c => (ProjectionKernel.kernel (u p) a c : ℂ))) -
      ConductorSupport.tensorForm (rationalCoefficient b R ell)
        (mixedMatrix J N (fun p a c => (ProjectionKernel.kernel (u p) a c : ℂ)))‖ ≤
      energy (rationalCoefficient (k := k) b R ell) *
        LocalFourier.weightedMatrixNorm (sliceFactor ell J)
          (fun a c => (∏ p : J, M p (a p) (c p)) - ∏ p : J, N p (a p) (c p)) := by
  have hinner (a c : J → Option (Fin k)) :
      (∑ x : {p : P // p ∉ J} → Option (Fin k),
        ∑ y : {p : P // p ∉ J} → Option (Fin k),
          (rationalCoefficient b R ell (join J a x) : ℂ) * (rationalCoefficient b R ell (join J c y) : ℂ) *
            ∏ p : {p : P // p ∉ J}, (ProjectionKernel.kernel (u p) (x p) (y p) : ℂ)) =
        (ProjectionSliceBound.form u (rationalSlice b R ell J a) (rationalSlice b R ell J c) : ℂ) := by
    rw [ProjectionSliceBound.form_eq_sum]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod, rationalSlice]
  rw [tensorForm_mixed, tensorForm_mixed]
  simp_rw [hinner]
  simp only [← Finset.sum_sub_distrib, ← sub_mul]
  exact norm_rational_slice_sum_le hb R ell hell J u hu _

theorem norm_rational_single_replacement_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p)
    (u : P → Option (Fin k) → ℝ) (hu : ∀ p, ∑ a, u p a ^ 2 = 1)
    (p : P) (t : Option (Fin k) → ℝ) :
    ‖quadratic (rationalCoefficient b R ell) (Function.update u p t) -
      quadratic (rationalCoefficient b R ell) u‖ ≤
        energy (rationalCoefficient (k := k) b R ell) *
          LocalFourier.weightedMatrixNorm (localWeight (ell p))
            (fun a c => (ProjectionKernel.kernel t a c : ℂ) - (ProjectionKernel.kernel (u p) a c : ℂ)) := by
  let outside : {q : P // q ∉ ({p} : Finset P)} → Option (Fin k) → ℝ := fun q => u q
  have hnew : (fun q a c => (ProjectionKernel.kernel (Function.update u p t q) a c : ℂ)) =
      mixedMatrix {p} (fun _ a c => (ProjectionKernel.kernel t a c : ℂ))
        (fun q a c => (ProjectionKernel.kernel (outside q) a c : ℂ)) := by
    funext q a c
    by_cases hq : q = p
    · subst q
      simp [mixedMatrix]
    · simp [mixedMatrix, hq, outside]
  have hold : (fun q a c => (ProjectionKernel.kernel (u q) a c : ℂ)) =
      mixedMatrix {p} (fun _ a c => (ProjectionKernel.kernel (u p) a c : ℂ))
        (fun q a c => (ProjectionKernel.kernel (outside q) a c : ℂ)) := by
    funext q a c
    by_cases hq : q = p
    · subst q
      simp [mixedMatrix]
    · simp [mixedMatrix, hq, outside]
  unfold quadratic
  rw [hnew, hold]
  have hh := norm_rational_block_difference_le hb R ell hell {p} outside (fun q => hu q)
    (fun _ a c => (ProjectionKernel.kernel t a c : ℂ))
    (fun _ a c => (ProjectionKernel.kernel (u p) a c : ℂ))
  rwa [singleton_matrixNorm_eq ell p (fun a c => (ProjectionKernel.kernel t a c : ℂ))
    (fun a c => (ProjectionKernel.kernel (u p) a c : ℂ))] at hh

end Erdos4.FGKMT
