import ErdosProblems.Erdos4.ProjectionSliceBound
import ErdosProblems.Erdos4.RestrictedTensor

/-!
# Replacing one local projection

Exact tensor splitting isolates one coordinate. The remaining product is
contractive, and the actual coefficient-slice estimate bounds the change
by the weighted entry norm of the local matrix difference.
-/

open scoped BigOperators

namespace Erdos4.ProjectionReplacement

open DivisorCoefficients DivisorSlices RestrictedProductNorm RestrictedTensor

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

noncomputable def quadratic (v : (P → Option (Fin k)) → ℝ)
    (u : P → Option (Fin k) → ℝ) : ℂ :=
  ConductorSupport.tensorForm v (fun p a b => (ProjectionKernel.kernel (u p) a b : ℂ))

theorem quadratic_eq_form (v : (P → Option (Fin k)) → ℝ)
    (u : P → Option (Fin k) → ℝ) :
    quadratic v u = (ProjectionSliceBound.form u v v : ℂ) := by
  rw [ProjectionSliceBound.form_eq_sum]
  simp only [quadratic, ConductorSupport.tensorForm,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod]

theorem norm_block_difference_le {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (J : Finset P)
    (u : {p : P // p ∉ J} → Option (Fin k) → ℝ) (hu : ∀ p, ∑ a, u p a ^ 2 = 1)
    (M N : J → Option (Fin k) → Option (Fin k) → ℂ) :
    ‖ConductorSupport.tensorForm (coefficient m R ell)
        (mixedMatrix J M (fun p a b => (ProjectionKernel.kernel (u p) a b : ℂ))) -
      ConductorSupport.tensorForm (coefficient m R ell)
        (mixedMatrix J N (fun p a b => (ProjectionKernel.kernel (u p) a b : ℂ)))‖ ≤
      energy (coefficient (k := k) m R ell) *
        LocalFourier.weightedMatrixNorm (sliceFactor ell J)
          (fun a b => (∏ p : J, M p (a p) (b p)) - ∏ p : J, N p (a p) (b p)) := by
  have hinner (a b : J → Option (Fin k)) :
      (∑ x : {p : P // p ∉ J} → Option (Fin k),
        ∑ y : {p : P // p ∉ J} → Option (Fin k),
          (coefficient m R ell (join J a x) : ℂ) * (coefficient m R ell (join J b y) : ℂ) *
            ∏ p : {p : P // p ∉ J}, (ProjectionKernel.kernel (u p) (x p) (y p) : ℂ)) =
        (ProjectionSliceBound.form u (slice m R ell J a) (slice m R ell J b) : ℂ) := by
    rw [ProjectionSliceBound.form_eq_sum]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_prod, slice]
  rw [tensorForm_mixed, tensorForm_mixed]
  simp_rw [hinner]
  simp only [← Finset.sum_sub_distrib, ← sub_mul]
  exact ProjectionSliceBound.norm_actual_slice_sum_le hm hR ell hell J u hu _

theorem singleton_matrixNorm_eq (ell : P → ℕ) (p : P)
    (M N : Option (Fin k) → Option (Fin k) → ℂ) :
    LocalFourier.weightedMatrixNorm (sliceFactor ell {p})
      (fun a b => (∏ q : ({p} : Finset P), M (a q) (b q)) -
        ∏ q : ({p} : Finset P), N (a q) (b q)) =
      LocalFourier.weightedMatrixNorm (localWeight (ell p)) (fun a b => M a b - N a b) := by
  let : Unique ({p} : Finset P) :=
    { default := ⟨p, Finset.mem_singleton_self p⟩
      uniq := fun q => Subtype.ext (Finset.mem_singleton.mp q.property) }
  let e := Equiv.funUnique ({p} : Finset P) (Option (Fin k))
  unfold LocalFourier.weightedMatrixNorm sliceFactor
  simp only [Fintype.prod_unique]
  have hinner (a : Option (Fin k)) :
      (∑ b : ({p} : Finset P) → Option (Fin k),
        ‖M a (b default) - N a (b default)‖ * localWeight (ell p) a * localWeight (ell p) (b default)) =
        ∑ b : Option (Fin k), ‖M a b - N a b‖ * localWeight (ell p) a * localWeight (ell p) b :=
    Equiv.sum_comp e (fun b => ‖M a b - N a b‖ * localWeight (ell p) a * localWeight (ell p) b)
  calc
    _ = ∑ a : ({p} : Finset P) → Option (Fin k), ∑ b : Option (Fin k),
        ‖M (a default) b - N (a default) b‖ * localWeight (ell p) (a default) * localWeight (ell p) b := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact hinner (a default)
    _ = _ := Equiv.sum_comp e (fun a => ∑ b : Option (Fin k),
      ‖M a b - N a b‖ * localWeight (ell p) a * localWeight (ell p) b)

/-- The changed local normal need not be a unit vector for this estimate;
only the untouched projections are used in the contraction. -/
theorem norm_single_replacement_le {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p)
    (u : P → Option (Fin k) → ℝ) (hu : ∀ p, ∑ a, u p a ^ 2 = 1)
    (p : P) (t : Option (Fin k) → ℝ) :
    ‖quadratic (coefficient m R ell) (Function.update u p t) - quadratic (coefficient m R ell) u‖ ≤
      energy (coefficient (k := k) m R ell) *
        LocalFourier.weightedMatrixNorm (localWeight (ell p))
          (fun a b => (ProjectionKernel.kernel t a b : ℂ) - (ProjectionKernel.kernel (u p) a b : ℂ)) := by
  let outside : {q : P // q ∉ ({p} : Finset P)} → Option (Fin k) → ℝ := fun q => u q
  have hnew : (fun q a b => (ProjectionKernel.kernel (Function.update u p t q) a b : ℂ)) =
      mixedMatrix {p} (fun _ a b => (ProjectionKernel.kernel t a b : ℂ))
        (fun q a b => (ProjectionKernel.kernel (outside q) a b : ℂ)) := by
    funext q a b
    by_cases hq : q = p
    · subst q
      simp [mixedMatrix]
    · simp [mixedMatrix, hq, outside]
  have hold : (fun q a b => (ProjectionKernel.kernel (u q) a b : ℂ)) =
      mixedMatrix {p} (fun _ a b => (ProjectionKernel.kernel (u p) a b : ℂ))
        (fun q a b => (ProjectionKernel.kernel (outside q) a b : ℂ)) := by
    funext q a b
    by_cases hq : q = p
    · subst q
      simp [mixedMatrix]
    · simp [mixedMatrix, hq, outside]
  unfold quadratic
  rw [hnew, hold]
  have hh := norm_block_difference_le hm hR ell hell {p} outside (fun q => hu q)
    (fun _ a b => (ProjectionKernel.kernel t a b : ℂ))
    (fun _ a b => (ProjectionKernel.kernel (u p) a b : ℂ))
  rwa [singleton_matrixNorm_eq ell p (fun a b => (ProjectionKernel.kernel t a b : ℂ))
    (fun a b => (ProjectionKernel.kernel (u p) a b : ℂ))] at hh

end Erdos4.ProjectionReplacement
