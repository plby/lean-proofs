import ErdosProblems.Erdos4.ProjectionKernel
import ErdosProblems.Erdos4.DivisorSlices
import ErdosProblems.Erdos4.LocalFourier

/-!
# Coefficient slices with arbitrary projection products

The untouched coordinates may contain any unit-normal deletion
projections. Their product is contractive, so the actual divisor-slice
bounds control a local matrix inserted between them.
-/

open scoped BigOperators

namespace Erdos4.ProjectionSliceBound

open RestrictedProductNorm DivisorSlices

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

noncomputable def form (u : P → Option (Fin k) → ℝ)
    (v w : (P → Option (Fin k)) → ℝ) : ℝ :=
  ∑ a, v a * ProjectionKernel.action (ProjectionKernel.tensor u) w a

theorem form_eq_sum (u : P → Option (Fin k) → ℝ)
    (v w : (P → Option (Fin k)) → ℝ) :
    form u v w = ∑ a, ∑ b, v a * w b * ∏ p, ProjectionKernel.kernel (u p) (a p) (b p) := by
  unfold form ProjectionKernel.action ProjectionKernel.tensor
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  exact Finset.sum_congr rfl (fun b _hb => by ring)

theorem abs_form_le_scaled (u : P → Option (Fin k) → ℝ)
    (hu : ∀ p, ∑ a, u p a ^ 2 = 1) (v w : (P → Option (Fin k)) → ℝ)
    {a b N : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N)
    (hv : energy v ≤ a ^ 2 * N) (hw : energy w ≤ b ^ 2 * N) :
    |form u v w| ≤ a * b * N := by
  have hsq := ProjectionKernel.tensor_form_sq_le_energy u hu v w
  have hprod := mul_le_mul hv hw (energy_nonneg w) (mul_nonneg (sq_nonneg a) hN)
  have hrhs : (a ^ 2 * N) * (b ^ 2 * N) = (a * b * N) ^ 2 := by ring
  rw [hrhs] at hprod
  have hpositive : 0 ≤ a * b * N := mul_nonneg (mul_nonneg ha hb) hN
  have hh : form u v w ^ 2 ≤ (a * b * N) ^ 2 := hsq.trans hprod
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

theorem norm_matrix_sum_le {A : Type*} [Fintype A]
    (u : P → Option (Fin k) → ℝ) (hu : ∀ p, ∑ a, u p a ^ 2 = 1)
    (v : A → (P → Option (Fin k)) → ℝ) (c : A → ℝ) (M : A → A → ℂ)
    {N : ℝ} (hN : 0 ≤ N) (hc : ∀ a, 0 ≤ c a)
    (hv : ∀ a, energy (v a) ≤ c a ^ 2 * N) :
    ‖∑ a, ∑ b, M a b * (form u (v a) (v b) : ℂ)‖ ≤
      N * LocalFourier.weightedMatrixNorm c M := by
  have hterm (a b : A) : ‖M a b * (form u (v a) (v b) : ℂ)‖ ≤
      N * (‖M a b‖ * c a * c b) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hh := mul_le_mul_of_nonneg_left
      (abs_form_le_scaled u hu (v a) (v b) (hc a) (hc b) hN (hv a) (hv b)) (norm_nonneg (M a b))
    exact hh.trans_eq (by ring)
  calc
    _ ≤ ∑ a, ∑ b, ‖M a b * (form u (v a) (v b) : ℂ)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ha => norm_sum_le _ _))
    _ ≤ ∑ a, ∑ b, N * (‖M a b‖ * c a * c b) :=
      Finset.sum_le_sum (fun a _ha => Finset.sum_le_sum (fun b _hb => hterm a b))
    _ = _ := by simp only [LocalFourier.weightedMatrixNorm, Finset.mul_sum]

/-- Actual divisor coefficients, with no rectangular support assumption. -/
theorem norm_actual_slice_sum_le {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (J : Finset P)
    (u : {p : P // p ∉ J} → Option (Fin k) → ℝ) (hu : ∀ p, ∑ a, u p a ^ 2 = 1)
    (M : (J → Option (Fin k)) → (J → Option (Fin k)) → ℂ) :
    ‖∑ a, ∑ b, M a b * (form u (slice m R ell J a) (slice m R ell J b) : ℂ)‖ ≤
      energy (DivisorCoefficients.coefficient (k := k) m R ell) *
        LocalFourier.weightedMatrixNorm (sliceFactor ell J) M :=
  norm_matrix_sum_le u hu (slice m R ell J) (sliceFactor ell J) M
    (energy_nonneg _) (sliceFactor_nonneg ell J) (slice_energy_le hm hR ell hell J)

end Erdos4.ProjectionSliceBound
