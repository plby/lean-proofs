import ErdosProblems.Erdos4.FGKMTSieveCoefficients
import ErdosProblems.Erdos4.ProjectionSliceBound

/-! Exact conductor-slice control for the rational product-cutoff coefficients. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open DivisorCoefficients DivisorSlices RestrictedProductNorm

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

noncomputable def rationalSlice (b : ℝ) (R : ℕ) (ell : P → ℕ) (J : Finset P)
    (a : J → Option (Fin k)) (x : {p : P // p ∉ J} → Option (Fin k)) : ℝ :=
  rationalCoefficient b R ell (join J a x)

theorem abs_rationalSlice_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (J : Finset P)
    (a : J → Option (Fin k)) (x : {p : P // p ∉ J} → Option (Fin k)) :
    |rationalSlice b R ell J a x| ≤ sliceFactor ell J a * |rationalSlice b R ell J (fun _ => none) x| := by
  unfold rationalSlice
  rw [abs_of_nonneg (rationalCoefficient_nonneg hb R ell _),
    abs_of_nonneg (rationalCoefficient_nonneg hb R ell _)]
  have hh := rationalCoefficient_le_removedFactor_mul_erase hb R ell hell J (join J a x)
  rwa [erase_join, removedFactor_join] at hh

theorem sum_rationalSlice_energy (b : ℝ) (R : ℕ) (ell : P → ℕ) (J : Finset P) :
    (∑ a : J → Option (Fin k), energy (rationalSlice b R ell J a)) =
      energy (rationalCoefficient (k := k) b R ell) := by
  unfold energy rationalSlice
  exact sum_join J (fun a => rationalCoefficient b R ell a ^ 2)

theorem rationalSlice_energy_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (J : Finset P) (a : J → Option (Fin k)) :
    energy (rationalSlice b R ell J a) ≤ sliceFactor ell J a ^ 2 *
      energy (rationalCoefficient (k := k) b R ell) := by
  have hh := SliceBounds.slice_energy_le_total (rationalSlice b R ell J) (fun _ => none)
    (sliceFactor ell J) (sliceFactor_nonneg ell J) (abs_rationalSlice_le hb R ell hell J) a
  rwa [sum_rationalSlice_energy] at hh

theorem norm_rational_slice_sum_le {b : ℝ} (hb : 0 ≤ b) (R : ℕ)
    (ell : P → ℕ) (hell : ∀ p, 1 ≤ ell p) (J : Finset P)
    (u : {p : P // p ∉ J} → Option (Fin k) → ℝ) (hu : ∀ p, ∑ a, u p a ^ 2 = 1)
    (M : (J → Option (Fin k)) → (J → Option (Fin k)) → ℂ) :
    ‖∑ a, ∑ c, M a c *
      (ProjectionSliceBound.form u (rationalSlice b R ell J a) (rationalSlice b R ell J c) : ℂ)‖ ≤
        energy (rationalCoefficient (k := k) b R ell) *
          LocalFourier.weightedMatrixNorm (sliceFactor ell J) M :=
  ProjectionSliceBound.norm_matrix_sum_le u hu (rationalSlice b R ell J) (sliceFactor ell J) M
    (energy_nonneg _) (sliceFactor_nonneg ell J) (rationalSlice_energy_le hb R ell hell J)

end Erdos4.FGKMT
