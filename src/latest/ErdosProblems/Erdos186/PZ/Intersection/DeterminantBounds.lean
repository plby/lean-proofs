/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Data.Real.Basic

/-!
# An anisotropic determinant bound

The progression-lattice estimate needs a column-sensitive version of the
elementary Leibniz bound.  If multiplying row `i` by `s i` bounds its entry
in column `j` by `t j`, then the determinant times `∏ i, s i` is bounded by
`d! * ∏ j, t j`.  Unlike a uniform max-norm estimate, this preserves the
volume cancellation between a progression and its containing box.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators
open Equiv Finset

set_option autoImplicit false

/-- Anisotropic Leibniz determinant bound over the reals. -/
theorem abs_det_mul_prod_le {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℝ) (s t : Fin d → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hentry : ∀ i j, s i * |A i j| ≤ t j) :
    |A.det| * (∏ i, s i) ≤
      (d.factorial : ℝ) * ∏ j, t j := by
  have hsprod : 0 ≤ ∏ i, s i := Finset.prod_nonneg fun i _ ↦ hs i
  rw [Matrix.det_apply]
  calc
    |∑ σ : Equiv.Perm (Fin d), Equiv.Perm.sign σ •
          ∏ i, A (σ i) i| * (∏ i, s i)
        ≤ (∑ σ : Equiv.Perm (Fin d),
            |Equiv.Perm.sign σ • ∏ i, A (σ i) i|) *
            (∏ i, s i) :=
      mul_le_mul_of_nonneg_right
        (Finset.abs_sum_le_sum_abs
          (fun σ : Equiv.Perm (Fin d) ↦
            Equiv.Perm.sign σ • ∏ i, A (σ i) i) Finset.univ)
        hsprod
    _ = ∑ σ : Equiv.Perm (Fin d),
          ((∏ i, |A (σ i) i|) * ∏ i, s i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      have habs :
          |Equiv.Perm.sign σ • ∏ i, A (σ i) i| =
            ∏ i, |A (σ i) i| := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
          simp [h, Finset.abs_prod]
      exact congrArg (fun u : ℝ ↦ u * ∏ i, s i) habs
    _ = ∑ σ : Equiv.Perm (Fin d),
          ∏ i, (s (σ i) * |A (σ i) i|) := by
      apply Finset.sum_congr rfl
      intro σ _
      calc
        (∏ i, |A (σ i) i|) * ∏ i, s i =
            (∏ i, |A (σ i) i|) * ∏ i, s (σ i) := by
          rw [Equiv.prod_comp]
        _ = ∏ i, (|A (σ i) i| * s (σ i)) := by
          rw [Finset.prod_mul_distrib]
        _ = ∏ i, (s (σ i) * |A (σ i) i|) := by
          apply Finset.prod_congr rfl
          intro i _
          ring
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), ∏ j, t j := by
      apply Finset.sum_le_sum
      intro σ _
      apply Finset.prod_le_prod
      · intro i _
        exact mul_nonneg (hs (σ i)) (abs_nonneg _)
      · intro i _
        exact hentry (σ i) i
    _ = (d.factorial : ℝ) * ∏ j, t j := by
      simp [Fintype.card_perm]

/-- Integer-matrix specialization, with the determinant reported by its
natural absolute value. -/
theorem natAbs_det_mul_prod_le {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℤ) (s t : Fin d → ℝ)
    (hs : ∀ i, 0 ≤ s i)
    (hentry : ∀ i j, s i * |(A i j : ℝ)| ≤ t j) :
    (A.det.natAbs : ℝ) * (∏ i, s i) ≤
      (d.factorial : ℝ) * ∏ j, t j := by
  let AR : Matrix (Fin d) (Fin d) ℝ := A.map (Int.castRingHom ℝ)
  have h := abs_det_mul_prod_le AR s t hs (by
    intro i j
    simpa [AR] using hentry i j)
  have hdet : AR.det = (A.det : ℝ) := by
    exact ((Int.castRingHom ℝ).map_det A).symm
  rw [hdet] at h
  simpa using h

end Erdos186.PZ.Intersection
