import ErdosProblems.Erdos394.MinimalIntegralBasis
import ErdosProblems.Erdos394.SupNormReduction

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Realification of a reduced integral two-vector basis
-/

open Module
open scoped Matrix

namespace Erdos394

/-- Coordinatewise cast of an integer vector to a real vector. -/
def intVecToReal (x : Fin 2 → ℤ) : Fin 2 → ℝ := fun i ↦ (x i : ℝ)

@[simp] lemma intVecToReal_apply (x : Fin 2 → ℤ) (i : Fin 2) :
    intVecToReal x i = (x i : ℝ) := rfl

lemma supHeight2_intVecToReal (x : Fin 2 → ℤ) :
    supHeight2 (intVecToReal x) = (intSupHeight2 x : ℝ) := by
  simp only [supHeight2, intSupHeight2, intVecToReal_apply]
  push_cast
  rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]

/-- The real family obtained from two integer vectors of nonzero determinant
is a basis of `ℝ²`. -/
noncomputable def realBasisOfIntPair (u v : Fin 2 → ℤ)
    (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0) : Basis (Fin 2) ℝ (Fin 2 → ℝ) := by
  let w : Fin 2 → (Fin 2 → ℝ) := ![intVecToReal u, intVecToReal v]
  have hdetR : Matrix.det (Matrix.of w) ≠ 0 := by
    rw [Matrix.det_fin_two]
    norm_num [w, intVecToReal]
    exact_mod_cast hdet
  have hli : LinearIndependent ℝ w :=
    Matrix.linearIndependent_rows_of_det_ne_zero hdetR
  exact basisOfLinearIndependentOfCardEqFinrank' w hli (by simp)

@[simp] theorem realBasisOfIntPair_zero (u v : Fin 2 → ℤ)
    (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    realBasisOfIntPair u v hdet 0 = intVecToReal u := by
  simp [realBasisOfIntPair]

@[simp] theorem realBasisOfIntPair_one (u v : Fin 2 → ℤ)
    (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    realBasisOfIntPair u v hdet 1 = intVecToReal v := by
  simp [realBasisOfIntPair]

lemma realBasisOfIntPair_det (u v : Fin 2 → ℤ)
    (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    |(Pi.basisFun ℝ (Fin 2)).det
      ![realBasisOfIntPair u v hdet 0, realBasisOfIntPair u v hdet 1]| =
      ((u 0 * v 1 - u 1 * v 0).natAbs : ℝ) := by
  rw [realBasisOfIntPair_zero, realBasisOfIntPair_one, basisFun_det_pair]
  simp only [intVecToReal_apply]
  push_cast
  rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_sub,
    ← Int.cast_abs, ← Int.natCast_natAbs]
  norm_num

/-- The output conditions of `exists_supnorm_reduced_integral_basis` imply the
real reduced-pair bounds of F-045. -/
theorem reduced_integral_pair_real_bounds
    (u v : Fin 2 → ℤ) (L : ℕ)
    (hL : L = intSupHeight2 u) (hLpos : 0 < L)
    (hmin : L ≤ intSupHeight2 v)
    (hred : ((u 1).natAbs ≤ (u 0).natAbs ∧ 2 * (v 0).natAbs ≤ L) ∨
      ((u 0).natAbs ≤ (u 1).natAbs ∧ 2 * (v 1).natAbs ≤ L))
    (hdet : u 0 * v 1 - u 1 * v 0 ≠ 0) :
    let b := realBasisOfIntPair u v hdet
    let D : ℝ := ((u 0 * v 1 - u 1 * v 0).natAbs : ℝ)
    supHeight2 (b 1) ≤ D / (L : ℝ) + (L : ℝ) / 2 ∧
      (L : ℝ) ^ 2 ≤ 2 * D := by
  dsimp
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have huheight : supHeight2 (intVecToReal u) = (L : ℝ) := by
    rw [supHeight2_intVecToReal, hL]
  have hminR : (L : ℝ) ≤ supHeight2 (intVecToReal v) := by
    rw [supHeight2_intVecToReal]
    exact_mod_cast hmin
  rw [realBasisOfIntPair_one]
  rcases hred with ⟨hcoord, hvred⟩ | ⟨hcoord, hvred⟩
  · apply reduced_pair_bounds_coord_zero hLR huheight
    · have hcR : ((u 1).natAbs : ℝ) ≤ ((u 0).natAbs : ℝ) := by
        exact_mod_cast hcoord
      simpa [intVecToReal, Nat.cast_natAbs, Int.cast_abs] using hcR
    · simp only [intVecToReal_apply]
      rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_sub,
        ← Int.cast_abs, ← Int.natCast_natAbs]
      norm_num
    · have hvR : (2 : ℝ) * |(v 0 : ℝ)| ≤ (L : ℝ) := by
        rw [← Int.cast_abs, ← Int.natCast_natAbs]
        exact_mod_cast hvred
      change |(v 0 : ℝ)| ≤ (L : ℝ) / 2
      nlinarith
    · exact hminR
  · apply reduced_pair_bounds_coord_one hLR huheight
    · have hcR : ((u 0).natAbs : ℝ) ≤ ((u 1).natAbs : ℝ) := by
        exact_mod_cast hcoord
      simpa [intVecToReal, Nat.cast_natAbs, Int.cast_abs] using hcR
    · simp only [intVecToReal_apply]
      rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_sub,
        ← Int.cast_abs, ← Int.natCast_natAbs]
      norm_num
    · have hvR : (2 : ℝ) * |(v 1 : ℝ)| ≤ (L : ℝ) := by
        rw [← Int.cast_abs, ← Int.natCast_natAbs]
        exact_mod_cast hvred
      change |(v 1 : ℝ)| ≤ (L : ℝ) / 2
      nlinarith
    · exact hminR

end Erdos394
