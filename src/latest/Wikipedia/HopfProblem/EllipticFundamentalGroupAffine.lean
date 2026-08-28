import Wikipedia.HopfProblem.EllipticArithmetic
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# The affine generators of the elliptic fundamental group

These are actual affine automorphisms of the real covering space. Their
multiplication is composition, with `(f * g) x = f (g x)`. The integral
translations and the affine lift of the elliptic twist satisfy the
conjugation and power relations used in the fundamental-group presentation.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic

/-- The group of affine automorphisms of the real four-dimensional cover. -/
abbrev AffineAutomorphism := RealCoordinates ≃ᵃ[ℝ] RealCoordinates

theorem matrix_pow_pred_mul (j : Kind) :
    j.matrix ^ (j.order - 1) * j.matrix = 1 := by
  rw [← pow_succ, Nat.sub_add_cancel j.order_pos, j.matrix_pow_order]

theorem matrix_mul_pow_pred (j : Kind) :
    j.matrix * j.matrix ^ (j.order - 1) = 1 := by
  rw [← pow_succ', Nat.sub_add_cancel j.order_pos, j.matrix_pow_order]

/-- Integral monodromy, with the inverse supplied by `A^(m-1)`. -/
def latticeMonodromy (j : Kind) : Lattice ≃+ Lattice where
  toFun w := j.matrix *ᵥ w
  invFun w := j.matrix ^ (j.order - 1) *ᵥ w
  left_inv w := by
    change j.matrix ^ (j.order - 1) *ᵥ (j.matrix *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, matrix_pow_pred_mul, Matrix.one_mulVec]
  right_inv w := by
    change j.matrix *ᵥ (j.matrix ^ (j.order - 1) *ᵥ w) = w
    rw [Matrix.mulVec_mulVec, matrix_mul_pow_pred, Matrix.one_mulVec]
  map_add' w z := Matrix.mulVec_add _ _ _

@[simp] theorem latticeMonodromy_apply (j : Kind) (w : Lattice) :
    latticeMonodromy j w = j.matrix *ᵥ w := rfl

@[simp] theorem latticeMonodromy_symm_apply (j : Kind) (w : Lattice) :
    (latticeMonodromy j).symm w = j.matrix ^ (j.order - 1) *ᵥ w := rfl

private theorem realMatrix_pow_pred_mul (j : Kind) :
    (j.matrix.map (Int.castRingHom ℝ)) ^ (j.order - 1) *
      j.matrix.map (Int.castRingHom ℝ) = 1 := by
  rw [← Matrix.map_pow, ← Matrix.map_mul, matrix_pow_pred_mul]
  simp

private theorem realMatrix_mul_pow_pred (j : Kind) :
    j.matrix.map (Int.castRingHom ℝ) *
      (j.matrix.map (Int.castRingHom ℝ)) ^ (j.order - 1) = 1 := by
  rw [← Matrix.map_pow, ← Matrix.map_mul, matrix_mul_pow_pred]
  simp

/-- The real linear part of the affine twist is invertible because its
`m`-th power is the identity. -/
def flatLinearEquiv (j : Kind) : RealCoordinates ≃ₗ[ℝ] RealCoordinates where
  __ := flatLinear j
  invFun x := (j.matrix.map (Int.castRingHom ℝ)) ^ (j.order - 1) *ᵥ x
  left_inv x := by
    change (j.matrix.map (Int.castRingHom ℝ)) ^ (j.order - 1) *ᵥ
      (j.matrix.map (Int.castRingHom ℝ) *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, realMatrix_pow_pred_mul, Matrix.one_mulVec]
  right_inv x := by
    change j.matrix.map (Int.castRingHom ℝ) *ᵥ
      ((j.matrix.map (Int.castRingHom ℝ)) ^ (j.order - 1) *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, realMatrix_mul_pow_pred, Matrix.one_mulVec]

@[simp] theorem flatLinearEquiv_apply (j : Kind) (x : RealCoordinates) :
    flatLinearEquiv j x = flatLinear j x := rfl

/-- The integral-coordinate inclusion as an additive homomorphism. -/
def realCastAddHom : Lattice →+ RealCoordinates where
  toFun := realCast
  map_zero' := by ext k; simp [realCast]
  map_add' w z := by ext k; simp [realCast]

/-- Integral translations, bundled as a group homomorphism. -/
def integerTranslationHom : Multiplicative Lattice →* AffineAutomorphism :=
  (AffineEquiv.constVAddHom ℝ RealCoordinates).comp realCastAddHom.toMultiplicative

/-- Translation by the lattice vector `w`, acting on the actual real cover. -/
def integerTranslation (w : Lattice) : AffineAutomorphism :=
  integerTranslationHom (Multiplicative.ofAdd w)

@[simp] theorem integerTranslationHom_apply (w : Multiplicative Lattice) :
    integerTranslationHom w = integerTranslation w.toAdd := rfl

@[simp] theorem integerTranslation_apply (w : Lattice) (x : RealCoordinates) :
    integerTranslation w x = realCast w + x := rfl

@[simp] theorem integerTranslation_zero : integerTranslation 0 = 1 :=
  integerTranslationHom.map_one

theorem integerTranslation_add (w z : Lattice) :
    integerTranslation (w + z) = integerTranslation w * integerTranslation z :=
  integerTranslationHom.map_mul (Multiplicative.ofAdd w) (Multiplicative.ofAdd z)

@[simp] theorem integerTranslation_neg (w : Lattice) :
    integerTranslation (-w) = (integerTranslation w)⁻¹ :=
  integerTranslationHom.map_inv (Multiplicative.ofAdd w)

theorem integerTranslation_injective : Function.Injective integerTranslation := by
  intro w z h
  have h0 := congrArg (fun f : AffineAutomorphism => f 0) h
  simp only [integerTranslation_apply, add_zero] at h0
  ext k
  have hk : (w k : ℝ) = (z k : ℝ) := congrFun h0 k
  exact_mod_cast hk

@[simp] theorem integerTranslation_eq_one_iff (w : Lattice) :
    integerTranslation w = 1 ↔ w = 0 := by
  rw [← integerTranslation_zero, integerTranslation_injective.eq_iff]

/-- The affine lift `x ↦ A x + v/m`, as an actual affine automorphism. -/
def affineGenerator (j : Kind) (v : Lattice) : AffineAutomorphism where
  toFun := flatAffine j v
  invFun x := (flatLinearEquiv j).symm (x - (1 / (j.order : ℝ)) • realCast v)
  left_inv x := by
    change (flatLinearEquiv j).symm
      ((flatLinearEquiv j x + (1 / (j.order : ℝ)) • realCast v) -
        (1 / (j.order : ℝ)) • realCast v) = x
    rw [add_sub_cancel_right, LinearEquiv.symm_apply_apply]
  right_inv x := by
    change flatLinearEquiv j
      ((flatLinearEquiv j).symm (x - (1 / (j.order : ℝ)) • realCast v)) +
        (1 / (j.order : ℝ)) • realCast v = x
    rw [LinearEquiv.apply_symm_apply, sub_add_cancel]
  linear := flatLinearEquiv j
  map_vadd' x w := by
    change flatLinear j (w + x) + (1 / (j.order : ℝ)) • realCast v =
      flatLinear j w + (flatLinear j x + (1 / (j.order : ℝ)) • realCast v)
    rw [map_add, add_assoc]

@[simp] theorem affineGenerator_apply (j : Kind) (v : Lattice) (x : RealCoordinates) :
    affineGenerator j v x = flatAffine j v x := rfl

theorem affineAutomorphism_mul_apply (f g : AffineAutomorphism) (x : RealCoordinates) :
    (f * g) x = f (g x) := rfl

/-- Powers of affine automorphisms use the same composition convention as
function iteration. -/
theorem affineAutomorphism_pow_apply (f : AffineAutomorphism) (n : ℕ)
    (x : RealCoordinates) : (f ^ n) x = (f : RealCoordinates → RealCoordinates)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', affineAutomorphism_mul_apply, ih, Function.iterate_succ_apply']

theorem affineAutomorphism_coe_pow (f : AffineAutomorphism) (n : ℕ) :
    (⇑(f ^ n) : RealCoordinates → RealCoordinates) =
      (f : RealCoordinates → RealCoordinates)^[n] :=
  funext (affineAutomorphism_pow_apply f n)

theorem affineGenerator_pow_apply (j : Kind) (v : Lattice) (n : ℕ)
    (x : RealCoordinates) :
    (affineGenerator j v ^ n) x = (flatAffine j v)^[n] x :=
  affineAutomorphism_pow_apply _ _ _

theorem affineGenerator_coe_pow (j : Kind) (v : Lattice) (n : ℕ) :
    (⇑(affineGenerator j v ^ n) : RealCoordinates → RealCoordinates) =
      (flatAffine j v)^[n] :=
  funext (affineGenerator_pow_apply j v n)

/-- Move an integral translation past the affine generator. -/
theorem affineGenerator_translation (j : Kind) (v w : Lattice) :
    affineGenerator j v * integerTranslation w =
      integerTranslation (j.matrix *ᵥ w) * affineGenerator j v := by
  ext x
  simp only [affineAutomorphism_mul_apply, affineGenerator_apply,
    integerTranslation_apply, flatAffine, map_add, flatLinear_realCast, add_assoc]

/-- Conjugation by the generator is precisely the integral monodromy. -/
theorem affineGenerator_conj_translation (j : Kind) (v w : Lattice) :
    affineGenerator j v * integerTranslation w * (affineGenerator j v)⁻¹ =
      integerTranslation (j.matrix *ᵥ w) := by
  rw [affineGenerator_translation, mul_assoc, mul_inv_cancel, mul_one]

/-- The `m`-th power of the affine generator is translation by `v`. -/
theorem affineGenerator_pow_order (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) :
    affineGenerator j v ^ j.order = integerTranslation v := by
  ext x
  rw [affineGenerator_pow_apply, flatAffine_iterate_order j v hv,
    integerTranslation_apply, add_comm]

/-- An arbitrary nonnegative power conjugates translations by `A^n`.
This identity does not require invariance of the twist vector. -/
theorem affineGenerator_pow_translation (j : Kind) (v w : Lattice) (n : ℕ) :
    affineGenerator j v ^ n * integerTranslation w =
      integerTranslation (j.matrix ^ n *ᵥ w) * affineGenerator j v ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      affineGenerator j v ^ (n + 1) * integerTranslation w =
          affineGenerator j v * (affineGenerator j v ^ n * integerTranslation w) := by
            rw [pow_succ', mul_assoc]
      _ = affineGenerator j v *
          (integerTranslation (j.matrix ^ n *ᵥ w) * affineGenerator j v ^ n) := by rw [ih]
      _ = (affineGenerator j v * integerTranslation (j.matrix ^ n *ᵥ w)) *
          affineGenerator j v ^ n := (mul_assoc _ _ _).symm
      _ = (integerTranslation (j.matrix *ᵥ (j.matrix ^ n *ᵥ w)) *
          affineGenerator j v) * affineGenerator j v ^ n := by
            rw [affineGenerator_translation]
      _ = integerTranslation (j.matrix ^ (n + 1) *ᵥ w) *
          affineGenerator j v ^ (n + 1) := by
            rw [mul_assoc, ← pow_succ', Matrix.mulVec_mulVec, ← pow_succ']

/-- All affine automorphisms of the real cover are continuous. -/
theorem affineAutomorphism_continuous (f : AffineAutomorphism) : Continuous f :=
  f.continuous_of_finiteDimensional

end Wikipedia.HopfProblem.Elliptic
