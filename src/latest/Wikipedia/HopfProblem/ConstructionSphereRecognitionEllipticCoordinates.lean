import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusPolar

/-!
# Native disc rotations for the elliptic solid-torus model

All rotations act on the original open unit disc.  A continuous circle
coordinate on a fibre gives an explicit homeomorphism of the disc-fibre
product, with inverse the opposite rotation.  No smooth structure is
transported or inferred here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticModel

open SpecialPeriods ThreefoldOverlapMappingTorus

abbrev Circle := AddCircle (1 : ℝ)

/-- Multiplication by the actual unit phase, within the original disc. -/
def rotate (c : Circle) (s : Disc) : Disc :=
  discScalar (phase c : ℂ) (_root_.Circle.norm_coe _) s

@[simp] theorem rotate_val (c : Circle) (s : Disc) :
    (rotate c s : ℂ) = (phase c : ℂ) * s := rfl

@[simp] theorem rotate_zero (s : Disc) : rotate 0 s = s := by
  apply Subtype.ext
  simp only [rotate_val, phase_zero, _root_.Circle.coe_one, one_mul]

theorem rotate_add (a b : Circle) (s : Disc) :
    rotate (a + b) s = rotate a (rotate b s) := by
  apply Subtype.ext
  simp only [rotate_val, phase_add, _root_.Circle.coe_mul, mul_assoc]

@[simp] theorem rotate_neg_rotate (c : Circle) (s : Disc) :
    rotate (-c) (rotate c s) = s := by
  rw [← rotate_add, neg_add_cancel, rotate_zero]

@[simp] theorem rotate_rotate_neg (c : Circle) (s : Disc) :
    rotate c (rotate (-c) s) = s := by
  rw [← rotate_add, add_neg_cancel, rotate_zero]

@[simp] theorem rotate_norm (c : Circle) (s : Disc) :
    ‖(rotate c s : ℂ)‖ = ‖(s : ℂ)‖ := by
  rw [rotate_val, norm_mul, _root_.Circle.norm_coe, one_mul]

theorem rotate_continuous : Continuous (fun p : Circle × Disc => rotate p.1 p.2) :=
  ((continuous_subtype_val.comp (phase_continuous.comp continuous_fst)).mul
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- The native rotation has a continuous inverse, without choosing an argument. -/
def rotationHomeomorph (c : Circle) : Disc ≃ₜ Disc where
  toFun := rotate c
  invFun := rotate (-c)
  left_inv := rotate_neg_rotate c
  right_inv := rotate_rotate_neg c
  continuous_toFun := rotate_continuous.comp (continuous_const.prodMk continuous_id)
  continuous_invFun := rotate_continuous.comp (continuous_const.prodMk continuous_id)

@[simp] theorem rotationHomeomorph_apply (c : Circle) (s : Disc) :
    rotationHomeomorph c s = rotate c s := rfl

theorem rotate_real (c : ℝ) (s : Disc) :
    (rotate (c : Circle) s : ℂ) = CuspUniformization.exponential (c : ℂ) * s := by
  rw [rotate_val, phase_real]

/-- The base power formula retains the actual phase of the disc coordinate. -/
theorem rotate_pow (c : Circle) (s : Disc) (m : ℕ) :
    (rotate c s : ℂ) ^ m = (phase (m • c) : ℂ) * (s : ℂ) ^ m := by
  rw [rotate_val, mul_pow]
  congr 1
  change (AddCircle.toCircle c : ℂ) ^ m = (AddCircle.toCircle (m • c) : ℂ)
  rw [AddCircle.toCircle_nsmul, _root_.Circle.coe_pow]

variable {X : Type*} [TopologicalSpace X]

/-- Rotate the disc by a genuine continuous fibre coordinate, retaining the fibre point. -/
def untwist (χ : C(X, Circle)) : (Disc × X) ≃ₜ (Disc × X) where
  toFun p := (rotate (χ p.2) p.1, p.2)
  invFun p := (rotate (-χ p.2) p.1, p.2)
  left_inv p := Prod.ext (rotate_neg_rotate (χ p.2) p.1) rfl
  right_inv p := Prod.ext (rotate_rotate_neg (χ p.2) p.1) rfl
  continuous_toFun := (rotate_continuous.comp
    ((χ.continuous.comp continuous_snd).prodMk continuous_fst)).prodMk continuous_snd
  continuous_invFun := (rotate_continuous.comp
    ((χ.continuous.comp continuous_snd).neg.prodMk continuous_fst)).prodMk continuous_snd

@[simp] theorem untwist_apply (χ : C(X, Circle)) (p : Disc × X) :
    untwist χ p = (rotate (χ p.2) p.1, p.2) := rfl

@[simp] theorem untwist_symm_apply (χ : C(X, Circle)) (p : Disc × X) :
    (untwist χ).symm p = (rotate (-χ p.2) p.1, p.2) := rfl

@[simp] theorem untwist_norm (χ : C(X, Circle)) (p : Disc × X) :
    ‖((untwist χ p).1 : ℂ)‖ = ‖(p.1 : ℂ)‖ := rotate_norm _ _

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticModel
