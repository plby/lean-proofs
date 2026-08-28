import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricUnitaryModel
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Circle

/-!
# Determinant and normalization for symmetric unitary matrices

The determinant is the actual continuous map to the complex unit circle.
A specified real argument of the determinant gives a continuous scalar
normalization into the symmetric special-unitary locus. No global choice
of argument, lifting theorem, or homotopy equivalence is assumed.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem norm_det_eq_one (B : Space N) : ‖B.val.val.det‖ = 1 := by
  have hu := Matrix.det_of_mem_unitary B.val.property
  have h := congrArg norm (Unitary.star_mul_self_of_mem hu)
  rw [norm_mul, norm_star, norm_one] at h
  nlinarith [norm_nonneg B.val.val.det]

def determinant : C(Space N, Circle) where
  toFun B := ⟨B.val.val.det, mem_sphere_zero_iff_norm.mpr (norm_det_eq_one B)⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp continuous_subtype_val).matrix_det).subtype_mk _

@[simp] theorem determinant_coe (B : Space N) : (determinant B : ℂ) = B.val.val.det := rfl

@[simp] theorem determinant_identity : determinant (identity : Space N) = 1 := by
  apply Circle.ext
  exact Matrix.det_one

def specialLocus (N : Type*) [Fintype N] [DecidableEq N] : Set (Space N) :=
  {B | determinant B = 1}

abbrev SpecialSpace (N : Type*) [Fintype N] [DecidableEq N] := specialLocus N

def specialIdentity : SpecialSpace N := ⟨identity, determinant_identity⟩

theorem isClosed_specialLocus : IsClosed (specialLocus N) :=
  isClosed_eq determinant.continuous continuous_const

private theorem circle_mem_unitary (z : Circle) : (z : ℂ) ∈ unitary ℂ := by
  apply Unitary.mem_iff_self_mul_star.mpr
  rw [Complex.star_def, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one]

/-- Scalar multiplication preserves both symmetry and unitarity. -/
def scale (z : Circle) (B : Space N) : Space N :=
  ⟨⟨(z : ℂ) • B.val.val, Unitary.smul_mem_of_mem (circle_mem_unitary z) B.val.property⟩,
    by rw [Matrix.transpose_smul, B.property]⟩

@[simp] theorem scale_one (B : Space N) : scale 1 B = B := by
  apply Subtype.ext
  apply Subtype.ext
  exact one_smul ℂ B.val.val

theorem scale_mul (z w : Circle) (B : Space N) : scale z (scale w B) = scale (z * w) B := by
  apply Subtype.ext
  apply Subtype.ext
  exact smul_smul (z : ℂ) (w : ℂ) B.val.val

theorem continuous_scale : Continuous (fun z : Circle × Space N ↦ scale z.1 z.2) := by
  have hz : Continuous (fun z : Circle × Space N ↦ (z.1 : ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  have hB : Continuous (fun z : Circle × Space N ↦ z.2.val.val) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact ((hz.smul hB).subtype_mk _).subtype_mk _

theorem determinant_scale (z : Circle) (B : Space N) :
    determinant (scale z B) = z ^ Fintype.card N * determinant B := by
  apply Circle.ext
  exact Matrix.det_smul B.val.val (z : ℂ)

/-- Normalize using a supplied real argument, in positive matrix rank. -/
def normalize (n : ℕ) (θ : ℝ) (B : Space (Fin (n + 1))) : Space (Fin (n + 1)) :=
  scale (Circle.exp (-θ / (n + 1 : ℝ))) B

theorem continuous_normalize (n : ℕ) :
    Continuous (fun z : ℝ × Space (Fin (n + 1)) ↦ normalize n z.1 z.2) :=
  continuous_scale.comp
    ((Circle.exp.continuous.comp (continuous_fst.neg.div_const _)).prodMk continuous_snd)

@[simp] theorem normalize_zero (n : ℕ) (B : Space (Fin (n + 1))) : normalize n 0 B = B := by
  simp [normalize, Circle.exp_zero]

theorem determinant_normalize (n : ℕ) (θ : ℝ) (B : Space (Fin (n + 1)))
    (hB : determinant B = Circle.exp θ) : determinant (normalize n θ B) = 1 := by
  rw [normalize, determinant_scale, hB, Fintype.card_fin, ← Circle.exp_natCast_mul,
    ← Circle.exp_add]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have he : (↑(n + 1) : ℝ) * (-θ / (n + 1 : ℝ)) + θ = 0 := by
    push_cast
    field_simp
    ring
  rw [he, Circle.exp_zero]

section Families

variable {X : Type*} [TopologicalSpace X]

def normalizedFamily (n : ℕ) (B : C(X, Space (Fin (n + 1)))) (θ : C(X, ℝ)) :
    C(X, Space (Fin (n + 1))) :=
  ⟨fun x ↦ normalize n (θ x) (B x),
    (continuous_normalize n).comp (θ.continuous.prodMk B.continuous)⟩

/-- A family with a continuous determinant argument normalizes into the actual fiber. -/
def normalizedSpecialFamily (n : ℕ) (B : C(X, Space (Fin (n + 1)))) (θ : C(X, ℝ))
    (hB : ∀ x, determinant (B x) = Circle.exp (θ x)) : C(X, SpecialSpace (Fin (n + 1))) :=
  ⟨fun x ↦ ⟨normalizedFamily n B θ x, determinant_normalize n (θ x) (B x) (hB x)⟩,
    (normalizedFamily n B θ).continuous.subtype_mk _⟩

/-- The deformation fixes every parameter where the chosen argument is zero. -/
def normalizationHomotopy (n : ℕ) (B : C(X, Space (Fin (n + 1)))) (θ : C(X, ℝ)) :
    B.HomotopyRel (normalizedFamily n B θ) {x | θ x = 0} where
  toFun z := normalize n ((z.1 : ℝ) * θ z.2) (B z.2)
  continuous_toFun := (continuous_normalize n).comp
    (((continuous_subtype_val.comp continuous_fst).mul (θ.continuous.comp continuous_snd)).prodMk
      (B.continuous.comp continuous_snd))
  map_zero_left x := by
    change normalize n ((0 : ℝ) * θ x) (B x) = B x
    rw [zero_mul, normalize_zero]
  map_one_left x := by
    change normalize n ((1 : ℝ) * θ x) (B x) = normalize n (θ x) (B x)
    rw [one_mul]
  prop' u x hx := by
    change normalize n ((u : ℝ) * θ x) (B x) = B x
    rw [hx, mul_zero, normalize_zero]

end Families

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
