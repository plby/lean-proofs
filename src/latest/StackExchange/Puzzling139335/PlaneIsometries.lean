import StackExchange.Puzzling139335.Definitions
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Coordinate classification of Euclidean plane isometries

An affine isometry of `Plane` has a translation term and an orthogonal
linear part.  In dimension two the linear part has one of the two familiar
matrix forms, including the orientation-reversing form.  The classification
is transported from Mathlib's proved classification of real-linear complex
isometries; it is not a hypothesis on the dissection.
-/

namespace Puzzling139335.PlaneIsometries

noncomputable section

open ComplexConjugate

/-- Euclidean coordinates identified isometrically with the complex plane. -/
def complexEquiv : Plane ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

@[simp] theorem complexEquiv_re (p : Plane) : (complexEquiv p).re = p 0 := by
  simp [complexEquiv]

@[simp] theorem complexEquiv_im (p : Plane) : (complexEquiv p).im = p 1 := by
  simp [complexEquiv]

/-- Equality of the two Euclidean coordinates implies equality of points. -/
theorem plane_ext {p q : Plane} (h₀ : p 0 = q 0) (h₁ : p 1 = q 1) : p = q := by
  ext i
  fin_cases i <;> assumption

/-- The linear part of an affine isometry, expressed in complex coordinates. -/
def linearInComplex (L : Plane ≃ₗᵢ[ℝ] Plane) : ℂ ≃ₗᵢ[ℝ] ℂ :=
  (complexEquiv.symm.trans L).trans complexEquiv

@[simp] theorem linearInComplex_apply (L : Plane ≃ₗᵢ[ℝ] Plane) (p : Plane) :
    linearInComplex L (complexEquiv p) = complexEquiv (L p) := by
  simp [linearInComplex]

/-- Every real-linear plane isometry is multiplication by a unit complex
number, possibly after complex conjugation. -/
theorem linear_complex_classification (L : Plane ≃ₗᵢ[ℝ] Plane) :
    ∃ a : Circle,
      (∀ p, complexEquiv (L p) = (a : ℂ) * complexEquiv p) ∨
      (∀ p, complexEquiv (L p) = (a : ℂ) * conj (complexEquiv p)) := by
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex (linearInComplex L)
  · refine ⟨a, Or.inl ?_⟩
    intro p
    simpa using LinearIsometryEquiv.congr_fun ha (complexEquiv p)
  · refine ⟨a, Or.inr ?_⟩
    intro p
    simpa using LinearIsometryEquiv.congr_fun ha (complexEquiv p)

/-- The translation term of an affine isometry is its value at the origin. -/
theorem affine_apply_eq_linear_add (e : Plane ≃ᵃⁱ[ℝ] Plane) (p : Plane) :
    e p = e.linearIsometryEquiv p + e 0 := by
  simpa using e.map_vadd (0 : Plane) p

/-- The complex-coordinate classification includes every affine isometry,
including reflections and glide reflections. -/
theorem affine_complex_classification (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    ∃ a : Circle,
      (∀ p, complexEquiv (e p) = (a : ℂ) * complexEquiv p + complexEquiv (e 0)) ∨
      (∀ p, complexEquiv (e p) =
        (a : ℂ) * conj (complexEquiv p) + complexEquiv (e 0)) := by
  obtain ⟨a, ha | ha⟩ := linear_complex_classification e.linearIsometryEquiv
  · refine ⟨a, Or.inl ?_⟩
    intro p
    rw [affine_apply_eq_linear_add, map_add, ha]
  · refine ⟨a, Or.inr ?_⟩
    intro p
    rw [affine_apply_eq_linear_add, map_add, ha]

/-- The coordinate formula with orientation-preserving linear part. -/
def directCoordinates (c s : ℝ) (t p : Plane) : Plane :=
  !₂[c * p 0 - s * p 1 + t 0, s * p 0 + c * p 1 + t 1]

/-- The coordinate formula with orientation-reversing linear part. -/
def reversingCoordinates (c s : ℝ) (t p : Plane) : Plane :=
  !₂[c * p 0 + s * p 1 + t 0, s * p 0 - c * p 1 + t 1]

/-- Exhaustive coordinate classification, with no orientation assumption. -/
theorem affine_coordinate_classification (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧
      ((∀ p, e p = directCoordinates c s (e 0) p) ∨
       (∀ p, e p = reversingCoordinates c s (e 0) p)) := by
  obtain ⟨a, ha | ha⟩ := affine_complex_classification e
  · refine ⟨(a : ℂ).re, (a : ℂ).im, ?_, Or.inl ?_⟩
    · simpa [pow_two, Complex.normSq_apply] using Circle.normSq_coe a
    · intro p
      apply plane_ext
      · simpa [directCoordinates, Complex.mul_re] using congrArg Complex.re (ha p)
      · simpa [directCoordinates, Complex.mul_im, add_comm] using congrArg Complex.im (ha p)
  · refine ⟨(a : ℂ).re, (a : ℂ).im, ?_, Or.inr ?_⟩
    · simpa [pow_two, Complex.normSq_apply] using Circle.normSq_coe a
    · intro p
      apply plane_ext
      · simpa [reversingCoordinates, Complex.mul_re] using congrArg Complex.re (ha p)
      · simpa [reversingCoordinates, Complex.mul_im, sub_eq_add_neg, add_comm]
          using congrArg Complex.im (ha p)

/-- The standard coordinate columns of the linear part. -/
def linearMatrix (e : Plane ≃ᵃⁱ[ℝ] Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => e.linearIsometryEquiv (EuclideanSpace.single j 1) i

/-- The columns of the linear matrix are orthonormal. -/
theorem linearMatrix_columns_orthonormal (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    Orthonormal ℝ (fun j : Fin 2 => e.linearIsometryEquiv (EuclideanSpace.single j 1)) := by
  exact (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 2)).comp_linearIsometryEquiv
    e.linearIsometryEquiv

/-- Every affine isometry's linear matrix is a rotation matrix or a
reflection matrix, with parameters on the unit circle. -/
theorem linearMatrix_classification (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧
      (linearMatrix e = !![c, -s; s, c] ∨ linearMatrix e = !![c, s; s, -c]) := by
  obtain ⟨c, s, hcs, he | he⟩ := affine_coordinate_classification e
  · refine ⟨c, s, hcs, Or.inl ?_⟩
    ext i j
    have h := congrArg (fun p : Plane => p i) (he (EuclideanSpace.single j 1))
    rw [affine_apply_eq_linear_add] at h
    fin_cases i <;> fin_cases j <;>
      simpa [linearMatrix, directCoordinates] using h
  · refine ⟨c, s, hcs, Or.inr ?_⟩
    ext i j
    have h := congrArg (fun p : Plane => p i) (he (EuclideanSpace.single j 1))
    rw [affine_apply_eq_linear_add] at h
    fin_cases i <;> fin_cases j <;>
      simpa [linearMatrix, reversingCoordinates] using h

/-- The unit-circle parameters can be written as the cosine and sine of an
angle in the usual principal range. -/
theorem exists_angle_of_sq_add_sq_eq_one {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ θ : ℝ, θ ∈ Set.Ioc (-Real.pi) Real.pi ∧ Real.cos θ = c ∧ Real.sin θ = s := by
  let z : ℂ := ⟨c, s⟩
  have hz : ‖z‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [← Complex.normSq_eq_norm_sq]
    simpa [Complex.normSq_apply, z, pow_two] using hcs
  refine ⟨z.arg, Complex.arg_mem_Ioc z, ?_, ?_⟩
  · simpa [hz, z] using Complex.norm_mul_cos_arg z
  · simpa [hz, z] using Complex.norm_mul_sin_arg z

/-- An angle form of the exhaustive classification. -/
theorem affine_angle_classification (e : Plane ≃ᵃⁱ[ℝ] Plane) :
    ∃ θ : ℝ, θ ∈ Set.Ioc (-Real.pi) Real.pi ∧
      ((∀ p, e p = directCoordinates (Real.cos θ) (Real.sin θ) (e 0) p) ∨
       (∀ p, e p = reversingCoordinates (Real.cos θ) (Real.sin θ) (e 0) p)) := by
  obtain ⟨c, s, hcs, he⟩ := affine_coordinate_classification e
  obtain ⟨θ, hθ, hc, hs⟩ := exists_angle_of_sq_add_sq_eq_one hcs
  exact ⟨θ, hθ, by simpa [hc, hs] using he⟩

end

end Puzzling139335.PlaneIsometries
