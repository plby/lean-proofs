import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Native analytic stereographic coordinates on the real two-sphere

These partial diffeomorphisms use the original stereographic atlas on the
Euclidean unit sphere. The change from the complex plane is the explicit
real-linear map that doubles the coordinates in the orthonormal basis `1, I`.
No topology or manifold structure is transported along a bijection.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealSphere

/-- The original three-dimensional real Euclidean space. -/
abbrev Ambient := EuclideanSpace ℝ (Fin 3)

/-- The unit two-sphere with its native subspace topology and stereographic atlas. -/
abbrev Sphere := Metric.sphere (0 : Ambient) 1

/-- The original two-dimensional real Euclidean model. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

instance ambientDimension : Fact (Module.finrank ℝ Ambient = 2 + 1) :=
  ⟨by simp [Ambient]⟩

/-- Stereographic projection is a chart of the unchanged native sphere atlas. -/
theorem stereographic_mem_atlas (v : Sphere) :
    stereographic' 2 v ∈ atlas Plane Sphere := by
  change ∃ w : Sphere, stereographic' 2 v = stereographic' 2 w
  exact ⟨v, rfl⟩

/-- The original stereographic projection, with its original inverse, is analytic. -/
def stereographicPartialDiffeomorph (v : Sphere) :
    PartialDiffeomorph (𝓡 2) (𝓡 2) Sphere Plane ω := by
  have he : stereographic' 2 v ∈ IsManifold.maximalAtlas (𝓡 2) ω Sphere :=
    IsManifold.subset_maximalAtlas (stereographic_mem_atlas v)
  exact {
    toPartialEquiv := (stereographic' 2 v).toPartialEquiv
    open_source := (stereographic' 2 v).open_source
    open_target := (stereographic' 2 v).open_target
    contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas he
    contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas he }

@[simp] theorem stereographicPartialDiffeomorph_apply (v x : Sphere) :
    stereographicPartialDiffeomorph v x = stereographic' 2 v x := rfl

@[simp] theorem stereographicPartialDiffeomorph_symm_apply (v : Sphere) (y : Plane) :
    (stereographicPartialDiffeomorph v).symm y = (stereographic' 2 v).symm y := rfl

@[simp] theorem stereographicPartialDiffeomorph_source (v : Sphere) :
    (stereographicPartialDiffeomorph v).source = {v}ᶜ :=
  stereographic'_source v

@[simp] theorem stereographicPartialDiffeomorph_target (v : Sphere) :
    (stereographicPartialDiffeomorph v).target = univ :=
  stereographic'_target v

@[simp] theorem stereographicPartialDiffeomorph_symm_source (v : Sphere) :
    (stereographicPartialDiffeomorph v).symm.source = univ :=
  stereographic'_target v

@[simp] theorem stereographicPartialDiffeomorph_symm_target (v : Sphere) :
    (stereographicPartialDiffeomorph v).symm.target = {v}ᶜ :=
  stereographic'_source v

/-- Antipodal negation is an analytic diffeomorphism for the native sphere atlas. -/
def antipodalDiffeomorph : Diffeomorph (𝓡 2) (𝓡 2) Sphere Sphere ω where
  toEquiv := {
    toFun := fun x => -x
    invFun := fun x => -x
    left_inv := neg_neg
    right_inv := neg_neg }
  contMDiff_toFun := contMDiff_neg_sphere
  contMDiff_invFun := contMDiff_neg_sphere

@[simp] theorem antipodalDiffeomorph_apply (x : Sphere) :
    antipodalDiffeomorph x = -x := rfl

@[simp] theorem antipodalDiffeomorph_symm_apply (x : Sphere) :
    antipodalDiffeomorph.symm x = -x := rfl

/-- Doubled orthonormal complex coordinates, with the explicit half-scaled inverse. -/
def doubledComplex : Diffeomorph 𝓘(ℝ, ℂ) (𝓡 2) ℂ Plane ω where
  toEquiv := {
    toFun := fun z => (2 : ℝ) • Complex.orthonormalBasisOneI.repr z
    invFun := fun y => (2 : ℝ)⁻¹ • Complex.orthonormalBasisOneI.repr.symm y
    left_inv := by
      intro z
      change (2 : ℝ)⁻¹ • Complex.orthonormalBasisOneI.repr.symm
        ((2 : ℝ) • Complex.orthonormalBasisOneI.repr z) = z
      rw [LinearIsometryEquiv.map_smul, LinearIsometryEquiv.symm_apply_apply, smul_smul]
      norm_num
    right_inv := by
      intro y
      change (2 : ℝ) • Complex.orthonormalBasisOneI.repr
        ((2 : ℝ)⁻¹ • Complex.orthonormalBasisOneI.repr.symm y) = y
      rw [LinearIsometryEquiv.map_smul, LinearIsometryEquiv.apply_symm_apply, smul_smul]
      norm_num }
  contMDiff_toFun :=
    (Complex.orthonormalBasisOneI.repr.contDiff.const_smul (2 : ℝ)).contMDiff
  contMDiff_invFun :=
    (Complex.orthonormalBasisOneI.repr.symm.contDiff.const_smul (2 : ℝ)⁻¹).contMDiff

@[simp] theorem doubledComplex_apply (z : ℂ) :
    doubledComplex z = (2 : ℝ) • Complex.orthonormalBasisOneI.repr z := rfl

@[simp] theorem doubledComplex_symm_apply (y : Plane) :
    doubledComplex.symm y =
      (2 : ℝ)⁻¹ • Complex.orthonormalBasisOneI.repr.symm y := rfl

/-- Inverse native stereographic projection in the doubled complex coordinates. -/
def complexStereographicParametrization (v : Sphere) :
    PartialDiffeomorph 𝓘(ℝ, ℂ) (𝓡 2) ℂ Sphere ω :=
  doubledComplex.toPartialDiffeomorph.trans (stereographicPartialDiffeomorph v).symm

@[simp] theorem complexStereographicParametrization_apply (v : Sphere) (z : ℂ) :
    complexStereographicParametrization v z =
      (stereographic' 2 v).symm
        ((2 : ℝ) • Complex.orthonormalBasisOneI.repr z) := rfl

@[simp] theorem complexStereographicParametrization_source (v : Sphere) :
    (complexStereographicParametrization v).source = univ := by
  ext z
  change (z ∈ (univ : Set ℂ) ∧ doubledComplex z ∈
    (stereographicPartialDiffeomorph v).symm.source) ↔ z ∈ univ
  simp only [stereographicPartialDiffeomorph_symm_source, mem_univ, and_self]

@[simp] theorem complexStereographicParametrization_target (v : Sphere) :
    (complexStereographicParametrization v).target = {v}ᶜ := by
  ext x
  change (x ∈ (stereographicPartialDiffeomorph v).symm.target ∧
    (stereographicPartialDiffeomorph v) x ∈ (univ : Set Plane)) ↔ x ∈ {v}ᶜ
  simp only [stereographicPartialDiffeomorph_symm_target, mem_univ, and_true]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealSphere
