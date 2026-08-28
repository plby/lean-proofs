import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealSphereAlgebra

/-!
# The reciprocal two-chart homeomorphism onto the actual Euclidean sphere

These charts are used only to construct and identify the map. The smooth
structure on the target is always the original stereographic atlas.
-/

noncomputable section

open Set Metric
open scoped ComplexConjugate

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealSphere

/-- The second chart has the complementary rational stereographic formula. -/
theorem right_coe (z : ℂ) :
    (right z : SphereAmbient) =
      (2 / (Complex.normSq z + 1)) • (equatorEquiv (conj z) : SphereAmbient) +
      ((1 - Complex.normSq z) / (Complex.normSq z + 1)) • northVector := by
  change -(left (-conj z) : SphereAmbient) = _
  rw [left_coe]
  simp only [map_neg, Complex.normSq_neg, Complex.normSq_conj, Submodule.coe_neg]
  module

/-- Complex reciprocal followed by conjugation is real radial inversion. -/
theorem conjugate_inv (z : ℂ) :
    conj (z⁻¹) = (Complex.normSq z)⁻¹ • z := by
  rw [Complex.inv_def]
  simp [Complex.real_smul, mul_comm]

/-- The literal reciprocal transition of the two charts. -/
theorem left_eq_right_inv (z : ℂ) (hz : z ≠ 0) : left z = right z⁻¹ := by
  have hq : Complex.normSq z ≠ 0 := by simpa using hz
  have hd : Complex.normSq z + 1 ≠ 0 := by
    have := Complex.normSq_nonneg z
    positivity
  have hi : (Complex.normSq z)⁻¹ + 1 ≠ 0 := by
    have := Complex.normSq_nonneg z
    positivity
  have hd' : 1 + Complex.normSq z ≠ 0 := by
    have := Complex.normSq_nonneg z
    positivity
  apply Subtype.ext
  rw [left_coe, right_coe, Complex.normSq_inv, conjugate_inv]
  simp only [map_smul, Submodule.coe_smul, smul_smul]
  congr 1 <;> congr 1 <;> field_simp [hq, hd, hi, hd'] <;> ring

/-- The two actual stereographic parametrizations cover the sphere. -/
theorem left_right_cover (x : UnitTwoSphere) :
    (∃ z, left z = x) ∨ ∃ z, right z = x := by
  by_cases hx : x = north
  · exact Or.inr ⟨0, right_zero.trans hx.symm⟩
  · left
    refine ⟨equatorEquiv.symm ((2 : ℝ)⁻¹ • stereoToFun northVector x), ?_⟩
    change stereoInvFun norm_northVector
      ((2 : ℝ) • equatorEquiv
        (equatorEquiv.symm ((2 : ℝ)⁻¹ • stereoToFun northVector x))) = x
    rw [equatorEquiv.apply_symm_apply, smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
      one_smul]
    exact stereo_left_inv norm_northVector (fun h => hx (Subtype.ext h))

/-- A concrete two-affine-chart sphere, without installing a different atlas. -/
def stereographicAffineCharts : TwoAffineCharts UnitTwoSphere where
  left := left
  right := right
  continuous_left := left_continuous
  continuous_right := right_continuous
  left_injective := left_injective
  right_injective := right_injective
  inversion := left_eq_right_inv
  endpoints_ne := by
    rw [right_zero]
    exact left_ne_north 0
  covered := left_right_cover

/-- The explicit conformal stereographic homeomorphism. -/
def sphereHomeomorph : RiemannSphere ≃ₜ UnitTwoSphere :=
  stereographicAffineCharts.homeomorph

@[simp] theorem sphereHomeomorph_coe (z : ℂ) :
    sphereHomeomorph (z : RiemannSphere) = left z := rfl

@[simp] theorem sphereHomeomorph_infinity :
    sphereHomeomorph (OnePoint.infty : RiemannSphere) = north := right_zero

@[simp] theorem sphereHomeomorph_affineMap (b : Bool) (z : ℂ) :
    sphereHomeomorph (RiemannSphere.standardCharts.affineMap b z) =
      stereographicAffineCharts.affineMap b z :=
  congrFun (RiemannSphere.homeomorph_comp_standardCharts stereographicAffineCharts b) z

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealSphere
