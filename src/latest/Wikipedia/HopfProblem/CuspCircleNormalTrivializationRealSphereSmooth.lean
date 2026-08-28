import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealSphereTopology
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealSphereStereo
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationGeometry

/-!
# The native real-analytic Riemann-sphere diffeomorphism

The explicit homeomorphism is locally a composition of the original
reciprocal affine sphere charts and the original Euclidean stereographic
charts. Both maps are therefore real analytic for the existing atlases.
-/

noncomputable section

open Set Topology Filter
open scoped ContDiff Manifold ComplexConjugate

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealSphere

/-- The finite rational parametrization is literally the original stereographic chart. -/
@[simp] theorem complexStereographicParametrization_north_apply (z : ℂ) :
    complexStereographicParametrization north z = left z := by
  rw [complexStereographicParametrization_apply]
  change stereoInvFun norm_northVector
    ((OrthonormalBasis.fromOrthogonalSpanSingleton 2 northVector_ne_zero).repr.symm
      ((2 : ℝ) • Complex.orthonormalBasisOneI.repr z)) = left z
  rw [map_smul]
  rfl

/-- Reflected conjugation is an explicit real-analytic involution of the complex plane. -/
def reflectedConjugation : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ω where
  toEquiv := {
    toFun := fun z => -conj z
    invFun := fun z => -conj z
    left_inv := by intro z; simp
    right_inv := by intro z; simp }
  contMDiff_toFun := Complex.conjCLE.contDiff.neg.contMDiff
  contMDiff_invFun := Complex.conjCLE.contDiff.neg.contMDiff

/-- The complementary rational chart with its actual native smooth inverse. -/
def rightPartialDiffeomorph :
    PartialDiffeomorph 𝓘(ℝ, ℂ) (𝓡 2) ℂ UnitTwoSphere ω :=
  reflectedConjugation.toPartialDiffeomorph.trans
    ((complexStereographicParametrization north).trans antipodalDiffeomorph.toPartialDiffeomorph)

@[simp] theorem rightPartialDiffeomorph_apply (z : ℂ) :
    rightPartialDiffeomorph z = right z := by
  change -(complexStereographicParametrization north (-conj z)) = right z
  rw [complexStereographicParametrization_north_apply]
  rfl

@[simp] theorem rightPartialDiffeomorph_source :
    rightPartialDiffeomorph.source = univ := by
  ext z
  change (z ∈ (univ : Set ℂ) ∧
    (reflectedConjugation z ∈ (complexStereographicParametrization north).source ∧
      complexStereographicParametrization north (reflectedConjugation z) ∈
        (univ : Set UnitTwoSphere))) ↔ z ∈ univ
  simp only [complexStereographicParametrization_source, mem_univ, and_self]

/-- The two actual real-analytic parametrizations of the Euclidean sphere. -/
def sphereParametrization (b : Bool) :
    PartialDiffeomorph 𝓘(ℝ, ℂ) (𝓡 2) ℂ UnitTwoSphere ω :=
  if b then rightPartialDiffeomorph else complexStereographicParametrization north

@[simp] theorem sphereParametrization_apply (b : Bool) (z : ℂ) :
    sphereParametrization b z = stereographicAffineCharts.affineMap b z := by
  cases b
  · exact complexStereographicParametrization_north_apply z
  · exact rightPartialDiffeomorph_apply z

@[simp] theorem sphereParametrization_source (b : Bool) :
    (sphereParametrization b).source = univ := by
  cases b <;> simp [sphereParametrization]

/-- Every native Riemann-sphere point lies in one of its original two affine charts. -/
theorem native_affine_chart_cover (p : RiemannSphere) :
    ∃ b z, RiemannSphere.standardCharts.affineMap b z = p := by
  obtain ⟨z, hz⟩ | ⟨z, hz⟩ := RiemannSphere.standardCharts.covered p
  · exact ⟨false, z, hz⟩
  · exact ⟨true, z, hz⟩

/-- The stereographic identification is a genuine local real-analytic diffeomorphism. -/
theorem sphereHomeomorph_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℝ, ℂ) (𝓡 2) ω sphereHomeomorph := by
  intro p
  obtain ⟨b, z, rfl⟩ := native_affine_chart_cover p
  let e := sphereChartPartialDiffeomorph b
  let g := sphereParametrization b
  have hz : z ∈ e.source := mem_univ z
  refine ⟨e.symm.trans g, ⟨e.map_source hz, ?_⟩, ?_⟩
  · change e.symm (RiemannSphere.standardCharts.affineMap b z) ∈
      (sphereParametrization b).source
    rw [sphereParametrization_source]
    exact mem_univ _
  · intro y hy
    have he : RiemannSphere.standardCharts.affineMap b (e.symm y) = y :=
      e.right_inv hy.1
    change sphereHomeomorph y = sphereParametrization b (e.symm y)
    rw [sphereParametrization_apply]
    calc
      sphereHomeomorph y = sphereHomeomorph
          (RiemannSphere.standardCharts.affineMap b (e.symm y)) :=
        congrArg sphereHomeomorph he.symm
      _ = stereographicAffineCharts.affineMap b (e.symm y) :=
        sphereHomeomorph_affineMap b _

/-- Forward real analyticity for the original reciprocal and stereographic atlases. -/
theorem sphereHomeomorph_contMDiff :
    ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) ω sphereHomeomorph :=
  sphereHomeomorph_isLocalDiffeomorph.contMDiff

/-- The actual inverse homeomorphism is real analytic in the unchanged native atlases. -/
theorem sphereHomeomorph_symm_contMDiff :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℂ) ω sphereHomeomorph.symm := by
  intro y
  let x := sphereHomeomorph.symm y
  have hx := sphereHomeomorph_isLocalDiffeomorph x
  have he : sphereHomeomorph x = y := sphereHomeomorph.apply_symm_apply y
  have hlocal : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ω hx.localInverse y := by
    rw [← he]
    exact hx.localInverse_contMDiffAt
  have hmem : y ∈ hx.localInverse.source := by
    rw [← he]
    exact hx.localInverse_mem_source
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [hx.localInverse.open_source.mem_nhds hmem] with z hz
  apply sphereHomeomorph.injective
  rw [sphereHomeomorph.apply_symm_apply, hx.localInverse_right_inv hz]

/-- The actual Riemann sphere is real-analytically diffeomorphic to the native unit two-sphere. -/
def sphereDiffeomorph :
    Diffeomorph 𝓘(ℝ, ℂ) (𝓡 2) RiemannSphere UnitTwoSphere ω where
  toEquiv := sphereHomeomorph.toEquiv
  contMDiff_toFun := sphereHomeomorph_contMDiff
  contMDiff_invFun := sphereHomeomorph_symm_contMDiff

@[simp] theorem sphereDiffeomorph_coe (z : ℂ) :
    sphereDiffeomorph (z : RiemannSphere) = left z := rfl

@[simp] theorem sphereDiffeomorph_infinity :
    sphereDiffeomorph (OnePoint.infty : RiemannSphere) = north :=
  sphereHomeomorph_infinity

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealSphere
