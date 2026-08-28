import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeLinearizationNative
import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroFamily

/-!
# The actual elliptic cap section factors through the zero-γ family

After the proved whole-boundary gauge homotopy, the original cap section
has zero first-circle coordinate at every point.  Codrestriction gives a
genuine continuous map to the literal rank-three subfamily.  This yields
a homotopy and exact all-degree homology factorization for the original
global attaching coefficient, not only a fibrewise comparison.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticGaugeLinearization

open Elliptic Elliptic.HigherHomology SpecialPeriods SpecialPeriods.Triangle
open SpecialPeriods.EllipticFilling SpecialPeriods.Threefold.EllipticGeometry
open ThreefoldOverlapMappingTorus SingularMayerVietoris PeriodTorusHigherHomology
open EllipticCapProduct

local notation "Dsp" =>
  regularData specialPeriodMap specialPeriodMap_generator₁ specialPeriodMap_generator₂

/-- The actual zero-time section fibre has identically zero original first circle coordinate. -/
theorem capSectionFibre_zero_gamma (j : Kind) (y : ProductTorus 3) :
    GammaZero.fibreGamma (capSectionFibre j 0 y) = 0 := by
  obtain ⟨k, rfl⟩ := coordinateProjection_surjective 3 y
  rw [capSectionFibre_zero_coordinateProjection, GammaZero.fibreGamma_mkQ]
  simp only [Fin.cons_zero, AddCircle.coe_zero]

/-- Vanishing holds on every point of the original surface's actual mapping-torus model. -/
theorem familyGamma_linear_capSectionFromModel (j : Kind) (τ : ℝ)
    (q : mappingTorusModel j) :
    GammaZero.familyGamma Dsp (linearRegularBoundaryMap j τ (capSectionFromModel j q)) = 0 := by
  obtain ⟨⟨s, y⟩, rfl⟩ := MappingTorus.mk_surjective (fibreTorusHomeomorph j).symm q
  rw [linearRegularBoundaryMap_capSectionFromModel_mk, GammaZero.familyGamma_quotient]
  exact capSectionFibre_zero_gamma j y

/-- The whole actual original cap section lands in the zero-γ subfamily after linearization. -/
theorem familyGamma_linear_capSection (j : Kind) (τ : ℝ)
    (q : ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j) :
    GammaZero.familyGamma Dsp (linearRegularBoundaryMap j τ (capSection j q)) = 0 := by
  obtain ⟨x, rfl⟩ :=
    (surfaceMappingTorusHomeomorph j (specialLocalData j).centralPeriod).symm.surjective q
  exact familyGamma_linear_capSectionFromModel j τ x

/-- The literal codrestriction of the proved linearized cap section. -/
def capSectionGammaZeroMap (j : Kind) (τ : ℝ) :
    C(ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j, GammaZero.Space Dsp) :=
  GammaZero.lift Dsp ((linearRegularBoundaryMap j τ).comp (capSection j))
    (familyGamma_linear_capSection j τ)

/-- The factorization is an exact equality of continuous maps into the original family. -/
@[simp] theorem inclusion_comp_capSectionGammaZeroMap (j : Kind) (τ : ℝ) :
    (GammaZero.inclusion Dsp).comp (capSectionGammaZeroMap j τ) =
      (linearRegularBoundaryMap j τ).comp (capSection j) := rfl

/-- The same actual map with the original surface's mapping-torus model as source. -/
def capSectionGammaZeroFromModel (j : Kind) (τ : ℝ) :
    C(mappingTorusModel j, GammaZero.Space Dsp) :=
  (capSectionGammaZeroMap j τ).comp
    ((surfaceMappingTorusHomeomorph j (specialLocalData j).centralPeriod).symm : C(_, _))

/-- Its original real-cylinder coordinates are the literal zero-head subfamily quotient. -/
theorem capSectionGammaZeroFromModel_coordinateProjection
    (j : Kind) (τ s : ℝ) (k : FibreCoordinates) :
    capSectionGammaZeroFromModel j τ
        (MappingTorus.mk (fibreTorusHomeomorph j).symm (s, coordinateProjection 3 k)) =
      GammaZero.quotient Dsp (nativeShiftedBase j τ (-s), GammaZero.fibreMkQ k) := by
  apply Subtype.ext
  exact linearRegularBoundaryMap_capSectionFromModel_coordinateProjection j τ s k

/-- The original full attaching map on the original cap section is genuinely homotopic
to the map through the literal rank-three subfamily. -/
theorem boundaryRegular_capSection_homotopic_gammaZero (j : Kind) (τ : ℝ) :
    ((boundaryToRegularFamily (some j)).comp (capSection j)).Homotopic
      ((GammaZero.inclusion Dsp).comp (capSectionGammaZeroMap j τ)) := by
  rw [inclusion_comp_capSectionGammaZeroMap]
  exact (boundaryToRegularFamily_homotopic_linear j τ).comp
    (ContinuousMap.Homotopic.refl (capSection j))

/-- The actual native global coefficient on cap-section classes factors in every degree. -/
theorem boundaryRegularHomologyMap_capSection_factor (j : Kind) (τ : ℝ) (n : ℕ) :
    (boundaryRegularHomologyMap (some j) n).comp (singularHomologyMap (capSection j) n) =
      (singularHomologyMap (GammaZero.inclusion Dsp) n).comp
        (singularHomologyMap (capSectionGammaZeroMap j τ) n) := by
  exact (singularHomologyMap_comp (capSection j) (boundaryToRegularFamily (some j)) n).symm.trans
    ((homotopic_homologyMap (boundaryRegular_capSection_homotopic_gammaZero j τ) n).trans
      (singularHomologyMap_comp (capSectionGammaZeroMap j τ) (GammaZero.inclusion Dsp) n))

/-- In particular, every actual cap-section class maps into the actual zero-γ homology image. -/
theorem boundaryRegularHomologyMap_capSection_mem_range (j : Kind) (τ : ℝ) (n : ℕ)
    (a : SingularHomology (ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j) n) :
    boundaryRegularHomologyMap (some j) n (singularHomologyMap (capSection j) n a) ∈
      LinearMap.range (singularHomologyMap (GammaZero.inclusion Dsp) n) := by
  refine ⟨singularHomologyMap (capSectionGammaZeroMap j τ) n a, ?_⟩
  exact (LinearMap.congr_fun (boundaryRegularHomologyMap_capSection_factor j τ n) a).symm

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticGaugeLinearization
