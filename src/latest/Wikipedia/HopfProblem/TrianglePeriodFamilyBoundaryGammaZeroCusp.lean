import Wikipedia.HopfProblem.CuspBoundaryGammaZero
import Wikipedia.HopfProblem.TrianglePeriodFamilyGammaZeroFamily
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusCuspRegular
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusHomology

/-!
# The literal zero-γ cusp boundary maps into the zero-γ regular family

The original cusp coefficient keeps every real period coordinate
unchanged.  Consequently the actual restricted mapping torus maps
pointwise into the zero fibre of the original γ character.  Codrestriction
gives an exact continuous-map factorization, and hence a factorization on
actual singular homology in every degree.  No assertion concerning the
image of its top class in the cusp cap is needed or made here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspBoundaryGammaZero

open TrianglePeriodFamily SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology
open ThreefoldOverlapMappingTorus ThreefoldOverlapMappingTorus.Cusp

/-- The whole original cusp coefficient has zero γ on the literal restricted boundary. -/
theorem regularMap_gamma_zero (q : Boundary) :
    GammaZero.familyGamma boundaryRegularData
      (boundaryToRegularFamily none (boundaryMap q)) = 0 := by
  obtain ⟨⟨t, y⟩, rfl⟩ := MappingTorus.mk_surjective restrictedMonodromy q
  rw [boundaryMap_mk, boundaryToRegularFamily_cusp_mk, GammaZero.familyGamma_quotient,
    fibreMap_gamma]

/-- The genuine original map codrestricted to the literal rank-three subfamily. -/
def regularGammaZeroMap : C(Boundary, GammaZero.Space boundaryRegularData) :=
  GammaZero.lift boundaryRegularData ((boundaryToRegularFamily none).comp boundaryMap)
    regularMap_gamma_zero

/-- This is an exact map factorization, without any choice of homology class or splitting. -/
@[simp] theorem inclusion_comp_regularGammaZeroMap :
    (GammaZero.inclusion boundaryRegularData).comp regularGammaZeroMap =
      (boundaryToRegularFamily none).comp boundaryMap := rfl

/-- The factorization respects actual singular homology in every degree. -/
theorem boundaryRegularHomologyMap_gammaZero_factor (n : ℕ) :
    (boundaryRegularHomologyMap none n).comp (singularHomologyMap boundaryMap n) =
      (singularHomologyMap (GammaZero.inclusion boundaryRegularData) n).comp
        (singularHomologyMap regularGammaZeroMap n) := by
  have h := singularHomologyMap_comp regularGammaZeroMap
    (GammaZero.inclusion boundaryRegularData) n
  rw [inclusion_comp_regularGammaZeroMap] at h
  exact (singularHomologyMap_comp boundaryMap (boundaryToRegularFamily none) n).symm.trans h

/-- Every restricted-boundary class has its actual image in the zero-γ family homology image. -/
theorem boundaryRegularHomologyMap_gammaZero_mem_range (n : ℕ)
    (a : SingularHomology Boundary n) :
    boundaryRegularHomologyMap none n (singularHomologyMap boundaryMap n a) ∈
      LinearMap.range (singularHomologyMap (GammaZero.inclusion boundaryRegularData) n) := by
  refine ⟨singularHomologyMap regularGammaZeroMap n a, ?_⟩
  exact (LinearMap.congr_fun (boundaryRegularHomologyMap_gammaZero_factor n) a).symm

/-- The actual native `uwδ` Wang lift has this genuine regular-family factorization. -/
theorem nativeClass_regular_mem_range :
    boundaryRegularHomologyMap none 4 nativeClass ∈
      LinearMap.range (singularHomologyMap (GammaZero.inclusion boundaryRegularData) 4) :=
  boundaryRegularHomologyMap_gammaZero_mem_range 4 fundamentalClass

end Wikipedia.HopfProblem.CuspBoundaryGammaZero
