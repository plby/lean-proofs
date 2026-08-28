import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticTopFibreReflection
import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndicesTop
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTorusGroupsPeriod

/-!
# The signed top coordinate of the actual elliptic twist splitting

The first split coordinate follows the actual primitive twist.  It is
positive for the order-three twist and negative for the order-four twist.
The verified integral splitting and the actual reflected-circle homology
calculation give the exact sign relative to the common original ordered
four-period marking.  All other first-column shears are handled by the
proved actual circle-cover naturality calculation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticTopFibre

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology Homology

/-- The actual inverse twist basis acts on top homology with its original primitive sign. -/
theorem twistBasisInvMatrix_homology_four (j : Kind)
    (a : SingularHomology (ProductTorus 4) 4) :
    singularHomologyMap (torusMatrixMap (twistBasisInvMatrix j)) 4 a = γ j.twist • a := by
  cases j with
  | three =>
      have h := torusMatrixMap_homologyFour_of_det_one (twistBasisInvMatrix .three)
        (by intro i; fin_cases i <;> decide) (by decide)
      rw [h, LinearMap.id_apply]
      simp [γ, Kind.twist, ε]
  | four =>
      have hfirst : ∀ i, (twistBasisInvMatrix .four * headReflectionMatrix) 0 i =
          if i = 0 then 1 else 0 := by
        intro i
        fin_cases i <;> decide
      have hdet : (twistBasisInvMatrix .four * headReflectionMatrix).det = 1 := by decide
      have hfactor : (twistBasisInvMatrix .four * headReflectionMatrix) *
          headReflectionMatrix = twistBasisInvMatrix .four := by decide
      have h := torusMatrixMap_homologyFour_of_det_one
        (twistBasisInvMatrix .four * headReflectionMatrix) hfirst hdet
      rw [← hfactor, torusMatrixMap_mul, singularHomologyMap_comp,
        LinearMap.comp_apply, h, LinearMap.id_apply, headReflectionMatrix_homology_four]
      simp [γ, Kind.twist, ε']

/-- The actual recursive top coordinate on the coordinate four-torus. -/
def coordinateTopEquiv : SingularHomology (ProductTorus 4) 4 ≃ₗ[ℤ] ℤ :=
  (productTorusHomologyEquiv 4 4).trans (integerBinomialZeroEquiv 4).symm

@[simp] theorem coordinateTopEquiv_topClass :
    coordinateTopEquiv (productTorusTopClass 4) = 1 := by
  change productTorusHomologyEquiv 4 4 (productTorusTopClass 4) ⟨0, by decide⟩ = 1
  rw [productTorusHomologyEquiv_topClass]

/-- Every actual top class is its integral multiple of the proved positive top class. -/
theorem coordinateTopEquiv_smul_topClass (a : SingularHomology (ProductTorus 4) 4) :
    a = coordinateTopEquiv a • productTorusTopClass 4 := by
  apply coordinateTopEquiv.injective
  rw [map_zsmul, coordinateTopEquiv_topClass, zsmul_eq_mul, mul_one]
  simp only [Int.cast_id]

/-- The circle-boundary and recursive top markings have the same positive normalization. -/
theorem topDegreeTorusCoordinates_eq_coordinateTopEquiv
    (a : SingularHomology (ProductTorus 4) 4) :
    topDegreeTorusCoordinates a = coordinateTopEquiv a := by
  conv_lhs => rw [coordinateTopEquiv_smul_topClass a]
  rw [map_zsmul, topDegreeTorusCoordinates_topClass, zsmul_eq_mul, mul_one]
  simp only [Int.cast_id]

/-- Compatibility of the recursive marking with its literal flat-to-circle homeomorphism. -/
theorem coordinateTopEquiv_flat (a : SingularHomology RealTorus₄ 4) :
    coordinateTopEquiv (homeomorphHomologyEquiv flatTorusCircleHomeomorph 4 a) =
      realTorusH4Equiv a := by
  change productTorusHomologyEquiv 4 4
    (homeomorphHomologyEquiv flatTorusCircleHomeomorph 4 a) ⟨0, by decide⟩ =
      realTorusHomologyEquiv 4 a ⟨0, by decide⟩
  rw [realTorusHomologyEquiv_apply, homeomorphHomologyEquiv_apply]

/-- The signed actual circle-boundary coordinate of the original flat torus. -/
theorem splitFlatTorus_top_boundary (j : Kind) (a : SingularHomology RealTorus₄ 4) :
    torusH3Coordinates
        (circleBoundary (ProductTorus 3) 3
          (homeomorphHomologyEquiv (splitFlatTorusHomeomorph j) 4 a)) =
      γ j.twist * realTorusH4Equiv a := by
  rw [splitFlatTorusHomeomorph, homeomorphHomologyEquiv_trans,
    LinearEquiv.trans_apply, homeomorphHomologyEquiv_trans, LinearEquiv.trans_apply]
  change topDegreeTorusCoordinates
    (singularHomologyMap (torusMatrixMap (twistBasisInvMatrix j)) 4
      (homeomorphHomologyEquiv flatTorusCircleHomeomorph 4 a)) = _
  rw [twistBasisInvMatrix_homology_four, map_zsmul,
    topDegreeTorusCoordinates_eq_coordinateTopEquiv, zsmul_eq_mul,
    Int.cast_id, coordinateTopEquiv_flat]

/-- The period homeomorphism cancels exactly in the actual split map. -/
theorem splitPeriod_comp_flatPeriod (j : Kind) (p : PeriodDomain) :
    (splitPeriodTorusHomeomorph j p : C(p.Torus, AddCircle (1 : ℝ) × ProductTorus 3)).comp
        (flatTorusPeriodHomeomorph p : C(RealTorus₄, p.Torus)) =
      (splitFlatTorusHomeomorph j : C(RealTorus₄, AddCircle (1 : ℝ) × ProductTorus 3)) := by
  apply ContinuousMap.ext
  intro x
  change splitFlatTorusHomeomorph j
    ((flatTorusPeriodHomeomorph p).symm (flatTorusPeriodHomeomorph p x)) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- The circle boundary of the genuine period-cover input keeps the same
signed original real-period orientation. -/
theorem surfacePeriodCoverCircleBoundary_flat (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology RealTorus₄ 4) :
    torusH3Coordinates
        (surfacePeriodCoverCircleBoundary j p 3
          (homeomorphHomologyEquiv (flatTorusPeriodHomeomorph p.val) 4 a)) =
      γ j.twist * realTorusH4Equiv a := by
  rw [surfacePeriodCoverCircleBoundary_apply, homeomorphHomologyEquiv_apply,
    homeomorphHomologyEquiv_apply]
  have hc :
      (singularHomologyMap
        (splitPeriodTorusHomeomorph j p.val :
          C(p.val.Torus, AddCircle (1 : ℝ) × ProductTorus 3)) 4).comp
          (singularHomologyMap
            (flatTorusPeriodHomeomorph p.val : C(RealTorus₄, p.val.Torus)) 4) =
        singularHomologyMap
          (splitFlatTorusHomeomorph j : C(RealTorus₄, AddCircle (1 : ℝ) × ProductTorus 3)) 4 := by
    rw [← singularHomologyMap_comp, splitPeriod_comp_flatPeriod]
  exact (congrArg
    (fun b => torusH3Coordinates (circleBoundary (ProductTorus 3) 3 b))
      (LinearMap.congr_fun hc a)).trans (splitFlatTorus_top_boundary j a)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticTopFibre
