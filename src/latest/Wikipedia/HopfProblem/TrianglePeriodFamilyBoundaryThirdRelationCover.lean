import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapKernelWang

/-!
# Actual elliptic covering representatives for the third-degree relation

The covering square and genuine shear invariance identify complete
boundary homology classes, before applying Wang.  In degree three this
gives finite-cover representatives for arbitrary integral combinations
of the two native split inputs, retaining the original surface shear.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation

open Elliptic Elliptic.HigherHomology SingularMayerVietoris PeriodTorusHigherHomology
open SpecialPeriods.EllipticFilling EllipticCapProduct EllipticCapKernelWang

/-- The literal covering square determines the entire actual boundary class,
not merely its Wang boundary. -/
theorem capCircle_surfaceCover_class (j : Kind) (n : ℕ) (hn : n = 1 ∨ n = 2)
    (a : SingularHomology RealTorus₄ n) :
    boundaryPositiveCircleCross j n (singularHomologyMap (surfaceCover j) n a) =
      singularHomologyMap (nativeProductCover j) (n + 1)
        (positiveCircleCross RealTorus₄ n a) := by
  rw [boundaryPositiveCircleCross_apply, ← positiveCircleCross_naturality]
  have hmap := congrArg
    (fun f : C(MappingTorus.Circle × RealTorus₄,
      ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary j) =>
        singularHomologyMap f (n + 1)) (nativeProductCover_comp_shear j)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at hmap
  have h := LinearMap.congr_fun hmap (positiveCircleCross RealTorus₄ n a)
  simpa only [LinearMap.comp_apply, nativeShear_positiveCircleCross j n hn a] using h.symm

/-- These source coordinates are the images of the actual two split covering classes. -/
theorem surfaceCover_two_combination (j : Kind) (p q : ℤ) :
    surfaceH2Equiv j (specialLocalData j).centralPeriod
        (singularHomologyMap (surfaceCover j) 2
          (p • splitFibreClassTwo j + q • splitCircleClassTwo j)) =
      ![p + q * sourceShearTwo j, q * (fibreNormIndex j : ℤ)] := by
  rw [map_add, map_zsmul, map_zsmul, map_add, map_zsmul, map_zsmul,
    surfaceCover_splitFibreClassTwo, surfaceCover_splitCircleClassTwo]
  ext i
  fin_cases i <;> simp

/-- The full native positive-circle class has its genuine finite-cover representative. -/
theorem capCircle_two_combination (j : Kind) (p q : ℤ) :
    boundaryPositiveCircleCross j 2
        ((surfaceH2Equiv j (specialLocalData j).centralPeriod).symm
          ![p + q * sourceShearTwo j, q * (fibreNormIndex j : ℤ)]) =
      singularHomologyMap (nativeProductCover j) 3
        (positiveCircleCross RealTorus₄ 2
          (p • splitFibreClassTwo j + q • splitCircleClassTwo j)) := by
  have h : (surfaceH2Equiv j (specialLocalData j).centralPeriod).symm
        ![p + q * sourceShearTwo j, q * (fibreNormIndex j : ℤ)] =
      singularHomologyMap (surfaceCover j) 2
        (p • splitFibreClassTwo j + q • splitCircleClassTwo j) := by
    apply (surfaceH2Equiv j (specialLocalData j).centralPeriod).injective
    rw [LinearEquiv.apply_symm_apply, surfaceCover_two_combination]
  rw [h]
  exact capCircle_surfaceCover_class j 2 (Or.inr rfl) _

/-- The order-three class uses four fibre pairs and twice the actual twist-circle pair. -/
theorem capCircle_three_reference :
    boundaryPositiveCircleCross .three 2
        ((surfaceH2Equiv .three (specialLocalData .three).centralPeriod).symm
          ![2 * sourceShearTwo .three + 4, 2]) =
      singularHomologyMap (nativeProductCover .three) 3
        (positiveCircleCross RealTorus₄ 2
          ((4 : ℤ) • splitFibreClassTwo .three + (2 : ℤ) • splitCircleClassTwo .three)) := by
  have h := capCircle_two_combination .three 4 2
  have h₀ : 4 + 2 * sourceShearTwo .three = 2 * sourceShearTwo .three + 4 := add_comm _ _
  have h₁ : (2 : ℤ) * (fibreNormIndex .three : ℤ) = 2 := by decide
  rw [h₀, h₁] at h
  exact h

/-- The order-four class uses three fibre pairs minus the actual twist-circle pair. -/
theorem capCircle_four_reference :
    boundaryPositiveCircleCross .four 2
        ((surfaceH2Equiv .four (specialLocalData .four).centralPeriod).symm
          ![3 - sourceShearTwo .four, -2]) =
      singularHomologyMap (nativeProductCover .four) 3
        (positiveCircleCross RealTorus₄ 2
          ((3 : ℤ) • splitFibreClassTwo .four - splitCircleClassTwo .four)) := by
  have h := capCircle_two_combination .four 3 (-1)
  simpa only [neg_one_mul, sub_eq_add_neg, fibreNormIndex_four, Nat.cast_ofNat,
    neg_one_zsmul] using h

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.ThirdRelation
