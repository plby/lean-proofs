import Wikipedia.HopfProblem.ThreefoldHomologyCapEliminationClasses
import Wikipedia.HopfProblem.ThreefoldHomologyEllipticFibreKernel
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProductMarked
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticTopFibre

/-!
# The genuine fibre terms of the two elliptic cap-kernel axes

The positive first cap-kernel axes have Wang coordinates three and four
times the positive `uwδ` axis.  Their complete original boundary classes
are determined by these coordinates together with the actual cap maps.
The signed top fibre coefficients are retained, so no boundary splitting
or residual fibre coefficient is chosen.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthFibre

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology
open ThreefoldOverlapMappingTorus TrianglePeriodFamily
open TrianglePeriodFamily.Boundary.EllipticCapProduct
open TrianglePeriodFamily.Boundary.EllipticCapKernelWang
open TrianglePeriodFamily.Boundary.EllipticTopFibre
open Elliptic Elliptic.HigherHomology SpecialPeriods.EllipticFilling
open CapElimination Finiteness

/-- The positive generator in the unchanged original four-torus marking. -/
def positiveFibreClass : SingularHomology RealTorus₄ 4 := realTorusH4Equiv.symm 1

@[simp] theorem positiveFibreClass_coordinates : realTorusH4Equiv positiveFibreClass = 1 :=
  realTorusH4Equiv.apply_symm_apply 1

/-- The same original cap section, with the native global boundary type made explicit. -/
def nativeUnitCapSection (j : Kind) : SingularHomology (Boundary (some j)) 4 :=
  unitCapSectionClass j

@[simp] theorem nativeUnitCapSection_eq (j : Kind) :
    nativeUnitCapSection j = unitCapSectionClass j := rfl

/-- Genuine Wang exactness kills each literal fourth-degree fibre image. -/
theorem wang_three_fibre_four (i : Puncture) (a : SingularHomology RealTorus₄ 4) :
    wangBoundary (monodromy i) 3 (fibreHomologyMap (monodromy i) 4 a) = 0 := by
  have ha : fibreHomologyMap (monodromy i) 4 a ∈
      LinearMap.range (fibreHomologyMap (monodromy i) 4) := ⟨a, rfl⟩
  rw [wang_exact_at_mappingTorus (monodromy i) 3] at ha
  exact ha

/-- Joint detection fixes the complete boundary class of either first cap-kernel axis. -/
theorem ellipticFirstAxis_eq (j : Kind) :
    (ellipticThreeClass j ![1, 0]).val =
      γ j.twist • fibreHomologyMap (monodromy (some j)) 4 positiveFibreClass -
        (j.order : ℤ) • nativeUnitCapSection j := by
  apply EllipticFibre.boundaryFilling_four_wang_three_injective j
  apply Prod.ext
  · calc
      boundaryFillingHomologyMap (some j) 4 (ellipticThreeClass j ![1, 0]).val = 0 :=
        (ellipticThreeClass j ![1, 0]).property
      _ = boundaryFillingHomologyMap (some j) 4
          (γ j.twist • fibreHomologyMap (monodromy (some j)) 4 positiveFibreClass -
            (j.order : ℤ) • nativeUnitCapSection j) := by
        symm
        let c : SingularHomology (Boundary (some j)) 4 →ₗ[ℤ] ℤ :=
          (surfaceH4Equiv j (specialLocalData j).centralPeriod).toLinearMap.comp
            ((ellipticPieceRetractionHomologyEquiv j 4).toLinearMap.comp
              (boundaryFillingHomologyMap (some j) 4))
        have hf : c (fibreHomologyMap (monodromy (some j)) 4 positiveFibreClass) =
            (j.order : ℤ) * γ j.twist := by
          have h := boundaryFilling_fibre_h4_coordinates j positiveFibreClass
          rw [positiveFibreClass_coordinates, mul_one] at h
          exact h
        have hu : c (nativeUnitCapSection j) = 1 := unitCapSectionClass_filling j
        apply (ellipticPieceRetractionHomologyEquiv j 4).injective
        apply (surfaceH4Equiv j (specialLocalData j).centralPeriod).injective
        change c (_ - _) = _
        rw [map_zero, map_zero, map_sub, map_zsmul, map_zsmul, hf, hu]
        cases j <;> norm_num [Kind.order, Kind.twist, γ, ε, ε']
  · apply FlatTorus.singularH3Coordinates.injective
    let w : SingularHomology (Boundary (some j)) 4 →ₗ[ℤ] Lattice :=
      FlatTorus.singularH3Coordinates.toLinearMap.comp (wangBoundary (monodromy (some j)) 3)
    have hk : w (ellipticThreeClass j ![1, 0]).val =
        (j.order : ℤ) • ![0, 0, 0, 1] := capKernelWangH4Coordinates_first_axis j
    have hf : w (fibreHomologyMap (monodromy (some j)) 4 positiveFibreClass) = 0 :=
      (congrArg FlatTorus.singularH3Coordinates
        (wang_three_fibre_four (some j) positiveFibreClass)).trans
          FlatTorus.singularH3Coordinates.map_zero
    have hu : w (nativeUnitCapSection j) = -Pi.single (3 : Fin 4) 1 :=
      unitCapSectionClass_wang j
    change w _ = w (_ - _)
    rw [hk, map_sub, map_zsmul, map_zsmul, hf, hu]
    have haxis : (Pi.single (3 : Fin 4) (1 : ℤ) : Lattice) = ![0, 0, 0, 1] := by
      ext i
      fin_cases i <;> simp
    simp [haxis]

/-- The actual order-three kernel axis has positive unit fibre term. -/
theorem ellipticThreeFirstAxis_eq :
    (ellipticThreeClass .three ![1, 0]).val =
      fibreHomologyMap (monodromy (some Kind.three)) 4 positiveFibreClass -
        (3 : ℤ) • nativeUnitCapSection .three := by
  simpa [Kind.order, Kind.twist, γ, ε] using ellipticFirstAxis_eq .three

/-- The actual order-four kernel axis has negative unit fibre term. -/
theorem ellipticFourFirstAxis_eq :
    (ellipticThreeClass .four ![1, 0]).val =
      -fibreHomologyMap (monodromy (some Kind.four)) 4 positiveFibreClass -
        (4 : ℤ) • nativeUnitCapSection .four := by
  simpa [Kind.order, Kind.twist, γ, ε'] using ellipticFirstAxis_eq .four

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.FourthFibre
