import Wikipedia.HopfProblem.EllipticHigherHomologyDeckHomology
import Wikipedia.HopfProblem.EllipticHigherHomologyDeckCoinvariantsAlgebra
import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusLowDegrees

/-!
# Coordinates on the actual elliptic deck coinvariants

The proved deck-action formula identifies the actual quotient by
`id - H(deck⁻¹)` with the product of adjacent actual Wang cokernels.
Their integral markings give two coordinates in degrees one through
three and one coordinate in degree four.  The representative formulas
keep the original period-torus homology and actual fibre inclusion.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology

/-- Coinvariants of the actual inverse deck generator on the original period torus. -/
abbrev PeriodDeckCoinvariants (j : Kind) (p : FixedPeriod j) (n : ℕ) :=
  SingularHomology p.val.Torus n ⧸ LinearMap.range (periodDeckDifference j p n)

/-- The actual circle splitting descends to the product of the two actual cokernels. -/
def periodDeckCoinvariantsEquivProd (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    PeriodDeckCoinvariants j p (n + 1) ≃ₗ[ℤ]
      ((SingularHomology (ProductTorus 3) (n + 1) ⧸
          LinearMap.range (wangDifference (fibreTorusHomeomorph j).symm (n + 1))) ×
        (SingularHomology (ProductTorus 3) n ⧸
          LinearMap.range (wangDifference (fibreTorusHomeomorph j).symm n))) :=
  ((conjugacyCokernelEquiv (periodCircleHomologyEquiv j p n)
    (periodDeckDifference j p (n + 1))
    (((wangDifference (fibreTorusHomeomorph j).symm (n + 1)).toAddMonoidHom.prodMap
      (wangDifference (fibreTorusHomeomorph j).symm n).toAddMonoidHom).toIntLinearMap)
    (periodCircleHomologyEquiv_periodDeckDifference j p n)).toAddEquiv.trans
    (prodCokernelEquiv (wangDifference (fibreTorusHomeomorph j).symm (n + 1))
      (wangDifference (fibreTorusHomeomorph j).symm n)).toAddEquiv).toIntLinearEquiv

@[simp] theorem periodDeckCoinvariantsEquivProd_mk (j : Kind) (p : FixedPeriod j)
    (n : ℕ) (a : SingularHomology p.val.Torus (n + 1)) :
    periodDeckCoinvariantsEquivProd j p n (Submodule.Quotient.mk a) =
      (Submodule.Quotient.mk (periodCircleHomologyEquiv j p n a).1,
        Submodule.Quotient.mk (periodCircleHomologyEquiv j p n a).2) := rfl

@[simp] theorem periodDeckCoinvariantsEquivProd_symm_mk
    (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularHomology (ProductTorus 3) (n + 1))
    (b : SingularHomology (ProductTorus 3) n) :
    (periodDeckCoinvariantsEquivProd j p n).symm
        (Submodule.Quotient.mk a, Submodule.Quotient.mk b) =
      Submodule.Quotient.mk ((periodCircleHomologyEquiv j p n).symm (a, b)) := rfl

/-- The two marked degree-one coinvariant coordinates. -/
def periodDeckCoinvariantsH1Equiv (j : Kind) (p : FixedPeriod j) :
    PeriodDeckCoinvariants j p 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((periodDeckCoinvariantsEquivProd j p 0).toAddEquiv.trans
    (((mappingTorusCokernelOneEquiv j).toAddEquiv.prodCongr
      (mappingTorusCokernelZeroEquiv j).toAddEquiv).trans
      (LinearEquiv.finTwoArrow ℤ ℤ).symm.toAddEquiv)).toIntLinearEquiv

/-- The two marked degree-two coinvariant coordinates. -/
def periodDeckCoinvariantsH2Equiv (j : Kind) (p : FixedPeriod j) :
    PeriodDeckCoinvariants j p 2 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((periodDeckCoinvariantsEquivProd j p 1).toAddEquiv.trans
    (((mappingTorusCokernelTwoEquiv j).toAddEquiv.prodCongr
      (mappingTorusCokernelOneEquiv j).toAddEquiv).trans
      (LinearEquiv.finTwoArrow ℤ ℤ).symm.toAddEquiv)).toIntLinearEquiv

/-- The two marked degree-three coinvariant coordinates. -/
def periodDeckCoinvariantsH3Equiv (j : Kind) (p : FixedPeriod j) :
    PeriodDeckCoinvariants j p 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((periodDeckCoinvariantsEquivProd j p 2).toAddEquiv.trans
    (((mappingTorusCokernelThreeEquiv j).toAddEquiv.prodCongr
      (mappingTorusCokernelTwoEquiv j).toAddEquiv).trans
      (LinearEquiv.finTwoArrow ℤ ℤ).symm.toAddEquiv)).toIntLinearEquiv

/-- Degree four has one coordinate, since the actual fibre has zero fourth homology. -/
def periodDeckCoinvariantsH4Equiv (j : Kind) (p : FixedPeriod j) :
    PeriodDeckCoinvariants j p 4 ≃ₗ[ℤ] ℤ := by
  have := productTorus_homology_subsingleton_of_lt (show 3 < 4 by decide)
  letI : Unique (SingularHomology (ProductTorus 3) 4 ⧸
      LinearMap.range (wangDifference (fibreTorusHomeomorph j).symm 4)) :=
    uniqueOfSubsingleton 0
  exact ((periodDeckCoinvariantsEquivProd j p 3).toAddEquiv.trans
    (AddEquiv.uniqueProd.trans (mappingTorusCokernelThreeEquiv j).toAddEquiv)).toIntLinearEquiv

@[simp] theorem periodDeckCoinvariantsH1Equiv_mk (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology p.val.Torus 1) :
    periodDeckCoinvariantsH1Equiv j p (Submodule.Quotient.mk a) =
      ![fibreCoinvariantCoordinate j (torusH1Equiv (periodCircleHomologyEquiv j p 0 a).1),
        torusH0Coordinates (periodCircleHomologyEquiv j p 0 a).2] := rfl

@[simp] theorem periodDeckCoinvariantsH2Equiv_mk (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology p.val.Torus 2) :
    periodDeckCoinvariantsH2Equiv j p (Submodule.Quotient.mk a) =
      ![torusH2Coordinates (periodCircleHomologyEquiv j p 1 a).1 0,
        fibreCoinvariantCoordinate j (torusH1Equiv (periodCircleHomologyEquiv j p 1 a).2)] := rfl

@[simp] theorem periodDeckCoinvariantsH3Equiv_mk (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology p.val.Torus 3) :
    periodDeckCoinvariantsH3Equiv j p (Submodule.Quotient.mk a) =
      ![torusH3Coordinates (periodCircleHomologyEquiv j p 2 a).1,
        torusH2Coordinates (periodCircleHomologyEquiv j p 2 a).2 0] := rfl

@[simp] theorem periodDeckCoinvariantsH4Equiv_mk (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology p.val.Torus 4) :
    periodDeckCoinvariantsH4Equiv j p (Submodule.Quotient.mk a) =
      torusH3Coordinates (periodCircleHomologyEquiv j p 3 a).2 := rfl

@[simp] theorem periodDeckCoinvariantsH1Equiv_fibre (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (ProductTorus 3) 1) :
    periodDeckCoinvariantsH1Equiv j p
        (Submodule.Quotient.mk (singularHomologyMap (fibreIntoPeriodTorus j p) 1 a)) =
      ![fibreCoinvariantCoordinate j (torusH1Equiv a), 0] := by
  simp only [periodDeckCoinvariantsH1Equiv_mk, periodCircleHomologyEquiv_fibre, map_zero]

@[simp] theorem periodDeckCoinvariantsH2Equiv_fibre (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (ProductTorus 3) 2) :
    periodDeckCoinvariantsH2Equiv j p
        (Submodule.Quotient.mk (singularHomologyMap (fibreIntoPeriodTorus j p) 2 a)) =
      ![torusH2Coordinates a 0, 0] := by
  simp only [periodDeckCoinvariantsH2Equiv_mk, periodCircleHomologyEquiv_fibre, map_zero]

@[simp] theorem periodDeckCoinvariantsH3Equiv_fibre (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (ProductTorus 3) 3) :
    periodDeckCoinvariantsH3Equiv j p
        (Submodule.Quotient.mk (singularHomologyMap (fibreIntoPeriodTorus j p) 3 a)) =
      ![torusH3Coordinates a, 0] := by
  simp only [periodDeckCoinvariantsH3Equiv_mk, periodCircleHomologyEquiv_fibre, map_zero,
    Pi.zero_apply]

@[simp] theorem periodDeckCoinvariantsH4Equiv_fibre (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (ProductTorus 3) 4) :
    periodDeckCoinvariantsH4Equiv j p
        (Submodule.Quotient.mk (singularHomologyMap (fibreIntoPeriodTorus j p) 4 a)) = 0 := by
  simp only [periodDeckCoinvariantsH4Equiv_mk, periodCircleHomologyEquiv_fibre, map_zero]

end Wikipedia.HopfProblem.Elliptic.HigherHomology
