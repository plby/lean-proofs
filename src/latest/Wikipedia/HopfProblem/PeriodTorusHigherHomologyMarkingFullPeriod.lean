import Wikipedia.HopfProblem.PeriodTorusHigherHomologyMarkingProductTorus
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeSurjectiveFullPeriod
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeFullPeriodCoordinates

/-!
# Canonical higher-homology markings for every full period torus

The actual products of positive period loops identify the second and third
integral singular homology with the exterior powers of the integral period
lattice, in the original order `(m₀,m₁,n₀,n₁)`. Surjectivity and matching
finite free ranks have already been proved from actual singular chains and
the circle-product Mayer--Vietoris calculation.

The resulting markings preserve the actual product-torus coordinate
homeomorphism and are natural for every continuous additive map with its
proved integral action on first homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris
open PeriodTorusHigherHomologyExterior PeriodTorusHigherHomologyPontryagin

/-- The actual full-period exterior-square map is an integral isomorphism. -/
theorem fullPeriodTorusWedgeTwo_bijective (q : FullPeriodMatrix) :
    Function.Bijective (fullPeriodTorusWedgeTwo q) := by
  let := q.singularHomology_free 2
  let := q.singularHomology_finite 2
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    (fullPeriodTorusWedgeTwo q) (fullPeriodTorusWedgeTwo_surjective q)
  rw [latticeExterior_finrank, q.singularHomology_finrank]

/-- The actual full-period exterior-cube map is an integral isomorphism. -/
theorem fullPeriodTorusWedgeThree_bijective (q : FullPeriodMatrix) :
    Function.Bijective (fullPeriodTorusWedgeThree q) := by
  let := q.singularHomology_free 3
  let := q.singularHomology_finite 3
  apply OrzechProperty.bijective_of_surjective_of_finrank_le
    (fullPeriodTorusWedgeThree q) (fullPeriodTorusWedgeThree_surjective q)
  rw [latticeExterior_finrank, q.singularHomology_finrank]

/-- Ordered products of positive periods identify the exterior square with actual `H₂`. -/
def fullPeriodTorusWedgeTwoEquiv (q : FullPeriodMatrix) :
    latticeExterior 2 ≃ₗ[ℤ] SingularHomology q.Torus 2 :=
  LinearEquiv.ofBijective (fullPeriodTorusWedgeTwo q) (fullPeriodTorusWedgeTwo_bijective q)

/-- Ordered products of positive periods identify the exterior cube with actual `H₃`. -/
def fullPeriodTorusWedgeThreeEquiv (q : FullPeriodMatrix) :
    latticeExterior 3 ≃ₗ[ℤ] SingularHomology q.Torus 3 :=
  LinearEquiv.ofBijective (fullPeriodTorusWedgeThree q) (fullPeriodTorusWedgeThree_bijective q)

@[simp] theorem fullPeriodTorusWedgeTwoEquiv_apply (q : FullPeriodMatrix)
    (v : latticeExterior 2) :
    fullPeriodTorusWedgeTwoEquiv q v = fullPeriodTorusWedgeTwo q v := rfl

@[simp] theorem fullPeriodTorusWedgeThreeEquiv_apply (q : FullPeriodMatrix)
    (v : latticeExterior 3) :
    fullPeriodTorusWedgeThreeEquiv q v = fullPeriodTorusWedgeThree q v := rfl

/-- The canonical exterior-square marking of actual full-period second singular homology. -/
def fullPeriodTorusH2ExteriorEquiv (q : FullPeriodMatrix) :
    SingularHomology q.Torus 2 ≃ₗ[ℤ] latticeExterior 2 :=
  (fullPeriodTorusWedgeTwoEquiv q).symm

/-- The canonical exterior-cube marking of actual full-period third singular homology. -/
def fullPeriodTorusH3ExteriorEquiv (q : FullPeriodMatrix) :
    SingularHomology q.Torus 3 ≃ₗ[ℤ] latticeExterior 3 :=
  (fullPeriodTorusWedgeThreeEquiv q).symm

@[simp] theorem fullPeriodTorusH2ExteriorEquiv_wedge (q : FullPeriodMatrix)
    (v : latticeExterior 2) :
    fullPeriodTorusH2ExteriorEquiv q (fullPeriodTorusWedgeTwo q v) = v :=
  (fullPeriodTorusWedgeTwoEquiv q).symm_apply_apply v

@[simp] theorem fullPeriodTorusH3ExteriorEquiv_wedge (q : FullPeriodMatrix)
    (v : latticeExterior 3) :
    fullPeriodTorusH3ExteriorEquiv q (fullPeriodTorusWedgeThree q v) = v :=
  (fullPeriodTorusWedgeThreeEquiv q).symm_apply_apply v

/-- The inverse square marking is the actual ordered product of the two positive period loops. -/
theorem fullPeriodTorusH2ExteriorEquiv_symm_ιMulti (q : FullPeriodMatrix)
    (v : Fin 2 → Lattice) :
    (fullPeriodTorusH2ExteriorEquiv q).symm (exteriorPower.ιMulti ℤ 2 v) =
      product11 q.Torus
        (loopHomologyClass (q.periodLoop
          (FullPeriodMatrix.integerCoordinatesEquiv.symm (v 0))))
        (loopHomologyClass (q.periodLoop
          (FullPeriodMatrix.integerCoordinatesEquiv.symm (v 1)))) :=
  fullPeriodTorusWedgeTwo_apply_ιMulti_periodLoops q v

/-- The inverse cubic marking is the actual ordered product of three positive period loops. -/
theorem fullPeriodTorusH3ExteriorEquiv_symm_ιMulti (q : FullPeriodMatrix)
    (v : Fin 3 → Lattice) :
    (fullPeriodTorusH3ExteriorEquiv q).symm (exteriorPower.ιMulti ℤ 3 v) =
      tripleProduct q.Torus
        (loopHomologyClass (q.periodLoop
          (FullPeriodMatrix.integerCoordinatesEquiv.symm (v 0))))
        (loopHomologyClass (q.periodLoop
          (FullPeriodMatrix.integerCoordinatesEquiv.symm (v 1))))
        (loopHomologyClass (q.periodLoop
          (FullPeriodMatrix.integerCoordinatesEquiv.symm (v 2)))) :=
  fullPeriodTorusWedgeThree_apply_ιMulti_periodLoops q v

/-- The actual marked degree-one action determines the exterior-square action. -/
theorem fullPeriodTorusH2ExteriorEquiv_natural (q r : FullPeriodMatrix)
    (f : C(q.Torus, r.Torus)) (hf : ∀ x y, f (x + y) = f x + f y)
    (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, singularHomologyMap f 1 (fullPeriodCoordinateH1 q v) =
      fullPeriodCoordinateH1 r (A v)) (a : SingularHomology q.Torus 2) :
    fullPeriodTorusH2ExteriorEquiv r (singularHomologyMap f 2 a) =
      exteriorPower.map 2 A (fullPeriodTorusH2ExteriorEquiv q a) := by
  obtain ⟨v, rfl⟩ := fullPeriodTorusWedgeTwo_surjective q a
  have h := LinearMap.congr_fun (fullPeriodTorusWedgeTwo_natural q r f hf A hmark) v
  change singularHomologyMap f 2 (fullPeriodTorusWedgeTwo q v) =
    fullPeriodTorusWedgeTwo r (exteriorPower.map 2 A v) at h
  rw [h, fullPeriodTorusH2ExteriorEquiv_wedge, fullPeriodTorusH2ExteriorEquiv_wedge]

/-- The actual marked degree-one action determines the exterior-cube action. -/
theorem fullPeriodTorusH3ExteriorEquiv_natural (q r : FullPeriodMatrix)
    (f : C(q.Torus, r.Torus)) (hf : ∀ x y, f (x + y) = f x + f y)
    (A : Lattice →ₗ[ℤ] Lattice)
    (hmark : ∀ v, singularHomologyMap f 1 (fullPeriodCoordinateH1 q v) =
      fullPeriodCoordinateH1 r (A v)) (a : SingularHomology q.Torus 3) :
    fullPeriodTorusH3ExteriorEquiv r (singularHomologyMap f 3 a) =
      exteriorPower.map 3 A (fullPeriodTorusH3ExteriorEquiv q a) := by
  obtain ⟨v, rfl⟩ := fullPeriodTorusWedgeThree_surjective q a
  have h := LinearMap.congr_fun (fullPeriodTorusWedgeThree_natural q r f hf A hmark) v
  change singularHomologyMap f 3 (fullPeriodTorusWedgeThree q v) =
    fullPeriodTorusWedgeThree r (exteriorPower.map 3 A v) at h
  rw [h, fullPeriodTorusH3ExteriorEquiv_wedge, fullPeriodTorusH3ExteriorEquiv_wedge]

/-- Actual full-period second homology in the ordered six-minor coordinates. -/
def fullPeriodTorusH2Coordinates (q : FullPeriodMatrix) :
    SingularHomology q.Torus 2 ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  (fullPeriodTorusH2ExteriorEquiv q).trans squareCoordinates

/-- Actual full-period third homology in the ordered four-minor coordinates. -/
def fullPeriodTorusH3Coordinates (q : FullPeriodMatrix) :
    SingularHomology q.Torus 3 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (fullPeriodTorusH3ExteriorEquiv q).trans cubeCoordinates

/-- The actual coordinate homeomorphism preserves the canonical square marking. -/
theorem coordinateTorusH2ExteriorEquiv_fullPeriodCoordinates (q : FullPeriodMatrix)
    (a : SingularHomology q.Torus 2) :
    coordinateTorusH2ExteriorEquiv
        (singularHomologyMap (q.productTorusHomeomorph : C(_, _)) 2 a) =
      fullPeriodTorusH2ExteriorEquiv q a := by
  obtain ⟨v, rfl⟩ := fullPeriodTorusWedgeTwo_surjective q a
  have h := LinearMap.congr_fun (fullPeriodTorusWedgeTwo_coordinates q) v
  change singularHomologyMap (q.productTorusHomeomorph : C(_, _)) 2
    (fullPeriodTorusWedgeTwo q v) = coordinateTorusWedgeTwo v at h
  rw [h, coordinateTorusH2ExteriorEquiv_wedge, fullPeriodTorusH2ExteriorEquiv_wedge]

/-- The actual coordinate homeomorphism preserves the canonical cubic marking. -/
theorem coordinateTorusH3ExteriorEquiv_fullPeriodCoordinates (q : FullPeriodMatrix)
    (a : SingularHomology q.Torus 3) :
    coordinateTorusH3ExteriorEquiv
        (singularHomologyMap (q.productTorusHomeomorph : C(_, _)) 3 a) =
      fullPeriodTorusH3ExteriorEquiv q a := by
  obtain ⟨v, rfl⟩ := fullPeriodTorusWedgeThree_surjective q a
  have h := LinearMap.congr_fun (fullPeriodTorusWedgeThree_coordinates q) v
  change singularHomologyMap (q.productTorusHomeomorph : C(_, _)) 3
    (fullPeriodTorusWedgeThree q v) = coordinateTorusWedgeThree v at h
  rw [h, coordinateTorusH3ExteriorEquiv_wedge, fullPeriodTorusH3ExteriorEquiv_wedge]

theorem coordinateTorusH2Coordinates_fullPeriodCoordinates (q : FullPeriodMatrix)
    (a : SingularHomology q.Torus 2) :
    coordinateTorusH2Coordinates
        (singularHomologyMap (q.productTorusHomeomorph : C(_, _)) 2 a) =
      fullPeriodTorusH2Coordinates q a :=
  congrArg squareCoordinates (coordinateTorusH2ExteriorEquiv_fullPeriodCoordinates q a)

theorem coordinateTorusH3Coordinates_fullPeriodCoordinates (q : FullPeriodMatrix)
    (a : SingularHomology q.Torus 3) :
    coordinateTorusH3Coordinates
        (singularHomologyMap (q.productTorusHomeomorph : C(_, _)) 3 a) =
      fullPeriodTorusH3Coordinates q a :=
  congrArg cubeCoordinates (coordinateTorusH3ExteriorEquiv_fullPeriodCoordinates q a)

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
