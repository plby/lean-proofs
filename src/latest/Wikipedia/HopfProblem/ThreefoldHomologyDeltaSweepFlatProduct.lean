import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepFlat
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportTorus

/-!
# Ordered Pontryagin products in the actual flat torus

The genuine additive coordinate homeomorphism carries the actual Pontryagin
product to the product of the positive coordinate-loop classes.  The frozen
second-homology marking is the inverse of exactly this exterior-product map.
Its ordered coordinates are `01, 02, 03, 12, 13, 23`, so placing the positive
delta circle first gives negative signs in the `03`, `13`, and `23` entries.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep

open Elliptic TrianglePeriodFamily FirstHurewicz SingularMayerVietoris
open PeriodTorusHigherHomology PeriodTorusHigherHomologyExterior
open PeriodTorusHigherHomologyPontryagin LocalSystemMatrices

/-- The actual flat-torus product agrees with the actual exterior-square marking,
with the two input periods in the stated order. -/
theorem flat_product11_exterior (a b : Lattice) :
    FlatTorus.singularH2Equiv
      (product11 RealTorus₄ (FlatTorus.singularH1Equiv.symm a)
        (FlatTorus.singularH1Equiv.symm b)) =
      exteriorPower.ιMulti ℤ 2 ![a, b] := by
  rw [FlatTorus.singularH2Equiv_apply,
    product_natural _ flatTorusCircleHomeomorph_add 1,
    FlatTorus.coordinateH1_flatMarking, FlatTorus.coordinateH1_flatMarking]
  calc
    _ = coordinateTorusH2ExteriorEquiv
        (coordinateTorusWedgeTwo (exteriorPower.ιMulti ℤ 2 ![a, b])) :=
      congrArg coordinateTorusH2ExteriorEquiv
        (coordinateTorusWedgeTwo_apply_ιMulti ![a, b]).symm
    _ = _ := coordinateTorusH2ExteriorEquiv_wedge _

/-- The six ordered coordinates of the genuine product are the corresponding
two-by-two minors of its two marked input classes. -/
theorem flat_product11_coordinates (a b : Lattice) :
    FlatTorus.singularH2Coordinates
      (product11 RealTorus₄ (FlatTorus.singularH1Equiv.symm a)
        (FlatTorus.singularH1Equiv.symm b)) =
      ![a 0 * b 1 - a 1 * b 0,
        a 0 * b 2 - a 2 * b 0,
        a 0 * b 3 - a 3 * b 0,
        a 1 * b 2 - a 2 * b 1,
        a 1 * b 3 - a 3 * b 1,
        a 2 * b 3 - a 3 * b 2] := by
  rw [FlatTorus.singularH2Coordinates_apply, flat_product11_exterior]
  funext i
  rw [squareCoordinates_apply, squareBasis, Module.Basis.repr_reindex_apply]
  change ((Pi.basisFun ℤ (Fin 4)).exteriorPower 2).repr
    (exteriorPower.ιMulti ℤ 2 ![a, b]) (pairSubset i) = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [pairSubset_ordered, Module.Basis.coord_apply, Pi.basisFun_repr]
  fin_cases i <;> simp [pairIndices, Matrix.det_fin_two, mul_comm]

/-- The literal positive fourth lattice vector is the first product input,
which fixes the negative signs in the three delta-containing coordinates. -/
theorem flat_delta_product11_coordinates (v : Lattice) :
    FlatTorus.singularH2Coordinates
      (product11 RealTorus₄ (FlatTorus.singularH1Equiv.symm ![0, 0, 0, 1])
        (FlatTorus.singularH1Equiv.symm v)) =
      ![0, 0, -v 0, 0, -v 1, -v 2] := by
  rw [flat_product11_coordinates]
  simp

/-- The actual positive delta-circle loop gives the same ordered coordinates
under its actual singular-homology map and the actual Pontryagin product. -/
theorem deltaCircle_positiveLoop_product_coordinates (v : Lattice) :
    FlatTorus.singularH2Coordinates
      (product11 RealTorus₄
        (singularHomologyMap deltaCircle 1 (loopHomologyClass CirclePaths.positiveLoop))
        (FlatTorus.singularH1Equiv.symm v)) =
      ![0, 0, -v 0, 0, -v 1, -v 2] := by
  rw [deltaCircle_positiveLoop_singularHomology]
  exact flat_delta_product11_coordinates v

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.DeltaSweep
