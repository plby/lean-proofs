import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusBasis
import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusBasisCurves
import Wikipedia.HopfProblem.CuspCentralHomologyMiddleAdmissible
import Mathlib.LinearAlgebra.StdBasis

/-!
# An integral basis from the three component spheres and the actual base torus

The first three vectors are the images of the oriented fundamental
classes of the three actual sphere parameterizations of the double
locus. The fourth is the top class of the actual embedded base-torus
section. The previous exact integral splitting proves that these four
specified classes, rather than arbitrary classes of the same rank,
form a basis of the original central fibre's second singular homology.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspCentralHomology

open Module ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)

/-- The actual ambient class of the indicated oriented component sphere. -/
def centralDoubleCurveH2Class (j : Fin 3) :
    SingularHomology (QuotientCentralFibre C r) 2 :=
  boundaryH2Inclusion C r hr
    (centralDoubleCurveFundamentalClass C r hr hr1 hC hR j)

/-- Integral coordinates assembled through the two genuine geometric
maps, with the three component coordinates first and the base coordinate last. -/
def baseTorusH2CoordinateAssembly :
    (Fin 4 → ℤ) ≃ₗ[ℤ] SingularHomology (QuotientCentralFibre C r) 2 :=
  ((middleIntegerFourEquiv.symm.toAddEquiv.trans
    (AddEquiv.prodCongr
      (centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR).symm.toAddEquiv
      baseTorusH2Marking.symm.toAddEquiv)).trans
        (baseTorusH2Split C r hr hr1 hC hR).toAddEquiv).toIntLinearEquiv

theorem baseTorusH2CoordinateAssembly_apply (v : Fin 4 → ℤ) :
    baseTorusH2CoordinateAssembly C r hr hr1 hC hR v =
      boundaryH2Inclusion C r hr
        ((centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR).symm
          ![v 0, v 1, v 2]) +
        baseTorusSectionHomologyMap C r hr 2 (baseTorusH2Marking.symm (v 3)) := rfl

theorem baseTorusH2CoordinateAssembly_first (j : Fin 3) :
    baseTorusH2CoordinateAssembly C r hr hr1 hC hR (Pi.single j.castSucc 1) =
      centralDoubleCurveH2Class C r hr hr1 hC hR j := by
  rw [baseTorusH2CoordinateAssembly_apply]
  have hfirst :
      (![ (Pi.single j.castSucc (1 : ℤ) : Fin 4 → ℤ) 0,
        (Pi.single j.castSucc (1 : ℤ) : Fin 4 → ℤ) 1,
        (Pi.single j.castSucc (1 : ℤ) : Fin 4 → ℤ) 2] : Fin 3 → ℤ) = Pi.single j 1 := by
    funext k
    fin_cases j <;> fin_cases k <;> simp
  have hlast : (Pi.single j.castSucc (1 : ℤ) : Fin 4 → ℤ) 3 = 0 := by
    fin_cases j <;> simp
  rw [hfirst, hlast, map_zero, map_zero, add_zero]
  have hclass : (centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR).symm
      (Pi.single j 1) = centralDoubleCurveFundamentalClass C r hr hr1 hC hR j := by
    apply (centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR).injective
    rw [LinearEquiv.apply_symm_apply, centralDoubleCurveFundamentalClass_coordinate]
  rw [hclass]
  rfl

theorem baseTorusH2CoordinateAssembly_last :
    baseTorusH2CoordinateAssembly C r hr hr1 hC hR (Pi.single 3 1) =
      baseTorusH2Class C r hr := by
  rw [baseTorusH2CoordinateAssembly_apply]
  change boundaryH2Inclusion C r hr
      ((centralBoundaryHomologyTwoEquiv C r hr hr1 hC hR).symm 0) +
        baseTorusSectionHomologyMap C r hr 2 (baseTorusH2Marking.symm 1) = _
  rw [map_zero, map_zero, zero_add]
  have htop : baseTorusH2Marking.symm 1 = productTorusTopClass 2 := by
    apply baseTorusH2Marking.injective
    rw [LinearEquiv.apply_symm_apply, baseTorusH2Marking_topClass]
  rw [htop]
  rfl

/-- The four specified geometric classes form an actual integral basis. -/
def baseTorusH2Basis : Basis (Fin 4) ℤ (SingularHomology (QuotientCentralFibre C r) 2) :=
  (Pi.basisFun ℤ (Fin 4)).map (baseTorusH2CoordinateAssembly C r hr hr1 hC hR)

theorem baseTorusH2Basis_apply (j : Fin 4) :
    baseTorusH2Basis C r hr hr1 hC hR j =
      baseTorusH2CoordinateAssembly C r hr hr1 hC hR (Pi.single j 1) := by
  rw [baseTorusH2Basis, Basis.map_apply, Pi.basisFun_apply]

@[simp] theorem baseTorusH2Basis_first (j : Fin 3) :
    baseTorusH2Basis C r hr hr1 hC hR j.castSucc =
      centralDoubleCurveH2Class C r hr hr1 hC hR j := by
  rw [baseTorusH2Basis_apply, baseTorusH2CoordinateAssembly_first]

@[simp] theorem baseTorusH2Basis_last :
    baseTorusH2Basis C r hr hr1 hC hR 3 = baseTorusH2Class C r hr := by
  rw [baseTorusH2Basis_apply, baseTorusH2CoordinateAssembly_last]

/-- The coordinate map dual to the displayed geometric basis. -/
def baseTorusH2Coordinates :
    SingularHomology (QuotientCentralFibre C r) 2 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (baseTorusH2CoordinateAssembly C r hr hr1 hC hR).symm

@[simp] theorem baseTorusH2Coordinates_curve (j : Fin 3) :
    baseTorusH2Coordinates C r hr hr1 hC hR
      (centralDoubleCurveH2Class C r hr hr1 hC hR j) = Pi.single j.castSucc 1 := by
  rw [← baseTorusH2CoordinateAssembly_first]
  exact (baseTorusH2CoordinateAssembly C r hr hr1 hC hR).symm_apply_apply _

@[simp] theorem baseTorusH2Coordinates_base :
    baseTorusH2Coordinates C r hr hr1 hC hR (baseTorusH2Class C r hr) =
      Pi.single 3 1 := by
  rw [← baseTorusH2CoordinateAssembly_last C r hr hr1 hC hR]
  exact (baseTorusH2CoordinateAssembly C r hr hr1 hC hR).symm_apply_apply _

end Wikipedia.HopfProblem.CuspCentralHomology
