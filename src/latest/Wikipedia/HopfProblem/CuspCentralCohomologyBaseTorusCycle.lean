import Wikipedia.HopfProblem.CuspCentralCohomologyBaseProjection
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationTwoSection

/-!
# The original base-period two-cycle specializes to the actual base section

The literal first-coordinate two-subtorus is the unit-phase section in
the original marked product. The actual marked collapse therefore sends
its positively normalized top class to the top class of the genuine
base-torus section, with no change of target generators.
-/

noncomputable section

open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open ToricSpace CuspRetraction CuspCentralHomology
open CuspCentralHomology.SpecializationModel SingularMayerVietoris
open PeriodTorusHigherHomology

theorem sourceProductCoordinateHomeomorph_baseSection (t : ProductTorus 2) :
    sourceProductCoordinateHomeomorph (productBaseSection t) = markedBaseInclusion t := by
  rw [productBaseSection_apply, sourceProductCoordinateHomeomorph_apply,
    compactFibreTorusHomeomorph_one]
  rfl

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)

/-- The actual unit-phase base section is preserved as an equality of maps. -/
theorem markedCollapse_comp_baseInclusion :
    (markedCollapse C r hr).comp markedBaseInclusion = baseTorusSection C r hr := by
  apply ContinuousMap.ext
  intro t
  change markedCollapse C r hr (markedBaseInclusion t) = baseTorusSection C r hr t
  rw [← sourceProductCoordinateHomeomorph_baseSection t]
  exact congrArg
    (fun f : C(CompactFibreTorus × ProductTorus 2, QuotientCentralFibre C r) =>
      f (productBaseSection t)) (markedCollapse_comp_productCoordinates C r hr)

theorem markedCollapse_baseInclusion_homology (n : ℕ) :
    (singularHomologyMap (markedCollapse C r hr) n).comp
      (singularHomologyMap markedBaseInclusion n) =
        baseTorusSectionHomologyMap C r hr n := by
  rw [← singularHomologyMap_comp, markedCollapse_comp_baseInclusion]

/-- The canonical first ordered-minor generator specializes to the
literal geometric base-torus top class with coefficient positive one. -/
theorem markedCollapse_baseCoordinateH2Class :
    singularHomologyMap (markedCollapse C r hr) 2
      (coordinateTorusH2Coordinates.symm (Pi.single 0 1)) = baseTorusH2Class C r hr := by
  have htop : coordinateTorusH2Coordinates.symm (Pi.single 0 1) =
      singularHomologyMap markedBaseInclusion 2 (productTorusTopClass 2) := by
    apply coordinateTorusH2Coordinates.injective
    rw [LinearEquiv.apply_symm_apply, markedBaseInclusion_topClass_coordinates]
  rw [htop]
  exact LinearMap.congr_fun (markedCollapse_baseInclusion_homology C r hr 2)
    (productTorusTopClass 2)

end Wikipedia.HopfProblem.CuspCentralCohomology
