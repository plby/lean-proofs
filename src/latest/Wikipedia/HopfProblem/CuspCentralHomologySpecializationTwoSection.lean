import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorusSection
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# The actual base section is in the specialization image

Including the marked base torus at unit compact phase and applying the
existing product collapse is exactly the constructed geometric base
section. Functoriality therefore places its integral singular-homology
image inside the specialization image in every degree.
-/

noncomputable section

open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction PeriodTorusHigherHomology SingularMayerVietoris
open SpecializationModel

/-- The literal marked base torus at unit compact fibre phase. -/
def productBaseSection : C(ProductTorus 2, CompactFibreTorus × ProductTorus 2) :=
  ⟨fun t => (1, t), continuous_const.prodMk continuous_id⟩

@[simp] theorem productBaseSection_apply (t : ProductTorus 2) :
    productBaseSection t = (1, t) := rfl

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)

/-- The actual geometric section factors through the original product collapse. -/
theorem productCollapse_comp_productBaseSection :
    (productCollapse C ε hε).comp productBaseSection = baseTorusSection C ε hε := rfl

/-- Functoriality retains the specified maps on actual integral singular homology. -/
theorem baseTorusSection_homology_factorization (n : ℕ) :
    singularHomologyMap (baseTorusSection C ε hε) n =
      (singularHomologyMap (productCollapse C ε hε) n).comp
        (singularHomologyMap productBaseSection n) := by
  rw [← productCollapse_comp_productBaseSection, singularHomologyMap_comp]

/-- Every class coming from the actual base section is in the image of
the actual product specialization, without analytic assumptions. -/
theorem baseTorusSection_homology_range_le_productCollapse (n : ℕ) :
    LinearMap.range (singularHomologyMap (baseTorusSection C ε hε) n) ≤
      LinearMap.range (singularHomologyMap (productCollapse C ε hε) n) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨singularHomologyMap productBaseSection n x, ?_⟩
  exact (LinearMap.congr_fun (baseTorusSection_homology_factorization C ε hε n) x).symm

theorem baseTorusSection_homologyTwo_range_le_productCollapse :
    LinearMap.range (singularHomologyMap (baseTorusSection C ε hε) 2) ≤
      LinearMap.range (singularHomologyMap (productCollapse C ε hε) 2) :=
  baseTorusSection_homology_range_le_productCollapse C ε hε 2

end Wikipedia.HopfProblem.CuspCentralHomology
