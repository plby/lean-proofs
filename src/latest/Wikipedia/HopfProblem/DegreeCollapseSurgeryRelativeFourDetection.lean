import Wikipedia.HopfProblem.DegreeCollapseSevenExteriorHomology
import Wikipedia.HopfProblem.DegreeCollapseIntegralSurgeryComplementPair
import Wikipedia.HopfProblem.DegreeCollapseIntegralRelativeEvaluationComparison
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainBasic
import Wikipedia.HopfProblem.SphereHomologyTop
import Wikipedia.NoExoticSixSphere.RelativeSingularExcision

/-!
# Integral evaluation detects actual relative fourth homology of a surgery pair

Excision moves the original exterior pair into the actual open tube.
Only that tube's fourth homology vanishes, since it retracts to S3.
The relative connecting map therefore embeds its fourth homology into
the actual punctured tube's H3, whose two sphere coordinates separate
classes. Original universal coefficient surjectivity then proves that
integral cohomology evaluations separate the original relative classes.
No vanishing or finiteness of the ambient homology is assumed.
-/

noncomputable section

open Function Set

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryRelativeFour

open Wikipedia.SmoothSixDPoincare NoExoticSixSphere
open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology SphereHomology
open SurgeryInteriorCoordinates SurgeryExteriorSequence

local instance : SimplyConnectedSpace (Sphere 3) := EuclideanSphere.simplyConnectedSpace 1
local instance (s : Sphere 3) : Subsingleton (HomotopyGroup (Fin 2) (Sphere 3) s) :=
  subsingleton_sphereHomotopyGroup (by decide) s

variable {R X Y : Type} [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X]
  (d : SurgeryBoundaryPair (EuclideanSpace ℝ (Fin 4)) (EuclideanSpace ℝ (Fin 4)) R X Y)

def interiorOverlapHomeomorph :
    RelativeSingularHomology.overlapIn (interiorSet d) d.OldComplement ≃ₜ overlapSet d :=
  (RelativeSingularHomology.overlapHomeomorph (interiorSet d) d.OldComplement).trans
    (Homeomorph.setCongr (inter_comm (interiorSet d) d.OldComplement))

omit [T2Space X] in
theorem interior_connecting_injective :
    Injective (RelativeSingularHomology.connecting
      (RelativeSingularHomology.overlapIn (interiorSet d) d.OldComplement) 3) := by
  let : Subsingleton (SingularHomology (Sphere 3) 4) :=
    unitSphere_homology_subsingleton 2 4 (by decide) (by decide)
  let : Subsingleton (SingularHomology (interiorSet d) 4) :=
    (coreHomologyEquiv d 4).surjective.subsingleton
  exact IntegralEmbeddingRange.connecting_injective _ 3

def relativeFourthCornerMap :
    RelativeSingularHomology.Homology (range d.oldExterior) 4 →ₗ[ℤ]
      SingularHomology (Sphere 3 × Sphere 3) 3 :=
  (overlapHomologyEquiv d 3).symm.toLinearMap.comp
    ((homeomorphHomologyEquiv (interiorOverlapHomeomorph d) 3).toLinearMap.comp
      ((RelativeSingularHomology.connecting
        (RelativeSingularHomology.overlapIn (interiorSet d) d.OldComplement) 3).comp
        ((RelativeSingularHomology.excisionEquiv (interiorSet d) d.OldComplement
          (isOpen_interiorSet d) (isOpen_coreComplement d)
          ((union_comm _ _).trans (complement_interior_cover d)) 4).symm.toLinearMap.comp
          (SurgeryExteriorRetraction.exteriorToComplement d 4))))

theorem relativeFourthCornerMap_injective : Injective (relativeFourthCornerMap d) :=
  (overlapHomologyEquiv d 3).symm.injective.comp
    ((homeomorphHomologyEquiv (interiorOverlapHomeomorph d) 3).injective.comp
      ((interior_connecting_injective d).comp
        ((RelativeSingularHomology.excisionEquiv (interiorSet d) d.OldComplement
          (isOpen_interiorSet d) (isOpen_coreComplement d)
          ((union_comm _ _).trans (complement_interior_cover d)) 4).symm.injective.comp
          (SurgeryExteriorRetraction.exteriorToComplement_bijective d 4).1)))

theorem relative_fourth_evaluation_ext
    (x y : RelativeSingularHomology.Homology (range d.oldExterior) 4)
    (h : ∀ a : Cohomology (RelativeSingularHomology.complex (range d.oldExterior)) 4,
      cohomologyEvaluation (RelativeSingularHomology.complex (range d.oldExterior)) 4 a x =
      cohomologyEvaluation (RelativeSingularHomology.complex (range d.oldExterior)) 4 a y) :
    x = y := by
  let K := RelativeSingularHomology.complex (range d.oldExterior)
  let (j : ℕ) : Module.Free ℤ (K.X j) := RelativeSingularHomology.chains_free _ j
  have hall (φ : K.homology 4 →ₗ[ℤ] ℤ) : φ x = φ y := by
    obtain ⟨a, ha⟩ := LocalEvaluation.cohomologyEvaluation_surjective K 4 φ
    rw [← ha]
    exact h a
  let e := ProductThirdHomology.equivalence (spherePole 3) (spherePole 3)
  let q := e.toAddMonoidHom.comp (relativeFourthCornerMap d).toAddMonoidHom
  let m := (unitSphereHomologyTopEquiv 2).toAddMonoidHom
  apply relativeFourthCornerMap_injective d
  apply e.injective
  apply Prod.ext
  · apply (unitSphereHomologyTopEquiv 2).injective
    exact hall (ConstantSheafSingularComparison.addHomToIntLinearMap
      (m.comp ((AddMonoidHom.fst (SingularHomology (Sphere 3) 3)
        (SingularHomology (Sphere 3) 3)).comp q)))
  · apply (unitSphereHomologyTopEquiv 2).injective
    exact hall (ConstantSheafSingularComparison.addHomToIntLinearMap
      (m.comp ((AddMonoidHom.snd (SingularHomology (Sphere 3) 3)
        (SingularHomology (Sphere 3) 3)).comp q)))

theorem generator_evaluation_injective
    (a : Cohomology (RelativeSingularHomology.complex (range d.oldExterior)) 4)
    (ha : ∀ b : Cohomology (RelativeSingularHomology.complex (range d.oldExterior)) 4,
      ∃ k : ℤ, k • a = b) :
    Injective (cohomologyEvaluation
      (RelativeSingularHomology.complex (range d.oldExterior)) 4 a) := by
  intro x y hxy
  apply relative_fourth_evaluation_ext d x y
  intro b
  obtain ⟨k, rfl⟩ := ha b
  simp only [map_zsmul, LinearMap.smul_apply, hxy]

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryRelativeFour
