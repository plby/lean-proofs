import Wikipedia.HopfProblem.DegreeCollapseIntegralDualityHomeomorphicCopies
import Wikipedia.NoExoticSixSphere.AbsoluteSupportedHomology

/-!
# Actual integral cap duality on empty spaces

The original integer chains and cochains vanish because there are no
singular simplices. Their original class maps and the compact-to-absolute
comparison prove the empty case used in open-cover induction.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree NoExoticSixSphere

variable (X : Type) [TopologicalSpace X] [IsEmpty X]

theorem empty_homology_subsingleton (k : ℕ) : Subsingleton (SingularHomology X k) := by
  let : Subsingleton ((singularComplex X).X k) :=
    CoefficientChains.empty_subsingleton (ModuleCat.of ℤ ℤ) X k
  exact (ModuleHomology.cycleClass_surjective (singularComplex X) k).subsingleton

theorem empty_cohomology_subsingleton (p : ℕ) : Subsingleton (SingularCohomology X p) := by
  let : Subsingleton ((singularCochainComplex X).X p) := by
    refine ⟨fun a b => ?_⟩
    change Chains X p →ₗ[ℤ] ℤ at a b
    apply LinearMap.ext
    intro c
    have hc : c = 0 := (CoefficientChains.empty_subsingleton (ModuleCat.of ℤ ℤ) X p).elim c 0
    rw [hc, map_zero, map_zero]
  exact (cocycleClass_surjective (singularCochainComplex X) p).subsingleton

theorem empty_compactSupport_subsingleton (p : ℕ) :
    Subsingleton (IntegralCompactSupportCohomology.Cohomology X p) := by
  let := empty_cohomology_subsingleton X p
  exact (IntegralCompactSupportCohomology.absoluteEquiv X p).injective.subsingleton

theorem duality_of_isEmpty [T2Space X] (d : ℕ) : Duality d X := by
  refine ⟨?_, fun p _ => empty_compactSupport_subsingleton X p⟩
  intro c hc hp p q h
  let := empty_compactSupport_subsingleton X p
  let := empty_homology_subsingleton X q
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ b⟩⟩

theorem homeomorphicDuality_of_isEmpty (d : ℕ) : HomeomorphicDuality d X := by
  intro Y _ _ e
  let : IsEmpty Y := ⟨fun y => isEmptyElim (e y)⟩
  exact duality_of_isEmpty Y d

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCapDuality
