import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureExponentialCoordinates

/-!
# An actual local logarithm within the quaternionic complex-structure locus

The inverse-function theorem in the anticommuting model is composed with the
proved Cayley chart. On the stated open target its inverse is the original
exponential-step map, and both inverse identities are proved in the original
complex-structure space.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.LocalExponential

variable {n : ℕ}

def coordinateDiffeomorph (J : Space n) :
    PartialDiffeomorph 𝓘(ℝ, AntiSkewSpace J) 𝓘(ℝ, AntiSkewSpace J)
      (AntiSkewSpace J) (AntiSkewSpace J) ∞ :=
  Classical.choose (exists_coordinatePartialDiffeomorph J)

theorem zero_mem_coordinateDiffeomorph_source (J : Space n) :
    0 ∈ (coordinateDiffeomorph J).source :=
  (Classical.choose_spec (exists_coordinatePartialDiffeomorph J)).1

theorem coordinateDiffeomorph_source_subset (J : Space n) :
    (coordinateDiffeomorph J).source ⊆ coordinateDomain J :=
  (Classical.choose_spec (exists_coordinatePartialDiffeomorph J)).2.1

theorem coordinateDiffeomorph_apply (J : Space n) (K : AntiSkewSpace J) :
    coordinateDiffeomorph J K = inCoordinates J K :=
  congrFun (Classical.choose_spec (exists_coordinatePartialDiffeomorph J)).2.2 K

theorem zero_mem_coordinateDiffeomorph_target (J : Space n) :
    0 ∈ (coordinateDiffeomorph J).target := by
  have h := (coordinateDiffeomorph J).map_source' (zero_mem_coordinateDiffeomorph_source J)
  rwa [coordinateDiffeomorph_apply, inCoordinates_zero] at h

def logarithmChart (J : Space n) : OpenPartialHomeomorph (Space n) (AntiSkewSpace J) :=
  (Cayley.chart J).trans (coordinateDiffeomorph J).toOpenPartialHomeomorph.symm

theorem self_mem_logarithmChart_source (J : Space n) : J ∈ (logarithmChart J).source := by
  refine ⟨Cayley.self_mem_chart_source J, ?_⟩
  change Cayley.chart J J ∈ (coordinateDiffeomorph J).target
  rw [Cayley.chart_self]
  exact zero_mem_coordinateDiffeomorph_target J

theorem zero_mem_logarithmChart_target (J : Space n) :
    0 ∈ (logarithmChart J).target :=
  ⟨zero_mem_coordinateDiffeomorph_source J, mem_univ _⟩

theorem logarithmChart_target_subset (J : Space n) :
    (logarithmChart J).target ⊆ coordinateDomain J :=
  fun _ h ↦ coordinateDiffeomorph_source_subset J h.1

theorem logarithmChart_source_subset (J : Space n) :
    (logarithmChart J).source ⊆ Cayley.domain J := fun _ h ↦ h.1

theorem logarithmChart_symm_eq_step (J : Space n) (K : AntiSkewSpace J)
    (hK : K ∈ (logarithmChart J).target) :
    (logarithmChart J).symm K = exponentialStep J K := by
  change (Cayley.chart J).symm (coordinateDiffeomorph J K) = exponentialStep J K
  rw [coordinateDiffeomorph_apply,
    inCoordinates_eq_chart J K (logarithmChart_target_subset J hK)]
  exact (Cayley.chart J).left_inv (step_mem_domain J K (logarithmChart_target_subset J hK))

theorem step_logarithmChart (J J' : Space n) (h : J' ∈ (logarithmChart J).source) :
    exponentialStep J (logarithmChart J J') = J' :=
  (logarithmChart_symm_eq_step J _ ((logarithmChart J).map_source h)).symm.trans
    ((logarithmChart J).left_inv h)

theorem logarithmChart_step (J : Space n) (K : AntiSkewSpace J)
    (h : K ∈ (logarithmChart J).target) :
    logarithmChart J (exponentialStep J K) = K := by
  have he := (logarithmChart J).right_inv h
  rwa [logarithmChart_symm_eq_step J K h] at he

theorem logarithmChart_self (J : Space n) : logarithmChart J J = 0 := by
  have h := logarithmChart_step J 0 (zero_mem_logarithmChart_target J)
  simpa only [exponentialStep_zero] using h

theorem step_mem_logarithmChart_source (J : Space n) (K : AntiSkewSpace J)
    (h : K ∈ (logarithmChart J).target) : exponentialStep J K ∈ (logarithmChart J).source := by
  have he := (logarithmChart J).map_target h
  rwa [logarithmChart_symm_eq_step J K h] at he

theorem exponential_logarithmChart (J J' : Space n)
    (h : J' ∈ (logarithmChart J).source) :
    Exponential.exp (antiSkewToSkew J (logarithmChart J J')) = Cayley.relative J J' :=
  (relative_step J (logarithmChart J J')).symm.trans
    (congrArg (Cayley.relative J) (step_logarithmChart J J' h))

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.LocalExponential
