import Wikipedia.NoExoticSixSphere.JamesSphereQuotientStageHomologyRange

/-!
# The actual bottom-sphere map is a homology isomorphism in the required range

The second-stage quotient homeomorphism identifies the original bottom
sphere map with the original second-stage inclusion. Later cells preserve
its low homology. At the upper edge, surjectivity and vanishing of the
source sphere homology give injectivity as well.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient

def secondStageSphereHomeomorph (n : ℕ) : FiniteStage.Space n 1 ≃ₜ Sphere (n + n) := by
  change SecondStage.QuotientSpace n ≃ₜ Sphere (n + n)
  exact SecondStage.quotientHomeomorph n

theorem bottomSphere_factor (n : ℕ) :
    (FiniteStage.map n 1).comp ((secondStageSphereHomeomorph n).symm :
      C(Sphere (n + n), FiniteStage.Space n 1)) = bottomSphere n := rfl

theorem bottomSphere_homology_injective (n : ℕ) (hn : 0 < n) (d : ℕ)
    (hd : 2 ≤ d) (hdn : d + 1 < 3 * n) :
    Function.Injective (singularHomologyMap (bottomSphere n) d) := by
  rw [← bottomSphere_factor, singularHomologyMap_comp]
  exact (StageHomologyRange.fullMap_injective n hn d hd hdn).comp
    (homeomorphHomologyEquiv (secondStageSphereHomeomorph n).symm d).injective

theorem bottomSphere_homology_surjective (n : ℕ) (hn : 0 < n) (d : ℕ)
    (hd : 2 ≤ d) (hdn : d < 3 * n) :
    Function.Surjective (singularHomologyMap (bottomSphere n) d) := by
  rw [← bottomSphere_factor, singularHomologyMap_comp]
  exact (StageHomologyRange.fullMap_surjective n hn d hd hdn).comp
    (homeomorphHomologyEquiv (secondStageSphereHomeomorph n).symm d).surjective

theorem bottomSphere_homology_bijective_range (n : ℕ) (hn : 2 ≤ n) (d : ℕ)
    (hd : 2 ≤ d) (hdn : d < 3 * n) :
    Function.Bijective (singularHomologyMap (bottomSphere n) d) := by
  refine ⟨?_, bottomSphere_homology_surjective n (by omega) d hd hdn⟩
  by_cases hstrict : d + 1 < 3 * n
  · exact bottomSphere_homology_injective n (by omega) d hd hstrict
  · let : Subsingleton (SingularHomology (Sphere (n + n)) d) := by
      have he : n + n = (n + n - 1) + 1 := by omega
      rw [he]
      exact SphereHomology.unitSphere_homology_subsingleton (n + n - 1) d
        (by omega) (by omega)
    exact fun _ _ _ ↦ Subsingleton.elim _ _

end NoExoticSixSphere.JamesSphere.FirstStageQuotient
