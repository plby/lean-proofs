import Wikipedia.NoExoticSixSphere.JamesSphereFirstStageHomeomorph
import Wikipedia.NoExoticSixSphere.JamesSphereQuotientRelativeHomology
import Wikipedia.NoExoticSixSphere.JamesSphereBottomHomology
import Wikipedia.NoExoticSixSphere.RelativeContractibleSubspace
import Wikipedia.NoExoticSixSphere.RelativeHomologyAcyclic
import Wikipedia.NoExoticSixSphere.SphereHomologyGroups

/-!
# The original first-stage inclusion is a low-degree homology isomorphism

Below the bottom quotient cell, the quotient's positive homology vanishes.
The actual quotient comparison transfers this to relative homology of
the full James pair. Its exact sequence proves the stated inclusion
range, including the upper-edge injection from sphere homology vanishing.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.JamesSphere

namespace FirstStageQuotient

theorem homology_below_bottom (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) (hdn : d < 2 * n) :
    Subsingleton (SingularHomology (Space n) d) := by
  let : Subsingleton (SingularHomology (Sphere (n + n)) d) :=
    subsingleton_singularHomology_of_homeomorph_sphere
      (by omega) (by omega) (by omega) (Homeomorph.refl _)
  exact (bottomSphere_homology_surjective n (by omega) d hd (by omega)).subsingleton

theorem relative_homology_below_bottom (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d)
    (hdn : d < 2 * n) :
    Subsingleton (RelativeSingularHomology.Homology ({basepoint n} : Set (Space n)) d) := by
  let := homology_below_bottom n d hn hd hdn
  have he : d - 2 + 2 = d := Nat.sub_add_cancel hd
  have hb := RelativeSingularHomology.contractibleSubspace_toRelative_bijective
    ({basepoint n} : Set (Space n)) (d - 2)
  rw [he] at hb
  exact hb.surjective.subsingleton

end FirstStageQuotient

namespace FirstStage

theorem relative_homology_below_bottom (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d)
    (hdn : d < 2 * n) :
    Subsingleton (RelativeSingularHomology.Homology (James.stage (spherePole n) 1) d) := by
  let := FirstStageQuotient.relative_homology_below_bottom n d hn hd hdn
  exact (FirstStageQuotient.quotient_relative_homology_bijective n d).injective.subsingleton

theorem inclusion_homology_bijective (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d)
    (hdn : d < 2 * n) : Function.Bijective
      (singularHomologyMap (subtypeInclusion (James.stage (spherePole n) 1)) d) := by
  let := relative_homology_below_bottom n d hn hd hdn
  refine ⟨?_, RelativeSingularHomology.inclusion_surjective_of_relative_subsingleton _ d⟩
  by_cases hstrict : d + 1 < 2 * n
  · let := relative_homology_below_bottom n (d + 1) hn (by omega) hstrict
    exact RelativeSingularHomology.inclusion_injective_of_relative_subsingleton _ d
  · let : Subsingleton (SingularHomology (James.stage (spherePole n) 1) d) :=
      subsingleton_singularHomology_of_homeomorph_sphere
        (by omega) (by omega) (by omega) (homeomorph n).symm
    exact fun _ _ _ ↦ Subsingleton.elim _ _

end FirstStage

end NoExoticSixSphere.JamesSphere
