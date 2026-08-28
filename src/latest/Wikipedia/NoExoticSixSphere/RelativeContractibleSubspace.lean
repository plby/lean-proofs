import Wikipedia.NoExoticSixSphere.RelativeSingularHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint

/-!
# Relative homology above degree one for a contractible subspace

The genuine pair exact sequence proves that the original map from
absolute to relative homology is an isomorphism in degrees at least two.
Its inverse is therefore tied to that map, not an arbitrary abstract
identification of groups.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X : Type} [TopologicalSpace X] (U : Set X) [ContractibleSpace U]

theorem contractibleSubspace_toRelative_bijective (n : ℕ) :
    Function.Bijective (toRelative U (n + 2)) := by
  let := contractible_homology_subsingleton U (n + 2) (by omega)
  let := contractible_homology_subsingleton U (n + 1) (by omega)
  constructor
  · apply LinearMap.ker_eq_bot.mp
    rw [← exact_at_ambient]
    apply LinearMap.range_eq_bot.mpr
    ext c
    exact (congrArg (singularHomologyMap (subtypeInclusion U) (n + 2))
      (Subsingleton.elim c 0)).trans (map_zero _)
  · intro c
    have hc : c ∈ LinearMap.ker (connecting U (n + 1)) := Subsingleton.elim _ _
    rw [← exact_at_relative] at hc
    exact hc

def contractibleSubspaceEquiv (n : ℕ) :
    SingularHomology X (n + 2) ≃ₗ[ℤ] Homology U (n + 2) :=
  LinearEquiv.ofBijective (toRelative U (n + 2))
    (contractibleSubspace_toRelative_bijective U n)

theorem contractibleSubspaceEquiv_apply (n : ℕ) (c : SingularHomology X (n + 2)) :
    contractibleSubspaceEquiv U n c = toRelative U (n + 2) c := rfl

theorem contractibleSubspaceEquiv_symm_toRelative (n : ℕ)
    (c : SingularHomology X (n + 2)) :
    (contractibleSubspaceEquiv U n).symm (toRelative U (n + 2) c) = c :=
  (contractibleSubspaceEquiv U n).symm_apply_apply c

end NoExoticSixSphere.RelativeSingularHomology
