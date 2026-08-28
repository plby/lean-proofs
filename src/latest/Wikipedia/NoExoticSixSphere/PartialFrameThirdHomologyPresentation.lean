import Wikipedia.NoExoticSixSphere.PartialFrameMayerVietoris
import Wikipedia.NoExoticSixSphere.PartialFrameOverlapHomology
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# An unconditional native third-homology presentation for `Space 5 2`

The actual overlap has zero second homology, so the Mayer–Vietoris map from
the two patches onto third homology is surjective. Its kernel is the range
of the proved reduced inclusion map. The quotient below therefore presents
the original third singular homology, without a connectivity or exactness
hypothesis. The transition's integer relations are still to be computed.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnHomology

open GLOrthonormalization ColumnBundle
open Wikipedia.HopfProblem.SingularMayerVietoris

variable (v : UnitSphere (Vector 2))

theorem thirdHomologyMap_surjective :
    Function.Surjective (rightHomologyMap (North 3 v) (South 3 v) 3) := by
  let : Subsingleton (SingularHomology ↥(North 3 v ∩ South 3 v) 2) :=
    twoColumnOverlap_secondHomology_subsingleton v
  intro a
  have ha : a ∈ LinearMap.range (rightHomologyMap (North 3 v) (South 3 v) 3) := by
    rw [exact_at_ambient (North 3 v) (South 3 v) (isOpen_north 3 v) (isOpen_south 3 v)
      (cover 3 v) 2]
    exact Subsingleton.elim _ _
  exact ha

theorem reducedThirdHomologyMap_surjective : Function.Surjective (reducedRightMap 3 v 3) := by
  intro a
  obtain ⟨b, hb⟩ := thirdHomologyMap_surjective v a
  refine ⟨pairEquiv 3 v 3 b, ?_⟩
  change rightHomologyMap (North 3 v) (South 3 v) 3
    ((pairEquiv 3 v 3).symm (pairEquiv 3 v 3 b)) = a
  rw [LinearEquiv.symm_apply_apply]
  exact hb

def thirdHomologyPresentation :
    ((SingularHomology (Space 4 1) 3 × SingularHomology (Space 4 1) 3) ⧸
      LinearMap.range (reducedLeftMap 3 v 3)) ≃ₗ[ℤ] SingularHomology (Space 5 2) 3 :=
  (Submodule.quotEquivOfEq _ _ (reduced_exact_at_pair 3 v 3)).trans
    ((reducedRightMap 3 v 3).quotKerEquivOfSurjective (reducedThirdHomologyMap_surjective v))

theorem thirdHomologyPresentation_mk
    (b : SingularHomology (Space 4 1) 3 × SingularHomology (Space 4 1) 3) :
    thirdHomologyPresentation v (Submodule.Quotient.mk b) = reducedRightMap 3 v 3 b := by
  simp only [thirdHomologyPresentation, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

end NoExoticSixSphere.Stiefel.ColumnHomology
