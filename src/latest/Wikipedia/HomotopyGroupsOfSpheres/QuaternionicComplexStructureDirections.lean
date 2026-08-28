import Wikipedia.HomotopyGroupsOfSpheres.AnticommutingLinearSpace
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureConjugation

/-!
# Skew directions anticommuting with a quaternionic complex structure

The model is an actual real submodule of the ambient operator space. The
exponential intertwining identity is proved from anticommutation, rather
than assuming that ambient deformations preserve the complex-structure locus.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures

open NoExoticSixSphere.GLOrthonormalization Exponential

variable {n : ℕ}

def antiSkewSubmodule (J : Space n) :
    Submodule ℝ (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) :=
  skewSubmodule n ⊓ anticommutingSubmodule J.val.val

abbrev AntiSkewSpace (J : Space n) := ↥(antiSkewSubmodule J)

def antiSkewToSkew (J : Space n) : AntiSkewSpace J →ₗ[ℝ] SkewSpace n where
  toFun K := ⟨K.val, K.property.1⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem antiSkew_anticommute (J : Space n) (K : AntiSkewSpace J) :
    J.val.val * K.val = -(K.val * J.val.val) := K.property.2

theorem continuous_antiSkewToSkew (J : Space n) : Continuous (antiSkewToSkew J) :=
  continuous_subtype_val.subtype_mk _

local instance : NormedAlgebra ℚ (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) :=
  NormedAlgebra.restrictScalars ℚ ℝ (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))

theorem anticommute_exp (J : Space n) (K : SkewSpace n)
    (hK : J.val.val * K.val = -(K.val * J.val.val)) :
    toSymplectic J * exp K = exp (-K) * toSymplectic J := by
  have hs : SemiconjBy J.val.val K.val (-K.val) := by
    change J.val.val * K.val = (-K.val) * J.val.val
    apply ContinuousLinearMap.ext
    intro x
    exact DFunLike.congr_fun hK x
  have he := hs.exp_right
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact he

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures
