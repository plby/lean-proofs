import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicAnticommutingStructures
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMinimumPathFamily

/-!
# The path family for the second symplectic Bott step

An anticommuting structure `J` gives the path `cos(πt) J₀ + sin(πt) J`
from `J₀` to `-J₀` in the original quaternionic complex-structure space.
It is a closed embedding into the native compact-open path space. The second
Bott homotopy comparison is not assumed or proved by this construction.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.SecondPaths

open AnticommutingStructures NoExoticSixSphere.PathFamilies

variable {n : ℕ}

private def phaseMap (J₀ : ComplexStructures.Space n) : C(I × Space J₀, ℝ × Space J₀) where
  toFun z := ((z.1 : ℝ) * Real.pi, z.2)
  continuous_toFun := by
    have ht : Continuous (fun z : I × Space J₀ ↦ (z.1 : ℝ) * Real.pi) :=
      (continuous_subtype_val.comp continuous_fst).mul_const Real.pi
    exact ht.prodMk continuous_snd

private def rotationMap (J₀ : ComplexStructures.Space n) :
    C(ℝ × Space J₀, ComplexStructures.Space n) :=
  ⟨fun z ↦ rotation z.2 z.1, continuous_rotation J₀⟩

def family (J₀ : ComplexStructures.Space n) :
    C(I × Space J₀, ComplexStructures.Space n) :=
  (rotationMap J₀).comp (phaseMap J₀)

theorem family_zero (J₀ : ComplexStructures.Space n) (J : Space J₀) :
    family J₀ (0, J) = J₀ := by
  change rotation J ((0 : ℝ) * Real.pi) = J₀
  rw [zero_mul, rotation_zero]

theorem family_one (J₀ : ComplexStructures.Space n) (J : Space J₀) :
    family J₀ (1, J) = ComplexStructures.negative J₀ := by
  change rotation J ((1 : ℝ) * Real.pi) = ComplexStructures.negative J₀
  rw [one_mul, rotation_pi]

def pathMap (J₀ : ComplexStructures.Space n) :
    C(Space J₀, Path J₀ (ComplexStructures.negative J₀)) :=
  curry (family J₀) (family_zero J₀) (family_one J₀)

theorem pathMap_apply (J₀ : ComplexStructures.Space n) (J : Space J₀) (t : I) :
    pathMap J₀ J t = rotation J ((t : ℝ) * Real.pi) := rfl

theorem pathMap_midpoint (J₀ : ComplexStructures.Space n) (J : Space J₀) :
    pathMap J₀ J (⟨1 / 2, by norm_num⟩ : I) = J.val := by
  rw [pathMap_apply]
  change rotation J ((1 / 2 : ℝ) * Real.pi) = J.val
  rw [show (1 / 2 : ℝ) * Real.pi = Real.pi / 2 by ring, rotation_half_pi]

theorem pathMap_injective (J₀ : ComplexStructures.Space n) :
    Function.Injective (pathMap J₀) := by
  intro J K h
  have he := congrArg (fun p : Path J₀ (ComplexStructures.negative J₀) ↦
    p (⟨1 / 2, by norm_num⟩ : I)) h
  rw [pathMap_midpoint, pathMap_midpoint] at he
  exact Subtype.ext he

theorem pathMap_isClosedEmbedding (J₀ : ComplexStructures.Space n) :
    Topology.IsClosedEmbedding (pathMap J₀) :=
  (pathMap J₀).continuous.isClosedEmbedding (pathMap_injective J₀)

def pathRangeHomeomorph (J₀ : ComplexStructures.Space n) :
    Space J₀ ≃ₜ Set.range (pathMap J₀) :=
  (pathMap_isClosedEmbedding J₀).isEmbedding.toHomeomorph

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.SecondPaths
