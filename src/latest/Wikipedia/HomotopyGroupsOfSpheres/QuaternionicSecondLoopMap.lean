import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicReferenceRotation
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondPathFamily

/-!
# A based loop map for anticommuting quaternionic complex structures

Conjugation along a fixed reference rotation gives an actual homeomorphism
from the antipodal path space to the loop space of complex structures. It
sends the reference path to the constant loop. This construction does not
use a group structure on the complex-structure locus.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.SecondPaths

open AnticommutingStructures

variable {n : ℕ} {J₀ : ComplexStructures.Space n}

def referenceLift (J : Space J₀) : C(I, symplecticSubgroup n) where
  toFun t := conjugator J ((t : ℝ) * Real.pi)
  continuous_toFun := (continuous_conjugator J).comp
    (continuous_subtype_val.mul_const Real.pi)

theorem referenceLift_zero (J : Space J₀) : referenceLift J 0 = 1 := by
  change conjugator J ((0 : ℝ) * Real.pi) = 1
  rw [zero_mul, conjugator_zero]

theorem referenceLift_rotation (J : Space J₀) (t : I) :
    ComplexStructures.conjugate (referenceLift J t) J₀ = pathMap J₀ J t :=
  conjugator_rotation J ((t : ℝ) * Real.pi)

theorem referenceLift_one_action (J : Space J₀) :
    ComplexStructures.conjugate (referenceLift J 1) J₀ =
      ComplexStructures.negative J₀ := by
  rw [referenceLift_rotation, Path.target]

def toLoop (J : Space J₀) (p : Path J₀ (ComplexStructures.negative J₀)) : Path J₀ J₀ where
  toFun t := ComplexStructures.conjugate (referenceLift J t)⁻¹ (p t)
  continuous_toFun := ComplexStructures.continuous_conjugate _ _
    (referenceLift J).continuous.inv p.continuous
  source' := by rw [Path.source, referenceLift_zero, inv_one, ComplexStructures.conjugate_one]
  target' := by
    rw [Path.target, ← referenceLift_one_action J]
    exact ComplexStructures.conjugate_inv_cancel _ _

def fromLoop (J : Space J₀) (p : Path J₀ J₀) : Path J₀ (ComplexStructures.negative J₀) where
  toFun t := ComplexStructures.conjugate (referenceLift J t) (p t)
  continuous_toFun := ComplexStructures.continuous_conjugate _ _
    (referenceLift J).continuous p.continuous
  source' := by rw [Path.source, referenceLift_zero, ComplexStructures.conjugate_one]
  target' := by rw [Path.target]; exact referenceLift_one_action J

theorem continuous_toLoop (J : Space J₀) : Continuous (toLoop J) := by
  apply Path.continuous_uncurry_iff.mp
  change Continuous (fun z : Path J₀ (ComplexStructures.negative J₀) × I ↦
    ComplexStructures.conjugate (referenceLift J z.2)⁻¹ (z.1 z.2))
  exact ComplexStructures.continuous_conjugate _ _
    ((referenceLift J).continuous.comp continuous_snd).inv continuous_eval

theorem continuous_fromLoop (J : Space J₀) : Continuous (fromLoop J) := by
  apply Path.continuous_uncurry_iff.mp
  change Continuous (fun z : Path J₀ J₀ × I ↦
    ComplexStructures.conjugate (referenceLift J z.2) (z.1 z.2))
  exact ComplexStructures.continuous_conjugate _ _
    ((referenceLift J).continuous.comp continuous_snd) continuous_eval

theorem fromLoop_toLoop (J : Space J₀) (p : Path J₀ (ComplexStructures.negative J₀)) :
    fromLoop J (toLoop J p) = p := by
  apply Path.ext
  funext t
  exact ComplexStructures.conjugate_cancel_inv (referenceLift J t) (p t)

theorem toLoop_fromLoop (J : Space J₀) (p : Path J₀ J₀) :
    toLoop J (fromLoop J p) = p := by
  apply Path.ext
  funext t
  exact ComplexStructures.conjugate_inv_cancel (referenceLift J t) (p t)

def loopHomeomorph (J : Space J₀) : Path J₀ (ComplexStructures.negative J₀) ≃ₜ Path J₀ J₀ where
  toFun := toLoop J
  invFun := fromLoop J
  left_inv := fromLoop_toLoop J
  right_inv := toLoop_fromLoop J
  continuous_toFun := continuous_toLoop J
  continuous_invFun := continuous_fromLoop J

theorem toLoop_reference (J : Space J₀) : toLoop J (pathMap J₀ J) = Path.refl J₀ := by
  apply Path.ext
  funext t
  change ComplexStructures.conjugate (referenceLift J t)⁻¹ (pathMap J₀ J t) = J₀
  rw [← referenceLift_rotation]
  exact ComplexStructures.conjugate_inv_cancel _ _

def loopMap (J : Space J₀) : C(Space J₀, Path J₀ J₀) :=
  (toContinuousMap (loopHomeomorph J)).comp (pathMap J₀)

theorem loopMap_reference (J : Space J₀) : loopMap J J = Path.refl J₀ := toLoop_reference J

theorem loopMap_apply (J K : Space J₀) (t : I) :
    loopMap J K t = ComplexStructures.conjugate (conjugator J ((t : ℝ) * Real.pi))⁻¹
      (rotation K ((t : ℝ) * Real.pi)) := rfl

theorem loopMap_injective (J : Space J₀) : Function.Injective (loopMap J) :=
  (loopHomeomorph J).injective.comp (pathMap_injective J₀)

theorem loopMap_isClosedEmbedding (J : Space J₀) : Topology.IsClosedEmbedding (loopMap J) :=
  (loopMap J).continuous.isClosedEmbedding (loopMap_injective J)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.SecondPaths
