import Wikipedia.HomotopyGroupsOfSpheres.CliffordSingleLatitudeFamily
import Wikipedia.HomotopyGroupsOfSpheres.SingleLatitudeHomeomorphComparison
import Wikipedia.HomotopyGroupsOfSpheres.CliffordCorrectedGenerator
import Wikipedia.HomotopyGroupsOfSpheres.CliffordCorrectedClassAction
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitarySpecialReindex
import Wikipedia.HomotopyGroupsOfSpheres.BalancedBottHomotopy

/-!
# The degree-twelve candidate reduces to the actual balanced four-sphere class

The angular coordinate homeomorphism, native cube factorization, determinant-one
inclusion, and balanced Bott isomorphism all act on the original representatives.
Primitivity of the resulting balanced class remains a separate assertion.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices LatitudeDescent

attribute [local irreducible] correctedUnderlyingMap basedAngularSphereHomeomorph parameterCube

theorem correctedInputClass_eq_pointed :
    correctedInputClass = pointedMap correctedUnderlyingMap axis identity
      correctedUnderlyingMap_axis parameterCubeClass := by
  have h₁ : correctedInputClass = (⟦correctedCube parameterCube⟧ :
      π_ 5 (Space (Fin 6 ⊕ Fin 6)) identity) := rfl
  have h₂ : (⟦correctedCube parameterCube⟧ : π_ 5 (Space (Fin 6 ⊕ Fin 6)) identity) =
      pointedMap (N := Fin 5) correctedUnderlyingMap axis identity correctedUnderlyingMap_axis
        (⟦parameterCube⟧ : π_ 5 ComplexCrossProductUnitary.UnitSphere axis) :=
    correctedCube_class_eq_pointed parameterCube
  have h₃ : (⟦parameterCube⟧ : π_ 5 ComplexCrossProductUnitary.UnitSphere axis) =
      parameterCubeClass := rfl
  exact h₁.trans (h₂.trans (congrArg
    (pointedMap (N := Fin 5) correctedUnderlyingMap axis identity correctedUnderlyingMap_axis) h₃))

theorem corrected_generates_iff_includedBalancedBott :
    Function.Surjective (fun k : ℤ ↦ correctedInputClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ includedBalancedBottClass ^ k) := by
  rw [correctedInputClass_eq_pointed]
  have h := SingleFamily.nativeCube_generates_iff_of_homeomorph
    correctedLatitudeFamily correctedLatitudeFamily_parameter_point
    basedAngularSphereHomeomorph axis basedAngularSphereHomeomorph_basepoint
    correctedUnderlyingMap correctedUnderlyingMap_axis correctedLatitudeFamily_sphereMap
    parameterCubeClass parameterCubeClass_generates
  rw [correctedLatitudeFamily_nativeClass] at h
  exact h

def balancedSpecialInclusionMulEquiv :
    π_ 5 (SpecialSpace (Fin 6 ⊕ Fin 6)) specialIdentity ≃*
      π_ 5 (Space (Fin 6 ⊕ Fin 6)) identity :=
  specialInclusionReindexMulEquiv (finSumFinEquiv : Fin 6 ⊕ Fin 6 ≃ Fin (11 + 1)) 3

theorem balancedSpecialInclusionMulEquiv_apply
    (a : π_ 5 (SpecialSpace (Fin 6 ⊕ Fin 6)) specialIdentity) :
    balancedSpecialInclusionMulEquiv a =
      pointedMap forgetSpecial specialIdentity identity forgetSpecial_identity a :=
  specialInclusionReindexMulEquiv_apply (finSumFinEquiv : Fin 6 ⊕ Fin 6 ≃ Fin (11 + 1)) 3 a

theorem includedBalancedBott_generates_iff_special :
    Function.Surjective (fun k : ℤ ↦ includedBalancedBottClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ balancedBottClass ^ k) := by
  have h := CyclicGenerators.equiv_generates_iff balancedSpecialInclusionMulEquiv balancedBottClass
  rw [balancedSpecialInclusionMulEquiv_apply] at h
  exact h

theorem balancedBott_generates_iff_balanced :
    Function.Surjective (fun k : ℤ ↦ balancedBottClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ balancedInputClass ^ k) := by
  have h := CyclicGenerators.equiv_generates_iff
    (BalancedRealInvolutions.bottDegreeShiftMulEquiv 6 4 (by decide)) balancedInputClass
  have he : BalancedRealInvolutions.bottDegreeShiftMulEquiv 6 4 (by decide)
      balancedInputClass = balancedBottClass :=
    BalancedRealInvolutions.bottDegreeShiftMulEquiv_mk 6 4 (by decide) balancedInputCube
  rw [he] at h
  exact h

theorem corrected_generates_iff_balanced :
    Function.Surjective (fun k : ℤ ↦ correctedInputClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ balancedInputClass ^ k) :=
  corrected_generates_iff_includedBalancedBott.trans
    (includedBalancedBott_generates_iff_special.trans balancedBott_generates_iff_balanced)

theorem sphereCandidate_generates_iff_balanced :
    Function.Surjective (fun k : ℤ ↦ sphereCandidateClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ balancedInputClass ^ k) :=
  sphereCandidate_generates_iff_corrected.trans corrected_generates_iff_balanced

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
