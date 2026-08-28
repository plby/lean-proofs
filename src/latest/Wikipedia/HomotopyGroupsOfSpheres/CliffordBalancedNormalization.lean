import Wikipedia.HomotopyGroupsOfSpheres.CliffordPhaseHomotopy
import Wikipedia.HomotopyGroupsOfSpheres.BalancedRotationConjugation

/-! # The phase-padded Clifford family in the actual based balanced coordinates -/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open ComplexCrossProductUnitary QuaternionicSymmetricMatrices

def normalizationHomeomorph : Space (Fin 6 ⊕ Fin 6) ≃ₜ Space (Fin 6 ⊕ Fin 6) :=
  BalancedRealInvolutions.symmetricCongruenceHomeomorph poleFrame⁻¹

theorem normalizationHomeomorph_identity : normalizationHomeomorph identity = identity :=
  BalancedRealInvolutions.symmetricCongruenceHomeomorph_identity poleFrame⁻¹

def balancedSourceMap : C(ComplexCrossProductUnitary.UnitSphere, Space (Fin 6 ⊕ Fin 6)) :=
  (normalizationHomeomorph : C(_, _)).comp paddedSource

def balancedSphereMap : C(ComplexCrossProductUnitary.UnitSphere, Space (Fin 6 ⊕ Fin 6)) :=
  (normalizationHomeomorph : C(_, _)).comp paddedTarget

def balancedPaddingHomotopy : balancedSourceMap.HomotopyRel balancedSphereMap {axis} :=
  phasePaddingHomotopy.compContinuousMap
    (normalizationHomeomorph : C(Space (Fin 6 ⊕ Fin 6), Space (Fin 6 ⊕ Fin 6)))

theorem balancedSourceMap_axis : balancedSourceMap axis = identity := by
  change normalizationHomeomorph (paddedSource axis) = identity
  rw [paddedSource_axis, normalizationHomeomorph_identity]

theorem balancedSphereMap_axis : balancedSphereMap axis = identity := by
  change normalizationHomeomorph (paddedTarget axis) = identity
  rw [paddedTarget_axis, normalizationHomeomorph_identity]

theorem balancedSphereMap_latitude (θ : ℝ) (v : UnitSphere) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    balancedSphereMap (latitudePoint θ v) =
      (BalancedRealInvolutions.rotation (balancedMap v) θ).val := by
  change normalizationHomeomorph (paddedTarget (latitudePoint θ v)) = _
  rw [paddedTarget_latitude θ v h0 hπ]
  exact BalancedRealInvolutions.symmetricCongruenceHomeomorph_rotation poleFrame⁻¹
    (rawBalanced v) θ

theorem balancedSphereMap_reference (θ : ℝ) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    balancedSphereMap (latitudePoint θ pole) =
      (BalancedRealInvolutions.diagonalSpecial 6 θ).val := by
  rw [balancedSphereMap_latitude θ pole h0 hπ, balancedMap_pole,
    BalancedRealInvolutions.rotation_standard]

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
