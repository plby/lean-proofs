import Wikipedia.HomotopyGroupsOfSpheres.CliffordBalancedGenerator

/-!
# Primitivity can be computed before the chosen orthogonal normalization

This keeps the actual raw Clifford family and its own base point available
for an explicit Hopf frame. No identification of the chosen pole frame with
an explicit coordinate frame is required.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

def rawInputCube : GenLoop (Fin 4) (BalancedRealInvolutions.Space 6) (rawBalanced pole) :=
  pointedMapGenLoop rawBalanced pole (rawBalanced pole) rfl parameterFourCube

def rawInputClass : π_ 4 (BalancedRealInvolutions.Space 6) (rawBalanced pole) :=
  ⟦rawInputCube⟧

def balancedNormalizationMulEquiv :
    π_ 4 (BalancedRealInvolutions.Space 6) (rawBalanced pole) ≃*
      π_ 4 (BalancedRealInvolutions.Space 6) (BalancedRealInvolutions.standard 6) :=
  pointedHomeomorphMulEquiv (BalancedRealInvolutions.conjugationHomeomorph poleFrame⁻¹)
    (rawBalanced pole) (BalancedRealInvolutions.standard 6) balancedMap_pole

theorem balancedNormalizationMulEquiv_cube (p : GenLoop (Fin 4) UnitSphere pole) :
    balancedNormalizationMulEquiv
      (⟦pointedMapGenLoop rawBalanced pole (rawBalanced pole) rfl p⟧ :
        π_ 4 (BalancedRealInvolutions.Space 6) (rawBalanced pole)) =
      (⟦balancedCube p⟧ :
        π_ 4 (BalancedRealInvolutions.Space 6) (BalancedRealInvolutions.standard 6)) :=
  pointedHomeomorphMulEquiv_mk (BalancedRealInvolutions.conjugationHomeomorph poleFrame⁻¹)
    (rawBalanced pole) (BalancedRealInvolutions.standard 6) balancedMap_pole
    (pointedMapGenLoop rawBalanced pole (rawBalanced pole) rfl p)

theorem balancedNormalizationMulEquiv_rawInput :
    balancedNormalizationMulEquiv rawInputClass = balancedInputClass :=
  balancedNormalizationMulEquiv_cube parameterFourCube

theorem balanced_generates_iff_raw :
    Function.Surjective (fun k : ℤ ↦ balancedInputClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ rawInputClass ^ k) := by
  have h := CyclicGenerators.equiv_generates_iff balancedNormalizationMulEquiv rawInputClass
  rw [balancedNormalizationMulEquiv_rawInput] at h
  exact h

theorem sphereCandidate_generates_iff_raw :
    Function.Surjective (fun k : ℤ ↦ ComplexCrossProductUnitary.sphereCandidateClass ^ k) ↔
      Function.Surjective (fun k : ℤ ↦ rawInputClass ^ k) :=
  sphereCandidate_generates_iff_balanced.trans balanced_generates_iff_raw

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
