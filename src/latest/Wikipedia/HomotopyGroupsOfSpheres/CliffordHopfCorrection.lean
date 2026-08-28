import Wikipedia.HomotopyGroupsOfSpheres.CliffordRawHopfRotation
import Wikipedia.HomotopyGroupsOfSpheres.PointedHomotopyClassComparison

/-! # A based correction of the raw Clifford four-sphere family -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

def hopfReferenceAction :
    C(ℝ × BalancedRealInvolutions.Space 6, BalancedRealInvolutions.Space 6) :=
  ⟨fun p ↦ BalancedRealInvolutions.conjugate (rawHopfRotation equatorPole p.1)⁻¹ p.2,
    BalancedRealInvolutions.continuous_conjugate.comp
      ((continuous_rawHopfRotation.comp (continuous_const.prodMk continuous_fst)).inv.prodMk
        continuous_snd)⟩

theorem hopfReferenceAction_zero (J : BalancedRealInvolutions.Space 6) :
    hopfReferenceAction (0, J) = J := by
  change BalancedRealInvolutions.conjugate (rawHopfRotation equatorPole 0)⁻¹ J = J
  rw [rawHopfRotation_zero, inv_one, BalancedRealInvolutions.conjugate_one]

def hopfCorrectedSphereMap : C(UnitSphere, BalancedRealInvolutions.Space 6) :=
  hopfReferenceAction.comp
    ⟨fun v ↦ (fourPolarAngle v, rawBalanced v),
      fourPolarAngle.continuous.prodMk rawBalanced.continuous⟩

def hopfCorrectionHomotopy : rawBalanced.HomotopyRel hopfCorrectedSphereMap {pole} where
  toContinuousMap := hopfReferenceAction.comp
    ⟨fun p : I × UnitSphere ↦ ((p.1 : ℝ) * fourPolarAngle p.2, rawBalanced p.2),
      ((continuous_subtype_val.comp continuous_fst).mul
        (fourPolarAngle.continuous.comp continuous_snd)).prodMk
          (rawBalanced.continuous.comp continuous_snd)⟩
  map_zero_left v := by
    change hopfReferenceAction ((0 : ℝ) * fourPolarAngle v, rawBalanced v) = rawBalanced v
    rw [zero_mul, hopfReferenceAction_zero]
  map_one_left v := by
    change hopfReferenceAction ((1 : ℝ) * fourPolarAngle v, rawBalanced v) =
      hopfReferenceAction (fourPolarAngle v, rawBalanced v)
    rw [one_mul]
  prop' t v hv := by
    have h : v = pole := Set.mem_singleton_iff.mp hv
    subst v
    change hopfReferenceAction ((t : ℝ) * fourPolarAngle pole, rawBalanced pole) = rawBalanced pole
    rw [fourPolarAngle_pole, mul_zero, hopfReferenceAction_zero]

theorem hopfCorrectedSphereMap_pole : hopfCorrectedSphereMap pole = rawBalanced pole := by
  change hopfReferenceAction (fourPolarAngle pole, rawBalanced pole) = rawBalanced pole
  rw [fourPolarAngle_pole, hopfReferenceAction_zero]

theorem hopfCorrectedSphereMap_latitude (θ : ℝ) (q : EquatorSphere)
    (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    hopfCorrectedSphereMap (fourLatitudePoint θ q) =
      BalancedRealInvolutions.conjugate (correctedRawHopfRotation q θ) (rawBalanced pole) := by
  change BalancedRealInvolutions.conjugate
    (rawHopfRotation equatorPole (fourPolarAngle (fourLatitudePoint θ q)))⁻¹
      (rawBalanced (fourLatitudePoint θ q)) = _
  rw [fourPolarAngle_latitude θ q h0 hπ, ← rawHopfRotation_conjugate_pole,
    BalancedRealInvolutions.conjugate_mul]
  rfl

theorem hopfCorrectedSphereMap_reference (θ : ℝ) (h0 : 0 ≤ θ) (hπ : θ ≤ Real.pi) :
    hopfCorrectedSphereMap (fourLatitudePoint θ equatorPole) = rawBalanced pole := by
  rw [hopfCorrectedSphereMap_latitude θ equatorPole h0 hπ,
    correctedRawHopfRotation_reference, BalancedRealInvolutions.conjugate_one]

theorem hopfCorrectedSphereMap_pi (q : EquatorSphere) :
    hopfCorrectedSphereMap (fourLatitudePoint Real.pi q) = rawBalanced pole := by
  rw [fourLatitudePoint_pi_eq q equatorPole]
  exact hopfCorrectedSphereMap_reference Real.pi Real.pi_pos.le le_rfl

def hopfCorrectedCube (p : GenLoop (Fin 4) UnitSphere pole) :
    GenLoop (Fin 4) (BalancedRealInvolutions.Space 6) (rawBalanced pole) :=
  pointedMapGenLoop hopfCorrectedSphereMap pole (rawBalanced pole) hopfCorrectedSphereMap_pole p

theorem rawClass_eq_hopfCorrected (p : GenLoop (Fin 4) UnitSphere pole) :
    (⟦pointedMapGenLoop rawBalanced pole (rawBalanced pole) rfl p⟧ :
      π_ 4 (BalancedRealInvolutions.Space 6) (rawBalanced pole)) = ⟦hopfCorrectedCube p⟧ :=
  Quotient.sound (pointedMapGenLoop_homotopic_of_homotopyRel
    rawBalanced hopfCorrectedSphereMap pole (rawBalanced pole) rfl
      hopfCorrectedSphereMap_pole hopfCorrectionHomotopy p)

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
