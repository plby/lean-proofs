import Wikipedia.HopfProblem.DegreeCollapseRankSixThirdVanishing
import Wikipedia.HopfProblem.DegreeCollapseOrthogonalComponents

/-!
# The two actual components of rank-six orthogonal complex structures

Every original complex structure is reconstructed from a unit spinor
and its Pfaffian sign. The spinor sphere is path connected, while the
Pfaffian is constant on paths. Negating the structure exchanges the
two signs. The original degree-zero Bott comparison then computes
the native fundamental group of O(6) as a set of two elements.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.RankSixComponents

open NoExoticSixSphere GLOrthonormalization RankSixComplexProjection RankSixSkewMatrix

abbrev Space := OrthogonalComplexStructures.Space 6

def pointSpinor (J : Space) : UnitSpinor :=
  (RankSixThirdVanishing.exists_unitSection (ContinuousMap.const (Sphere 3) J)).choose
    (spherePole 3)

theorem pointSpinor_fixed (J : Space) :
    projection J (pointSpinor J) = (pointSpinor J : Spinor) :=
  (RankSixThirdVanishing.exists_unitSection (ContinuousMap.const (Sphere 3) J)).choose_spec
    (spherePole 3)

def sign (J : Space) : ℝ := -pfaffian (matrix J)

theorem sign_square (J : Space) : sign J ^ 2 = 1 := by
  rw [sign, neg_sq]
  exact pfaffian_sq_one _ (matrix_transpose _) (matrix_square _)

theorem recover (J : Space) :
    signScale (sign J) (sign_square J) (fromSpinor (pointSpinor J)) = J := by
  apply matrix_injective
  rw [matrix_signScale, fromSpinor_recovers_of_fixed J (pointSpinor J) (pointSpinor_fixed J)]
  change sign J • (sign J • matrix J) = matrix J
  rw [smul_smul, ← pow_two, sign_square, one_smul]

theorem spinors_joined (q r : UnitSpinor) : Joined q r := by
  let : SimplyConnectedSpace (Sphere 7) := EuclideanSphere.simplyConnectedSpace 5
  have h := (PathConnectedSpace.joined (unitSpinorHomeomorph q) (unitSpinorHomeomorph r)).map
    unitSpinorHomeomorph.symm.continuous
  simpa only [Homeomorph.symm_apply_apply] using h

theorem joined_of_pfaffian_eq (J K : Space) (h : pfaffian (matrix J) = pfaffian (matrix K)) :
    Joined J K := by
  have hs : sign J = sign K := congrArg Neg.neg h
  have hK : signScale (sign J) (sign_square J) (fromSpinor (pointSpinor K)) = K := by
    simpa only [← hs] using recover K
  have hp := (spinors_joined (pointSpinor J) (pointSpinor K)).map
    ((continuous_signScale (sign J) (sign_square J)).comp continuous_fromSpinor)
  simpa only [Function.comp_apply, recover, hK] using hp

theorem pfaffian_neg (A : Matrix6) : pfaffian (-A) = -pfaffian A := by
  simp only [pfaffian, Matrix.neg_apply]
  ring

def opposite (J : Space) : Space := signScale (-1) (by norm_num) J

theorem pfaffian_opposite (J : Space) : pfaffian (matrix (opposite J)) = -pfaffian (matrix J) := by
  rw [opposite, matrix_signScale, neg_one_smul, pfaffian_neg]

def baseStructure : Space := Classical.choice (OrthogonalComplexStructures.nonempty_even 3)

theorem joined_base_or_opposite (J : Space) :
    Joined J baseStructure ∨ Joined J (opposite baseStructure) := by
  have hJ := pfaffian_sq_one (matrix J) (matrix_transpose J) (matrix_square J)
  have hB := pfaffian_sq_one (matrix baseStructure)
    (matrix_transpose baseStructure) (matrix_square baseStructure)
  have h : pfaffian (matrix J) = pfaffian (matrix baseStructure) ∨
      pfaffian (matrix J) = -pfaffian (matrix baseStructure) := by
    rcases sq_eq_one_iff.mp hJ with hJ | hJ <;>
      rcases sq_eq_one_iff.mp hB with hB | hB <;> simp_all
  rcases h with h | h
  · exact Or.inl (joined_of_pfaffian_eq J baseStructure h)
  · exact Or.inr (joined_of_pfaffian_eq J (opposite baseStructure)
      (h.trans (pfaffian_opposite baseStructure).symm))

theorem not_joined_base_opposite : ¬ Joined baseStructure (opposite baseStructure) := by
  rintro ⟨p⟩
  have h := pfaffian_constant (⟨p, p.continuous⟩ : C(I, Space)) 0 1
  change pfaffian (matrix (p 0)) = pfaffian (matrix (p 1)) at h
  rw [p.source, p.target, pfaffian_opposite] at h
  have hs := pfaffian_sq_one (matrix baseStructure)
    (matrix_transpose baseStructure) (matrix_square baseStructure)
  nlinarith

def representativeClass (b : Bool) : ZerothHomotopy Space :=
  ZerothHomotopy.mk (if b then opposite baseStructure else baseStructure)

theorem representativeClass_injective : Function.Injective representativeClass := by
  intro b c h
  cases b <;> cases c
  · rfl
  · exact False.elim (not_joined_base_opposite (Quotient.exact h))
  · exact False.elim (not_joined_base_opposite (Quotient.exact h.symm))
  · rfl

theorem representativeClass_surjective : Function.Surjective representativeClass := by
  intro c
  obtain ⟨J, rfl⟩ := ZerothHomotopy.mk_surjective c
  rcases joined_base_or_opposite J with h | h
  · exact ⟨false, (Quotient.sound h).symm⟩
  · exact ⟨true, (Quotient.sound h).symm⟩

def componentsEquiv : ZerothHomotopy Space ≃ Bool :=
  (Equiv.ofBijective representativeClass
    ⟨representativeClass_injective, representativeClass_surjective⟩).symm

def orthogonalSixLoops : π_ 1 (OrthogonalOperators 6) 1 ≃ Bool :=
  (OrthogonalPolygon.bottDegreeShiftEquiv 0 (1 : OrthogonalOperators 6)
    (OrthogonalExponential.exp (Real.pi • baseStructure.val))
    (by simpa only [inv_one, one_mul] using OrthogonalComplexStructures.exp_pi baseStructure)
    baseStructure (by decide)).symm.trans
      (HomotopyGroup.pi0EquivZerothHomotopy.trans componentsEquiv)

end Wikipedia.HopfProblem.DegreeCollapse.RankSixComponents
