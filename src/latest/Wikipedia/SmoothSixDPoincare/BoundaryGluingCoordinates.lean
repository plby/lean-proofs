import Wikipedia.SmoothSixDPoincare.BoundaryGluing

/-!
# Coordinate changes and empty endpoints for actual boundary gluings

Homeomorphisms of the two bodies and their common boundary induce the
specified map on every point of the glued space. Gluing an empty body
creates no further identifications and recovers the other whole body.
-/

noncomputable section

open Set Function Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.BoundaryGluing

variable {B X Y B' X' Y' : Type*}
  [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace B'] [TopologicalSpace X'] [TopologicalSpace Y']
  (i : C(B, X)) (j : C(B, Y)) (i' : C(B', X')) (j' : C(B', Y'))
  (eB : B ≃ₜ B') (eX : X ≃ₜ X') (eY : Y ≃ₜ Y')
  (hi : ∀ b, eX (i b) = i' (eB b)) (hj : ∀ b, eY (j b) = j' (eB b))

def congr : Space i j ≃ₜ Space i' j' := by
  apply Homeomorph.Quot.congr (eX.sumCongr eY)
  rintro (x | y) (x' | y')
  · exact Iff.rfl
  · change (∃ b, i b = x ∧ j b = y') ↔ ∃ b, i' b = eX x ∧ j' b = eY y'
    constructor
    · rintro ⟨b, rfl, rfl⟩
      exact ⟨eB b, (hi b).symm, (hj b).symm⟩
    · rintro ⟨b, hb, hb'⟩
      refine ⟨eB.symm b, eX.injective ?_, eY.injective ?_⟩
      · exact (hi _).trans ((congrArg i' (eB.apply_symm_apply b)).trans hb)
      · exact (hj _).trans ((congrArg j' (eB.apply_symm_apply b)).trans hb')
  · exact Iff.rfl
  · exact Iff.rfl

theorem congr_left (x : X) :
    congr i j i' j' eB eX eY hi hj (left i j x) = left i' j' (eX x) := rfl

theorem congr_right (y : Y) :
    congr i j i' j' eB eX eY hi hj (right i j y) = right i' j' (eY y) := rfl

variable [IsEmpty Y]

def rightEmptyHomeomorph : Space i j ≃ₜ X where
  toFun := desc i j (ContinuousMap.id X) ⟨isEmptyElim, by fun_prop⟩
    (fun b => isEmptyElim (j b))
  invFun := left i j
  left_inv q := by
    induction q using Quot.inductionOn with
    | _ q => cases q with
      | inl x => rfl
      | inr y => exact isEmptyElim y
  right_inv _ := rfl
  continuous_toFun := (desc i j _ _ _).continuous
  continuous_invFun := (left i j).continuous

theorem rightEmptyHomeomorph_left (x : X) : rightEmptyHomeomorph i j (left i j x) = x := rfl

omit [IsEmpty Y] in
def leftEmptyHomeomorph [IsEmpty X] : Space i j ≃ₜ Y :=
  (commute i j).trans (rightEmptyHomeomorph j i)

omit [IsEmpty Y] in
theorem leftEmptyHomeomorph_right [IsEmpty X] (y : Y) :
    leftEmptyHomeomorph i j (right i j y) = y := rfl

end Wikipedia.SmoothSixDPoincare.BoundaryGluing
