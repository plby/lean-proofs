import Wikipedia.NoExoticSixSphere.InducedHomotopyMap

/-!
# Native higher homotopy groups under an actual homeomorphism

Both directions are induced by the homeomorphism and its inverse. The inverse
identities hold already for generalized loops, and multiplication is the native
homotopy-group multiplication.
-/

namespace Wikipedia.HopfProblem.OrbitPair.HigherHomotopyCoordinates

open NoExoticSixSphere

variable {N Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

theorem map_homeomorph_leftInverse (e : Y ≃ₜ Z) (y : Y) :
    Function.LeftInverse
      (HigherHomotopy.map (N := N) (e.symm : C(Z, Y)) (e.symm_apply_apply y))
      (HigherHomotopy.map (N := N) (e : C(Y, Z)) (y := y) rfl) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro p
  apply congrArg (fun q : GenLoop N Y y ↦ (Quotient.mk' q : HomotopyGroup N Y y))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact e.symm_apply_apply (p.val t)

theorem map_homeomorph_rightInverse (e : Y ≃ₜ Z) (y : Y) :
    Function.RightInverse
      (HigherHomotopy.map (N := N) (e.symm : C(Z, Y)) (e.symm_apply_apply y))
      (HigherHomotopy.map (N := N) (e : C(Y, Z)) (y := y) rfl) := by
  intro c
  refine Quotient.inductionOn c ?_
  intro p
  apply congrArg (fun q : GenLoop N Z (e y) ↦
    (Quotient.mk' q : HomotopyGroup N Z (e y)))
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact e.apply_symm_apply (p.val t)

noncomputable def homeomorphEquiv (N : Type*) (e : Y ≃ₜ Z) (y : Y) :
    HomotopyGroup N Y y ≃ HomotopyGroup N Z (e y) where
  toFun := HigherHomotopy.map (e : C(Y, Z)) rfl
  invFun := HigherHomotopy.map (e.symm : C(Z, Y)) (e.symm_apply_apply y)
  left_inv := map_homeomorph_leftInverse e y
  right_inv := map_homeomorph_rightInverse e y

noncomputable def homeomorphMulEquiv (N : Type*) [DecidableEq N] [Nonempty N]
    (e : Y ≃ₜ Z) (y : Y) : HomotopyGroup N Y y ≃* HomotopyGroup N Z (e y) where
  toEquiv := homeomorphEquiv N e y
  map_mul' := HigherHomotopy.map_mul (e : C(Y, Z)) rfl

end Wikipedia.HopfProblem.OrbitPair.HigherHomotopyCoordinates
