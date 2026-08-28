import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexOrientationGeneratorsSwapLastBasic

/-!
# The sign of the last-vertex swap in the native third homotopy group

Affine interpolation in the actual tetrahedron joins the swapped simplex
quotient to the reflected cube quotient. Its common zero coordinate on each
cube facet makes this a homotopy relative to the whole cube boundary.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] {x : X}

/-- An actual homotopy relative to the entire native cube boundary, from the
last-vertex swap to reversal of the last cubical coordinate. -/
def basedThreeSimplexSwapLast_loopHomotopy (τ : BasedThreeSimplex x) :
    (basedThreeSimplexLoop (basedThreeSimplexSwapLast τ)).val.HomotopyRel
      (GenLoop.symmAt (2 : Fin 3) (basedThreeSimplexLoop τ)).val
      (Cube.boundary (Fin 3)) where
  toFun z := τ.val (tetrahedronSimplexBlend z.1
    (threeSimplexSwapLast (threeSimplexQuotient z.2))
    (threeSimplexQuotient (cubeThirdLastReverse z.2)))
  continuous_toFun := τ.val.continuous.comp
    (tetrahedronSimplexBlendMap (threeSimplexSwapLast.comp threeSimplexQuotient)
      (threeSimplexQuotient.comp cubeThirdLastReverse)).continuous
  map_zero_left u := by
    change τ.val (tetrahedronSimplexBlend 0 _ _) = _
    rw [tetrahedronSimplexBlend_zero]
    rfl
  map_one_left u := by
    change τ.val (tetrahedronSimplexBlend 1 _ _) =
      GenLoop.symmAt (2 : Fin 3) (basedThreeSimplexLoop τ) u
    rw [tetrahedronSimplexBlend_one, symmAt_last_apply]
    rfl
  prop' t u hu := by
    obtain ⟨i, ha, hb⟩ := threeSimplexSwapLast_commonZero u hu
    exact (τ.property _ ⟨i,
      tetrahedronSimplexBlend_zero_coordinate t _ _ i ha hb⟩).trans
      ((basedThreeSimplexLoop (basedThreeSimplexSwapLast τ)).property u hu).symm

/-- Swapping the last two vertices gives the negative of the original class
in Mathlib's actual third homotopy group. -/
theorem basedThreeSimplexSwapLast_class (τ : BasedThreeSimplex x) :
    basedThreeSimplexClass (basedThreeSimplexSwapLast τ) = -basedThreeSimplexClass τ := by
  have h : (⟦basedThreeSimplexLoop (basedThreeSimplexSwapLast τ)⟧ : π_ 3 X x) =
      ⟦GenLoop.symmAt (2 : Fin 3) (basedThreeSimplexLoop τ)⟧ :=
    Quotient.sound ⟨basedThreeSimplexSwapLast_loopHomotopy τ⟩
  exact congrArg Additive.ofMul
    (h.trans (HomotopyGroup.inv_spec
      (i := (2 : Fin 3)) (p := basedThreeSimplexLoop τ)).symm)

end Wikipedia.HopfProblem.ThirdHurewicz
