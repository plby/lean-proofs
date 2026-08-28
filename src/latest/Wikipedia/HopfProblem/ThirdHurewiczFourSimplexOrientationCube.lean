import Wikipedia.HopfProblem.ThirdHurewiczFourSimplexOrientationCubeRotations

/-!
# Native third-homotopy signs of cube permutations

The positive cycle is homotopic to the identity through actual maps of the
cube boundary. Composing it with one coordinate reversal therefore gives
the native group inverse, with no Hurewicz detection hypothesis.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- Two embedded quarter turns give an actual relative homotopy for every
native three-dimensional generalized loop. -/
def cyclicThreeLoop_homotopy (p : GenLoop (Fin 3) X x) :
    p.val.HomotopyRel (cyclicThreeLoop p).val (Cube.boundary (Fin 3)) where
  toFun z := p (cubeThirdCycleHomotopyMap z)
  continuous_toFun := p.val.continuous.comp cubeThirdCycleHomotopyMap.continuous
  map_zero_left u := congrArg p (cubeThirdCycleHomotopyMap_zero u)
  map_one_left u := congrArg p (cubeThirdCycleHomotopyMap_one u)
  prop' t u hu := (p.property _ (cubeThirdCycleHomotopyMap_boundary t u hu)).trans
    (p.property u hu).symm

/-- The positive cube coordinate cycle acts trivially on native `π₃`. -/
theorem cyclicThreeLoop_class (p : GenLoop (Fin 3) X x) :
    (⟦cyclicThreeLoop p⟧ : π_ 3 X x) = ⟦p⟧ := by
  have h : (⟦p⟧ : π_ 3 X x) = ⟦cyclicThreeLoop p⟧ :=
    Quotient.sound (show GenLoop.Homotopic p (cyclicThreeLoop p) from
      ⟨cyclicThreeLoop_homotopy p⟩)
  exact h.symm

/-- The cyclic reversal is literally a positive cycle of the reflected loop. -/
theorem cyclicReverseThreeLoop_eq (p : GenLoop (Fin 3) X x) :
    cyclicReverseThreeLoop p = cyclicThreeLoop (GenLoop.symmAt (2 : Fin 3) p) := by
  apply GenLoop.ext
  intro u
  change p ![u 1, u 2, σ (u 0)] =
    p (fun j => if j = (2 : Fin 3) then σ (![u 1, u 2, u 0] 2)
      else ![u 1, u 2, u 0] j)
  congr 1
  funext i
  fin_cases i <;> simp

/-- The cycle followed by one reflection acts by the native group inverse. -/
theorem cyclicReverseThreeLoop_class (p : GenLoop (Fin 3) X x) :
    (⟦cyclicReverseThreeLoop p⟧ : π_ 3 X x) =
      ((·⁻¹) : π_ 3 X x → π_ 3 X x) ⟦p⟧ := by
  rw [cyclicReverseThreeLoop_eq, cyclicThreeLoop_class]
  exact (HomotopyGroup.inv_spec (i := (2 : Fin 3)) (p := p)).symm

end Wikipedia.HopfProblem.ThirdHurewicz
