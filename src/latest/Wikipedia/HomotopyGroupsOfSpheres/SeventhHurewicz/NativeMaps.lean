import Wikipedia.HopfProblem.SecondHurewiczNativeMapsLoops

/-!
# The native induced map on the seventh homotopy group

Continuous postcomposition of generalized loops descends through Mathlib's
actual boundary-relative homotopy quotient in dimension seven. Its native
concatenation law gives the group homomorphism, and the loop-space formula
uses the actual remaining six-coordinate generalized-loop space.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open SecondHurewicz

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace Z]

/-- The homomorphism on the actual seventh homotopy group induced by a continuous map. -/
def homotopyMap (f : C(X, Y)) (x : X) : π_ 7 X x →* π_ 7 Y (f x) where
  toFun := Quotient.map (mapGenLoop f x) (fun _ _ h => mapGenLoop_homotopic f x h)
  map_one' := by
    change (⟦mapGenLoop f x GenLoop.const⟧ : π_ 7 Y (f x)) = ⟦GenLoop.const⟧
    rw [mapGenLoop_const]
  map_mul' a b := by
    refine Quotient.inductionOn₂ a b fun p q => ?_
    exact (congrArg (Quotient.map (mapGenLoop f x)
      (fun _ _ h => mapGenLoop_homotopic f x h))
      (HomotopyGroup.mul_spec (i := (0 : Fin 7)) (p := p) (q := q))).trans
      ((congrArg (fun r : GenLoop (Fin 7) Y (f x) => (⟦r⟧ : π_ 7 Y (f x)))
        (mapGenLoop_transAt f x (0 : Fin 7) q p)).trans
        (HomotopyGroup.mul_spec (i := (0 : Fin 7))
          (p := mapGenLoop f x p) (q := mapGenLoop f x q)).symm)

/-- On a representative, the induced map is literal continuous postcomposition. -/
@[simp] theorem homotopyMap_mk (f : C(X, Y)) (x : X)
    (p : GenLoop (Fin 7) X x) :
    homotopyMap f x ⟦p⟧ = ⟦mapGenLoop f x p⟧ := rfl

@[simp] theorem homotopyMap_id (x : X) :
    homotopyMap (ContinuousMap.id X) x = MonoidHom.id (π_ 7 X x) := by
  apply MonoidHom.ext
  intro a
  refine Quotient.inductionOn a fun p => ?_
  change (⟦mapGenLoop (ContinuousMap.id X) x p⟧ : π_ 7 X x) = ⟦p⟧
  rw [mapGenLoop_id]
  rfl

@[simp] theorem homotopyMap_comp (f : C(X, Y)) (g : C(Y, Z)) (x : X) :
    homotopyMap (g.comp f) x = (homotopyMap g (f x)).comp (homotopyMap f x) := by
  apply MonoidHom.ext
  intro a
  refine Quotient.inductionOn a fun p => ?_
  change (⟦mapGenLoop (g.comp f) x p⟧ : π_ 7 Z (g (f x))) =
    ⟦mapGenLoop g (f x) (mapGenLoop f x p)⟧
  rw [mapGenLoop_comp]
  rfl

@[simp] theorem homotopyMap_const (x : X) (y : Y) :
    homotopyMap (ContinuousMap.const X y) x = 1 := by
  apply MonoidHom.ext
  intro a
  refine Quotient.inductionOn a fun p => ?_
  change (⟦mapGenLoop (ContinuousMap.const X y) x p⟧ : π_ 7 Y y) = (1 : π_ 7 Y y)
  rw [mapGenLoop_constMap]
  rfl

/-- Under the native loop-space description of `π₇`, the induced map is
the actual fundamental-group map of continuous postcomposition on the
remaining six-coordinate generalized-loop space. -/
theorem homotopyMap_toLoop (f : C(X, Y)) (x : X) (a : π_ 7 X x) :
    homotopyGroupEquivFundamentalGroup (0 : Fin 7) (homotopyMap f x a) =
      FundamentalGroup.map
        (mapGenLoop (N := {j : Fin 7 // j ≠ 0}) f x) GenLoop.const
        (homotopyGroupEquivFundamentalGroup (0 : Fin 7) a) := by
  refine Quotient.inductionOn a fun p => ?_
  change Path.Homotopic.Quotient.mk
      (GenLoop.toLoop (0 : Fin 7) (mapGenLoop f x p)) =
    Path.Homotopic.Quotient.mk ((GenLoop.toLoop (0 : Fin 7) p).map
      (mapGenLoop (N := {j : Fin 7 // j ≠ 0}) f x).continuous)
  rw [mapGenLoop_toLoop]
  rfl

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
