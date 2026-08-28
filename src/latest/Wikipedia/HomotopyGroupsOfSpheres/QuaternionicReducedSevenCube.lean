import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicExplicitSevenCube
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottRankReduction

/-!
# Concrete native seventh-dimensional cubes in Sp(2)

Apply the explicit rank reduction before dividing by the reference family.
The four boundary identities survive the reduction. Composing with the
cross-product five-sphere parameter and uncurrying gives actual Sp(2) cubes.
Their generator property and projected degree are not asserted here.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicSymmetricMatrices QuaternionicColumns

def reducedRawCubeFamily : C(Space (Fin 3) × (Fin 2 → I), SpGroup (Fin 2)) :=
  reducedRotation.comp cubeAngles

private def referenceCube :
    C(Space (Fin 3) × (Fin 2 → I), Space (Fin 3) × (Fin 2 → I)) :=
  ⟨fun z ↦ (identity, z.2), continuous_const.prodMk continuous_snd⟩

def reducedCubeFamily : C(Space (Fin 3) × (Fin 2 → I), SpGroup (Fin 2)) :=
  reducedRawCubeFamily * (reducedRawCubeFamily.comp referenceCube)⁻¹

theorem reducedRawCubeFamily_boundary (B : Space (Fin 3)) (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) :
    reducedRawCubeFamily (B, u) = reducedRawCubeFamily (identity, u) := by
  apply congrArg reduce
  apply Subtype.ext
  have h := twoCubeFamily_boundary B u hu
  exact mul_inv_eq_one.mp h

theorem reducedCubeFamily_boundary (B : Space (Fin 3)) (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) : reducedCubeFamily (B, u) = 1 := by
  change reducedRawCubeFamily (B, u) * (reducedRawCubeFamily (identity, u))⁻¹ = 1
  rw [reducedRawCubeFamily_boundary B u hu, mul_inv_cancel]

def reducedTwoCube (B : Space (Fin 3)) : GenLoop (Fin 2) (SpGroup (Fin 2)) 1 :=
  ⟨reducedCubeFamily.curry B, reducedCubeFamily_boundary B⟩

def reducedTwoCubeMap : C(Space (Fin 3), GenLoop (Fin 2) (SpGroup (Fin 2)) 1) where
  toFun := reducedTwoCube
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact reducedCubeFamily.curry.continuous

theorem reducedTwoCubeMap_apply (B : Space (Fin 3)) (u : Fin 2 → I) :
    reducedTwoCubeMap B u =
      reducedRotation (((u 0 : ℝ) * Real.pi, (u 1 : ℝ) * Real.pi), B) *
        (reducedRotation (((u 0 : ℝ) * Real.pi, (u 1 : ℝ) * Real.pi), identity))⁻¹ := rfl

theorem reducedTwoCubeMap_identity : reducedTwoCubeMap identity = GenLoop.const := by
  apply GenLoop.ext
  intro u
  exact mul_inv_cancel _

end QuaternionicBottMatrix

namespace ComplexCrossProductUnitary

open QuaternionicColumns

def reducedDoubleLoopFamily : C(UnitSphere, GenLoop (Fin 2) (SpGroup (Fin 2)) 1) :=
  QuaternionicBottMatrix.reducedTwoCubeMap.comp symmetricMap

theorem reducedDoubleLoopFamily_axis : reducedDoubleLoopFamily axis = GenLoop.const := by
  change QuaternionicBottMatrix.reducedTwoCubeMap (symmetricMap axis) = GenLoop.const
  rw [symmetricMap_axis, QuaternionicBottMatrix.reducedTwoCubeMap_identity]

def reducedSevenCubeSum (p : GenLoop (Fin 5) UnitSphere axis) :
    GenLoop (Fin 5 ⊕ Fin 2) (SpGroup (Fin 2)) 1 :=
  GenLoop.genLoopGenLoopEquiv 1
    (pointedMapGenLoop reducedDoubleLoopFamily axis GenLoop.const reducedDoubleLoopFamily_axis p)

theorem reducedSevenCubeSum_apply (p : GenLoop (Fin 5) UnitSphere axis)
    (u : Fin 5 → I) (v : Fin 2 → I) :
    reducedSevenCubeSum p (Sum.elim u v) =
      QuaternionicBottMatrix.reducedTwoCubeMap (symmetricMap (p u)) v := rfl

def reducedSevenCube (p : GenLoop (Fin 5) UnitSphere axis) :
    GenLoop (Fin 7) (SpGroup (Fin 2)) 1 :=
  GenLoop.congr 1 finSumFinEquiv (reducedSevenCubeSum p)

end ComplexCrossProductUnitary
end Wikipedia.HomotopyGroupsOfSpheres
