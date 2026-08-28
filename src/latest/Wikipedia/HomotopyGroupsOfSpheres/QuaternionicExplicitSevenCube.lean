import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicDoubleBottCube
import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps

/-!
# The cross-product input gives an actual seventh-dimensional symplectic cube

Compose the concrete five-sphere map with the explicit based two-cube family,
then use native cubical uncurrying and coordinate reindexing. The result is
an actual cube in Sp(3), without assuming a generator or a degree calculation.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicColumns

def doubleLoopFamily : C(UnitSphere, GenLoop (Fin 2) (SpGroup (Fin 3)) 1) :=
  QuaternionicBottMatrix.twoCubeMap.comp symmetricMap

theorem doubleLoopFamily_axis : doubleLoopFamily axis = GenLoop.const := by
  change QuaternionicBottMatrix.twoCubeMap (symmetricMap axis) = GenLoop.const
  rw [symmetricMap_axis, QuaternionicBottMatrix.twoCubeMap_identity]

def sevenCubeSum (p : GenLoop (Fin 5) UnitSphere axis) :
    GenLoop (Fin 5 ⊕ Fin 2) (SpGroup (Fin 3)) 1 :=
  GenLoop.genLoopGenLoopEquiv 1
    (pointedMapGenLoop doubleLoopFamily axis GenLoop.const doubleLoopFamily_axis p)

theorem sevenCubeSum_apply (p : GenLoop (Fin 5) UnitSphere axis)
    (u : Fin 5 → I) (v : Fin 2 → I) :
    sevenCubeSum p (Sum.elim u v) =
      QuaternionicBottMatrix.basedRotation
        ((v 0 : ℝ) * Real.pi) ((v 1 : ℝ) * Real.pi) (symmetricMap (p u)) := rfl

def sevenCube (p : GenLoop (Fin 5) UnitSphere axis) :
    GenLoop (Fin 7) (SpGroup (Fin 3)) 1 :=
  GenLoop.congr 1 finSumFinEquiv (sevenCubeSum p)

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
