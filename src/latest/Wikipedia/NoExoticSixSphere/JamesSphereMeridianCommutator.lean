import Wikipedia.NoExoticSixSphere.SphereMooreCommutatorSmash
import Wikipedia.NoExoticSixSphere.JamesSphereSuspensionComparison
import Wikipedia.NoExoticSixSphere.SmoothSphereCubeHomotopy

/-!
# The actual meridian commutator gives a based sphere class

Use the original duration-weighted Moore meridians, the constructed
axes contraction, and the actual smash-sphere quotient. This produces
a based sphere map into Moore loops. In dimension three, normalization,
native currying, and the original coordinate reordering give an explicit
native seven-cube in S4. Its class has not yet been identified with the
original S4 attaching class, nor has its Hopf coordinate been evaluated.
-/

noncomputable section

open scoped Topology unitInterval

namespace NoExoticSixSphere.JamesSphere.MeridianCommutator

def meridians (n : ℕ) : C(Sphere n, Moore.Loop (spherePole (n + 1))) :=
  ⟨mooreGenerator n, continuous_mooreGenerator n⟩

theorem meridians_pole (n : ℕ) : meridians n (spherePole n) = 1 := mooreGenerator_pole n

def sphereMap (n : ℕ) : C(Sphere (n + n), Moore.Loop (spherePole (n + 1))) :=
  SphereMooreCommutator.smashMap n (meridians n) (meridians n)
    (meridians_pole n) (meridians_pole n)

theorem sphereMap_pole (n : ℕ) : sphereMap n (spherePole (n + n)) = 1 :=
  SphereMooreCommutator.smashMap_pole n (meridians n) (meridians n)
    (meridians_pole n) (meridians_pole n)

def factorHomotopy (n : ℕ) :
    (SphereMooreCommutator.commutator n (meridians n) (meridians n)).HomotopyRel
      ((sphereMap n).comp (SecondStage.arrayPairing n)) {SphereMooreCommutator.point n} :=
  SphereMooreCommutator.factorHomotopy n (meridians n) (meridians n)
    (meridians_pole n) (meridians_pole n)

def sixLoop : GenLoop (Fin 6) (Moore.Loop (spherePole 4)) 1 :=
  SmoothCube.toGenLoop ⟨sphereMap 3, sphereMap_pole 3⟩

def sixClass : π_ 6 (Moore.Loop (spherePole 4)) 1 := Quotient.mk' sixLoop

def fourLoop : GenLoop (Fin 7) (Sphere 4) (spherePole 4) :=
  HigherHomotopy.genLoopMap (SuspensionCoordinates.reorder 3 : C(_, _))
    (SuspensionCoordinates.reorder_pole 3)
    (GeneralizedLoopCurrying.uncurry
      (HigherHomotopy.genLoopMap Moore.Loop.normalizationMap Moore.Loop.toPath_one sixLoop))

theorem fourLoop_apply (u : Fin 7 → I) :
    fourLoop u = SuspensionCoordinates.reorder 3
      (Moore.Loop.toPath (sphereMap 3 (SmoothCube.quotient 6 (Fin.tail u))) (u 0)) := rfl

def fourClass : π_ 7 (Sphere 4) (spherePole 4) := Quotient.mk' fourLoop

theorem fourClass_comparison : fourClass =
    SuspensionComparison.coordinateEquiv 3 7
      (GeneralizedLoopCurrying.homotopyMulEquiv 6 (spherePole 4)
        (HigherHomotopy.map (N := Fin 6) Moore.Loop.normalizationMap
          Moore.Loop.toPath_one sixClass)) := rfl

end NoExoticSixSphere.JamesSphere.MeridianCommutator
