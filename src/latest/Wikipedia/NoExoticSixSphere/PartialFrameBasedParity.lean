import Wikipedia.NoExoticSixSphere.PartialFrameSphereObstruction

/-!
# Frame parity completely classifies based sphere maps

Injectivity of the actual native third-group isomorphism detects homotopies
of two loops, not just nullhomotopies. The genuine cube-to-sphere quotient
then gives a sphere homotopy fixing the common basepoint.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse

theorem thirdObstruction_eq_iff (r : ℕ) (a : Space (3 + (r + 2)) (r + 2))
    (p q : GenLoop (Fin 3) (Space (3 + (r + 2)) (r + 2)) a) :
    thirdObstruction r a p = thirdObstruction r a q ↔ GenLoop.Homotopic p q := by
  constructor
  · intro h
    have he := (stableThirdHomotopyEquivZModTwo r a).injective h
    change (Quotient.mk' p : HomotopyGroup (Fin 3) (Space (3 + (r + 2)) (r + 2)) a) =
      Quotient.mk' q at he
    exact Quotient.exact he
  · intro h
    exact thirdObstruction_homotopic r a h

def basedCubeWithPoint {X : Type*} [TopologicalSpace X] (a : X) (f : C(Sphere 3, X))
    (hf : f (SphereCube.point 3) = a) : GenLoop (Fin 3) X a :=
  ⟨f.comp (SphereCube.quotient 3), fun x hx ↦
    (congrArg f (SphereCube.quotient_boundary 3 x hx)).trans hf⟩

theorem thirdObstruction_basedCubeWithPoint (r : ℕ) (a : Space (3 + (r + 2)) (r + 2))
    (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) (hf : f (SphereCube.point 3) = a) :
    thirdObstruction r a (basedCubeWithPoint a f hf) = sphereThirdObstruction r f := by
  subst a
  rfl

theorem sphereThirdObstruction_eq_iff_homotopicRel (r : ℕ)
    (f g : C(Sphere 3, Space (3 + (r + 2)) (r + 2)))
    (hfg : f (SphereCube.point 3) = g (SphereCube.point 3)) :
    sphereThirdObstruction r f = sphereThirdObstruction r g ↔
      f.HomotopicRel g {SphereCube.point 3} := by
  let a := f (SphereCube.point 3)
  let p := basedCubeWithPoint a f rfl
  let q := basedCubeWithPoint a g hfg.symm
  have hp : thirdObstruction r a p = sphereThirdObstruction r f :=
    thirdObstruction_basedCubeWithPoint r a f rfl
  have hq : thirdObstruction r a q = sphereThirdObstruction r g :=
    thirdObstruction_basedCubeWithPoint r a g hfg.symm
  rw [← hp, ← hq, thirdObstruction_eq_iff]
  exact (SphereCubeHomotopy.homotopicRel_iff (by decide : 0 < 3) f g).symm

end NoExoticSixSphere.Stiefel
