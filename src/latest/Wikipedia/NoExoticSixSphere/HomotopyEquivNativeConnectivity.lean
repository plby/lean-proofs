import Wikipedia.HopfProblem.OrbitPairSphereNullhomotopyCriterion
import Mathlib.Topology.Homotopy.Equiv

/-!
# Native homotopy vanishing under an actual homotopy equivalence

Native homotopy vanishing at every target point contracts all sphere maps.
An actual inverse homotopy transports these contractions to the source.
The disk criterion restores the selected basepoint, so no basepoint-change
isomorphism or triviality of its action is assumed.
-/

noncomputable section

open scoped Topology ContinuousMap
open Wikipedia.HopfProblem.OrbitPair.SphereNullhomotopy

namespace NoExoticSixSphere.HomotopyEquivNativeConnectivity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem sphere_nullhomotopic {n : ℕ} (hn : 0 < n)
    (hpi : ∀ x : X, Subsingleton (π_ n X x)) (f : C(Sphere n, X)) :
    f.Homotopic (ContinuousMap.const _ (f (spherePole n))) := by
  let x := f (spherePole n)
  let F : SmoothCube.BasedMap n X x := ⟨f, rfl⟩
  let K : SmoothCube.BasedMap n X x := ⟨ContinuousMap.const _ x, rfl⟩
  let : Subsingleton (π_ n X x) := hpi x
  obtain ⟨H⟩ := (SmoothCube.sphereClass_eq_iff hn F K).mp (Subsingleton.elim _ _)
  exact ⟨H.toHomotopy⟩

theorem subsingleton (e : X ≃ₕ Y) {n : ℕ} (hn : 0 < n)
    (hpi : ∀ y : Y, Subsingleton (π_ n Y y)) (x : X) : Subsingleton (π_ n X x) := by
  apply pi_subsingleton_of_sphere_nullhomotopies hn ?_ x
  intro f
  let g := e.toFun.comp f
  have hg := sphere_nullhomotopic hn hpi g
  have hleft : f.Homotopic (e.invFun.comp g) :=
    e.left_inv.symm.comp (ContinuousMap.Homotopic.refl f)
  exact ⟨e.invFun (g (spherePole n)),
    hleft.trans ((ContinuousMap.Homotopic.refl e.invFun).comp hg)⟩

end NoExoticSixSphere.HomotopyEquivNativeConnectivity
