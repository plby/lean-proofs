import Wikipedia.NoExoticSixSphere.JamesSphereLoopMap
import Wikipedia.NoExoticSixSphere.CubicalSphereSuspension

/-!
# Exact reordering of the James and cubical suspension coordinates

The James generator appends its line coordinate; the native cubical
suspension puts that coordinate first. An explicit sphere homeomorphism
reorders the two product coordinates on the whole compactification,
including the collapsed point. No orientation or homotopy identity of
this coordinate change is assumed.
-/

noncomputable section

open scoped OnePoint unitInterval

namespace NoExoticSixSphere.JamesSphere.SuspensionCoordinates

open CubicalProductSuspension

def jamesSphereHomeomorph (n : ℕ) :
    OnePoint (EuclideanSpace ℝ (Fin n) × Line) ≃ₜ Sphere (n + 1) :=
  (EuclideanFactorProduct.productCoordinates n 1).onePointCongr.trans
    (euclideanOnePointSphere (n + 1))

theorem jamesSphereHomeomorph_infty (n : ℕ) :
    jamesSphereHomeomorph n ∞ = spherePole (n + 1) :=
  euclideanOnePointSphere_infty (n + 1)

def reorder (n : ℕ) : Sphere (n + 1) ≃ₜ Sphere (n + 1) :=
  (jamesSphereHomeomorph n).symm.trans
    ((Homeomorph.prodComm (EuclideanSpace ℝ (Fin n)) Line).onePointCongr.trans
      (CubicalSphereSuspension.sphereHomeomorph n))

theorem reorder_product (n : ℕ) (x : OnePoint (EuclideanSpace ℝ (Fin n)))
    (s : OnePoint Line) :
    reorder n (jamesSphereHomeomorph n (OnePointProduct.map (x, s))) =
      CubicalSphereSuspension.sphereHomeomorph n (OnePointProduct.map (s, x)) := by
  change CubicalSphereSuspension.sphereHomeomorph n
    ((Homeomorph.prodComm (EuclideanSpace ℝ (Fin n)) Line).onePointCongr
      ((jamesSphereHomeomorph n).symm
        (jamesSphereHomeomorph n (OnePointProduct.map (x, s))))) = _
  rw [Homeomorph.symm_apply_apply, OnePointProduct.map_swap]

theorem reorder_pole (n : ℕ) : reorder n (spherePole (n + 1)) = spherePole (n + 1) := by
  have h := reorder_product n (∞ : OnePoint (EuclideanSpace ℝ (Fin n))) (∞ : OnePoint Line)
  simpa only [OnePointProduct.map_infty_left, jamesSphereHomeomorph_infty,
    CubicalSphereSuspension.sphereHomeomorph_infty] using h

theorem reorder_loopEvaluation (n : ℕ) (x : Sphere n) (t : unitInterval) :
    reorder n (loopEvaluation n (x, t)) =
      CubicalSphereSuspension.sphereHomeomorph n (OnePointProduct.map
        (clock t, (euclideanOnePointSphere n).symm x)) :=
  reorder_product n ((euclideanOnePointSphere n).symm x) (clock t)

end NoExoticSixSphere.JamesSphere.SuspensionCoordinates
