import Wikipedia.NoExoticSixSphere.PartialFrameOverlapCylinder
import Wikipedia.NoExoticSixSphere.PartialFrameEuclideanCharts
import Wikipedia.NoExoticSixSphere.ZeroProductHomotopy

/-!
# Actual patch and overlap retractions with specified inverse maps

The patch retraction is its original fiber coordinate. The overlap retraction
uses the zero section of the real cylinder coordinate, so its inverse lies
exactly on the equator. Thus the two reduced inclusion maps are the second
projection and the actual equatorial transition, respectively.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnBundle

open GLOrthonormalization ContinuousMap

def patchHomotopyEquiv {n r : ℕ} (v : UnitSphere (Vector (r + 1)))
    (c : UnitSphere (Vector (n + 1))) : Patch v c ≃ₕ Space n r :=
  (sourceEuclideanHomeomorph v c).toHomotopyEquiv.trans
    (ZeroProduct.homotopyEquiv (Vector n) (Space n r))

theorem patchHomotopyEquiv_toFun {n r : ℕ} (v : UnitSphere (Vector (r + 1)))
    (c : UnitSphere (Vector (n + 1))) :
    (patchHomotopyEquiv v c).toFun = patchFiber v c := rfl

def overlapHomotopyEquiv {r : ℕ} (n : ℕ) (v : UnitSphere (Vector (r + 1))) :
    Overlap v (spherePole (n + 1)) (antipode (spherePole (n + 1))) ≃ₕ
      Sphere n × Space (n + 1) r :=
  (overlapCylinderHomeomorph n v).toHomotopyEquiv.trans
    ((ZeroProduct.homotopyEquiv ℝ (Sphere n)).prodCongr (HomotopyEquiv.refl _))

theorem overlapHomotopyEquiv_symm_val {r : ℕ} (n : ℕ)
    (v : UnitSphere (Vector (r + 1))) (p : Sphere n × Space (n + 1) r) :
    ((overlapHomotopyEquiv n v).symm p).val =
      fromCoordinates v (spherePole (n + 1)) (SphereCylinder.point n (0, p.1), p.2) := rfl

theorem overlapLeft_reduced {r : ℕ} (n : ℕ) (v : UnitSphere (Vector (r + 1))) :
    (patchFiber v (spherePole (n + 1))).comp
      ((overlapLeft v (spherePole (n + 1)) (antipode (spherePole (n + 1)))).comp
        (overlapHomotopyEquiv n v).symm.toFun) =
      (ContinuousMap.snd : C(Sphere n × Space (n + 1) r, Space (n + 1) r)) := by
  apply ContinuousMap.ext
  intro p
  change (toCoordinates v (spherePole (n + 1))
    (fromCoordinates v (spherePole (n + 1)) (SphereCylinder.point n (0, p.1), p.2))).2 = p.2
  rw [toCoordinates_fromCoordinates]

def equatorialTransition {r : ℕ} (n : ℕ) (v : UnitSphere (Vector (r + 1))) :
    C(Sphere n × Space (n + 1) r, Space (n + 1) r) :=
  (patchFiber v (antipode (spherePole (n + 1)))).comp
    ((overlapRight v (spherePole (n + 1)) (antipode (spherePole (n + 1)))).comp
      (overlapHomotopyEquiv n v).symm.toFun)

theorem equatorialTransition_apply {r : ℕ} (n : ℕ)
    (v : UnitSphere (Vector (r + 1))) (p : Sphere n × Space (n + 1) r) :
    equatorialTransition n v p = transition v (antipode (spherePole (n + 1)))
      (spherePole (n + 1)) (SphereCylinder.point n (0, p.1)) p.2 := rfl

end NoExoticSixSphere.Stiefel.ColumnBundle
