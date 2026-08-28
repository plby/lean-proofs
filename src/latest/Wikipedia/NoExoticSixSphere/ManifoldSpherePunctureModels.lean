import Wikipedia.NoExoticSixSphere.ManifoldSpherePunctureCoordinates
import Wikipedia.NoExoticSixSphere.SphereCylinderPuncturedCaps
import Wikipedia.NoExoticSixSphere.ManifoldPuncturedBallHomotopy

/-!
# Sphere models of the actual punctured components

The cap and ball models are transported by the genuine cylinder point map.
Their inverse parametrizations are explicit: exterior time slices for the
caps and the original chart's half-radius spheres for the singularity balls.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily.ParityBallSystem

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g)

theorem puncturedPiece_cap (b : Bool) :
    P.puncturedPiece (.inl b) = SphereCylinder.puncturedCap 3 b := by
  rw [P.puncturedPiece_eq_sdiff]
  rfl

theorem puncturedPiece_ball (q : singularParameters (n := 6) g) :
    P.puncturedPiece (.inr q) = SphereCylinder.point 3 '' (P.ball q).puncturedOpenRegion := by
  rw [P.puncturedPiece_eq_sdiff]
  change SphereCylinder.point 3 '' (P.ball q).openRegion \ {SphereCylinder.point 3 q.val} =
    SphereCylinder.point 3 '' ((P.ball q).openRegion \ {q.val})
  rw [image_sdiff (SphereCylinder.injective_point 3), image_singleton]

def puncturedBallImageHomeomorph (q : singularParameters (n := 6) g) :
    (P.ball q).puncturedOpenRegion ≃ₜ P.puncturedPiece (.inr q) :=
  ((SphereCylinder.isOpenEmbedding_point 3).isEmbedding.homeomorphImage
    (P.ball q).puncturedOpenRegion).trans (Homeomorph.setCongr (P.puncturedPiece_ball q).symm)

def pieceSphereEquiv : (i : BoundaryIndex g) → P.puncturedPiece i ≃ₕ Sphere 3
  | .inl b => (Homeomorph.setCongr (P.puncturedPiece_cap b)).toHomotopyEquiv.trans
      (SphereCylinder.capSphereEquiv 3 b)
  | .inr q => (P.puncturedBallImageHomeomorph q).symm.toHomotopyEquiv.trans
      (P.ball q).puncturedSphereEquiv

theorem pieceSphereEquiv_symm_cap (b : Bool) (s : Sphere 3) :
    ((P.pieceSphereEquiv (.inl b)).symm s).val =
      SphereCylinder.point 3 ((SphereCylinder.capBaseTime b).val, s) := rfl

theorem pieceSphereEquiv_symm_ball (q : singularParameters (n := 6) g) (s : Sphere 3) :
    ((P.pieceSphereEquiv (.inr q)).symm s).val =
      SphereCylinder.point 3 ((P.ball q).chart ((1 / 2 : ℝ) • s.val)) := rfl

def regularModelSphere (i : BoundaryIndex g) : C(Sphere 3, RegularParameters g) :=
  (sphereRegularHomeomorph g : C(_, _)).comp
    ((P.puncturedPieceInclusion i).comp (P.pieceSphereEquiv i).symm.toFun)

theorem regularModelSphere_cap (b : Bool) (s : Sphere 3) :
    (P.regularModelSphere (.inl b) s).val = ((SphereCylinder.capBaseTime b).val, s) :=
  SphereCylinder.inverse_point 3 _

theorem regularModelSphere_ball (q : singularParameters (n := 6) g) (s : Sphere 3) :
    (P.regularModelSphere (.inr q) s).val = (P.ball q).chart ((1 / 2 : ℝ) • s.val) :=
  SphereCylinder.inverse_point 3 _

theorem regularModelSphere_link_eq (q : singularParameters (n := 6) g) :
    P.regularModelSphere (.inr q) = (P.ball q).regularSmallLink := by
  apply ContinuousMap.ext
  intro s
  apply Subtype.ext
  exact P.regularModelSphere_ball q s

end NoExoticSixSphere.SphereFamily.ParityBallSystem
