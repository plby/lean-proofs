import Wikipedia.SmoothSixDPoincare.CollaredHandleEmbedding
import Wikipedia.SmoothSixDPoincare.HandleCollarCoordinates

/-!
# The whole new-face collar inside the actual handle attachment

Compose the explicit injective corner coordinates with the original
collar-plus-handle embedding. Its zero end is precisely the original new
face, and its corner agrees point-for-point with the original old collar.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.CollaredHandleEmbedding

open CollaredDiskAttachment (Disk Sphere Handle)

variable {E F X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [TopologicalSpace Y]
  (j : C(Sphere E × Disk F, X)) (i : C(X, Y)) (C : InwardBoundaryCollar i)
  (hi : Injective i) (hj : Injective j)

def newCollarMap : C((Disk E × Sphere F) × unitInterval, FaceAttachment.Space (faceMap j i)) :=
  (parametrization j i C hi hj).comp HandleCollarCoordinates.coordinates

theorem newCollarMap_isClosedEmbedding [T2Space Y] [CompactSpace Y] :
    IsClosedEmbedding (newCollarMap j i C hi hj) :=
  (parametrization_isClosedEmbedding j i C hi hj).comp
    HandleCollarCoordinates.coordinates_isClosedEmbedding

theorem newCollarMap_zero (u : Disk E) (v : Sphere F) :
    newCollarMap j i C hi hj ((u, v), 0) =
      FaceAttachment.handleMap (faceMap j i) (u, ⟨v.val, sphere_subset_closedBall v.property⟩) :=
  (congrArg (parametrization j i C hi hj) (HandleCollarCoordinates.coordinates_zero u v)).trans
    (parametrization_new j i C hi hj _)

theorem newCollarMap_corner (u : Sphere E) (v : Sphere F) (t : unitInterval) :
    newCollarMap j i C hi hj ((⟨u.val, sphere_subset_closedBall u.property⟩, v), t) =
      FaceAttachment.oldMap (faceMap j i)
        (C.map (j (u, ⟨v.val, sphere_subset_closedBall v.property⟩),
          HandleCollarCoordinates.oldTime t)) :=
  (congrArg (parametrization j i C hi hj)
    (HandleCollarCoordinates.coordinates_corner u v t)).trans
      (parametrization_old j i C hi hj _)

end Wikipedia.SmoothSixDPoincare.CollaredHandleEmbedding
