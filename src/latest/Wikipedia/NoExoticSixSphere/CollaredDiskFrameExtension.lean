import Wikipedia.NoExoticSixSphere.CollaredDiskFrameHomotopy

/-!
# A genuine collared disk operator extends the original boundary obstruction

The input normal and derivative operators are defined over the whole disk
and have disjoint ranges there. Their boundary values retain the actual
normal frame, tangent frame, and positive radial height. The constructed
combined map extends the collar boundary map. Its proved collar homotopy
then supplies an extension of the original source-twisted sphere frame.
-/

noncomputable section

open Function

namespace NoExoticSixSphere.CollaredDiskFrame

open GLOrthonormalization Stiefel SpanningDiskFrameCoordinates SphereThreeTangentFrame
open DiskBoundary
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {N k : ℕ}
  (a : C(Sphere 3, Vector k →L[ℝ] Vector N))
  (T : C(Sphere 3, Vector 3 →L[ℝ] Vector N))
  (v : C(Sphere 3, Vector N)) (c : C(Sphere 3, ℝ))
  (ha : ∀ s, Injective (a s)) (hT : ∀ s, Injective (T s))
  (hr : ∀ s, Disjoint (a s).range (T s).range) (hc : ∀ s, 0 < c s)
  (A : C(Disk (E := Vector 4), Vector k →L[ℝ] (Vector N × ℝ)))
  (D : C(Disk (E := Vector 4), Vector 4 →L[ℝ] (Vector N × ℝ)))
  (hA : ∀ x, Injective (A x)) (hD : ∀ x, Injective (D x))
  (hAD : ∀ x, Disjoint (A x).range (D x).range)
  (hboundary : ∀ s, A (boundaryToDisk s) =
    (ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp (a s))
  (htangent : ∀ s u, D (boundaryToDisk s) (operator s.val u) = (T s u, 0))
  (hradial : ∀ s, D (boundaryToDisk s) s.val = (v s, c s))

include hA hD hAD hboundary htangent hradial in
theorem extends_collarMap : Extends (collarMap a T v c ha hT hr hc) := by
  refine ⟨combinedMap A D hA hD hAD, ?_⟩
  intro s
  apply Subtype.ext
  change combined (A (boundaryToDisk s)) (D (boundaryToDisk s)) =
    combined ((ContinuousLinearMap.inl ℝ (Vector N) ℝ).comp (a s))
      (collarDerivative s (T s) (v s) (c s))
  rw [hboundary, eq_collarDerivative_of_tangent_radial s (T s) (D (boundaryToDisk s))
    (v s) (c s) (htangent s) (hradial s)]

include hc hA hD hAD hboundary htangent hradial in
theorem extends_twisted_sphereOperatorMap :
    Extends (twistedBlockMap (sphereOperatorMap a T ha hT hr)) :=
  (extends_homotopic_iff ⟨collarHomotopy a T v c ha hT hr hc⟩).mp
    (extends_collarMap a T v c ha hT hr hc A D hA hD hAD hboundary htangent hradial)

end NoExoticSixSphere.CollaredDiskFrame
