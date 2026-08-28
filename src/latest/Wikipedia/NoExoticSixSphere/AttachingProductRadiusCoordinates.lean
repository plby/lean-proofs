import Wikipedia.NoExoticSixSphere.FramedAttachingProduct
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Linear transverse coordinates normalizing the attaching radius

Scale the transverse three-space so that its radius-two ball maps to the
original available closed ball. This changes only product parameters, not
the ambient points, original manifold atlas, or normal-frame values.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct

open GLOrthonormalization Stiefel

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def radiusScale : ℝ := A.radius / 2

theorem radiusScale_pos : 0 < A.radiusScale := half_pos A.radius_pos

def transverseRadiusCoordinates : Vector 3 ≃L[ℝ] Vector 3 :=
  (LinearEquiv.smulOfNeZero ℝ (Vector 3) A.radiusScale
    A.radiusScale_pos.ne').toContinuousLinearEquiv

theorem transverseRadiusCoordinates_apply (v : Vector 3) :
    A.transverseRadiusCoordinates v = A.radiusScale • v := rfl

theorem transverseRadiusCoordinates_mem {v : Vector 3}
    (hv : v ∈ closedBall (0 : Vector 3) 2) :
    A.transverseRadiusCoordinates v ∈ closedBall (0 : Vector 3) A.radius := by
  have hn : ‖v‖ ≤ 2 := by simpa only [mem_closedBall, dist_zero_right] using hv
  rw [transverseRadiusCoordinates_apply, mem_closedBall, dist_zero_right, norm_smul,
    Real.norm_eq_abs, abs_of_pos A.radiusScale_pos]
  dsimp only [radiusScale]
  nlinarith [A.radius_pos]

def radiusBallMap : C(closedBall (0 : Vector 3) 2, closedBall (0 : Vector 3) A.radius) :=
  ⟨fun p ↦ ⟨A.transverseRadiusCoordinates p.val, A.transverseRadiusCoordinates_mem p.property⟩,
    (A.transverseRadiusCoordinates.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem isClosedEmbedding_radiusBallMap : IsClosedEmbedding A.radiusBallMap := by
  apply A.radiusBallMap.continuous.isClosedEmbedding
  intro p q he
  exact Subtype.ext (A.transverseRadiusCoordinates.injective (congrArg Subtype.val he))

def productRadiusCoordinates : (Vector 4 × Vector 3) ≃L[ℝ] (Vector 4 × Vector 3) :=
  (ContinuousLinearEquiv.refl ℝ (Vector 4)).prodCongr A.transverseRadiusCoordinates

theorem productRadiusCoordinates_apply (p : Vector 4 × Vector 3) :
    A.productRadiusCoordinates p = (p.1, A.transverseRadiusCoordinates p.2) := rfl

def tubeRadiusCoordinates : (Sphere 3 × Vector 3) ≃ₘ⟮(𝓡 3).prod (𝓡 3),
    (𝓡 3).prod (𝓡 3)⟯ (Sphere 3 × Vector 3) :=
  (Diffeomorph.refl (𝓡 3) (Sphere 3) ∞).prodCongr A.transverseRadiusCoordinates.toDiffeomorph

theorem tubeRadiusCoordinates_apply (p : Sphere 3 × Vector 3) :
    A.tubeRadiusCoordinates p = (p.1, A.transverseRadiusCoordinates p.2) := rfl

theorem isClosedEmbedding_radiusProduct : IsClosedEmbedding
    (fun p : closedBall (0 : Vector 4) 1 × closedBall (0 : Vector 3) 2 ↦
      A.map (p.1.val, A.transverseRadiusCoordinates p.2.val)) :=
  A.embedded.comp (IsClosedEmbedding.id.prodMap A.isClosedEmbedding_radiusBallMap)

theorem isClosedEmbedding_radiusTube : IsClosedEmbedding
    (fun p : Sphere 3 × closedBall (0 : Vector 3) 2 ↦
      A.tube (p.1, A.transverseRadiusCoordinates p.2.val)) :=
  A.tube_embedded.comp (IsClosedEmbedding.id.prodMap A.isClosedEmbedding_radiusBallMap)

theorem fderiv_radiusProduct {x : Vector 4} (hx : x ∈ closedBall (0 : Vector 4) 1)
    {v : Vector 3} (hv : v ∈ closedBall (0 : Vector 3) 2) :
    fderiv ℝ (A.map ∘ A.productRadiusCoordinates) (x, v) =
      (fderiv ℝ A.map (x, A.transverseRadiusCoordinates v)).comp
        A.productRadiusCoordinates.toContinuousLinearMap :=
  (((A.smooth x hx _ (A.transverseRadiusCoordinates_mem hv)).differentiableAt
    (by simp)).hasFDerivAt.comp (x, v) A.productRadiusCoordinates.hasFDerivAt).fderiv

theorem injective_fderiv_radiusProduct {x : Vector 4} (hx : x ∈ closedBall (0 : Vector 4) 1)
    {v : Vector 3} (hv : v ∈ closedBall (0 : Vector 3) 2) :
    Injective (fderiv ℝ (A.map ∘ A.productRadiusCoordinates) (x, v)) := by
  rw [A.fderiv_radiusProduct hx hv]
  exact (A.immersive x hx _ (A.transverseRadiusCoordinates_mem hv)).comp
    A.productRadiusCoordinates.injective

theorem range_fderiv_radiusProduct {x : Vector 4} (hx : x ∈ closedBall (0 : Vector 4) 1)
    {v : Vector 3} (hv : v ∈ closedBall (0 : Vector 3) 2) :
    (fderiv ℝ (A.map ∘ A.productRadiusCoordinates) (x, v)).range =
      (fderiv ℝ A.map (x, A.transverseRadiusCoordinates v)).range := by
  rw [A.fderiv_radiusProduct hx hv]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr A.productRadiusCoordinates.surjective)

end NoExoticSixSphere.EuclideanEmbedding.FramedAttachingProduct
