import Wikipedia.HopfProblem.DegreeCollapseLowAttachingTubeCoordinates
import Wikipedia.HopfProblem.DegreeCollapseLowRadialHeightCoordinates
import Wikipedia.NoExoticSixSphere.PartialDiffeomorphProduct
import Wikipedia.HopfProblem.DegreeCollapseLowHeightCylinder

/-!

# Genuine low-dimensional collar coordinates across the original attaching rim

The map uses the original native tube, the actual sphere retraction and signed
height. Its smooth inverse uses sqrt(1+t) and the actual tube inverse. On the
retained closed collar, both the handle map and its full normal frame are
exactly the original cylinder data in these same coordinates.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

def collarRadialChart (d : ℕ) :
    PartialDiffeomorph (((𝓡 d).prod 𝓘(ℝ, ℝ)).prod (𝓡 (7 - d))) ((𝓡 (d + 1)).prod (𝓡 (7 - d)))
      ((NoExoticSixSphere.Sphere d × ℝ) × Vector (7 - d)) (Vector (d + 1) × Vector (7 - d)) ∞ :=
  partialDiffeomorphProd (LowRadialHeightCoordinates.chart (spherePole d))
    (Diffeomorph.refl (𝓡 (7 - d)) (Vector (7 - d)) ∞).toPartialDiffeomorph

def collarReorder (d : ℕ) : ((NoExoticSixSphere.Sphere d × ℝ) × Vector (7 - d)) ≃ₘ⟮
    ((𝓡 d).prod 𝓘(ℝ, ℝ)).prod (𝓡 (7 - d)), ((𝓡 d).prod (𝓡 (7 - d))).prod 𝓘(ℝ, ℝ)⟯
      ((NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun :=
    ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst)
  contMDiff_invFun :=
    ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
      (contMDiff_snd.comp contMDiff_fst)

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def tubeHeightCoordinates :
    PartialDiffeomorph (((𝓡 d).prod (𝓡 (7 - d))).prod 𝓘(ℝ, ℝ)) ((𝓡 7).prod 𝓘(ℝ, ℝ))
      ((NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ) (M × ℝ) ∞ :=
  partialDiffeomorphProd A.tubeCoordinates
    (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph

def collarCoordinates : PartialDiffeomorph ((𝓡 (d + 1)).prod (𝓡 (7 - d))) ((𝓡 7).prod 𝓘(ℝ, ℝ))
    (Vector (d + 1) × Vector (7 - d)) (M × ℝ) ∞ :=
  (collarRadialChart d).symm.trans
    ((collarReorder d).toPartialDiffeomorph.trans A.tubeHeightCoordinates)

theorem mem_tubeHeightCoordinates_source (p : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ) :
    p ∈ A.tubeHeightCoordinates.source ↔ p.1.2 ∈ ball (0 : Vector (7 - d)) A.radius := by
  change (p.1 ∈ A.tubeCoordinates.source ∧ True) ↔ _
  rw [A.tubeCoordinates_source]
  simp only [openTubeDomain, mem_prod, mem_univ, true_and, and_true]

theorem collarCoordinates_apply (p : Vector (d + 1) × Vector (7 - d)) :
    A.collarCoordinates p =
      (A.tube (SphereRadialRetraction.retract (spherePole d) p.1, p.2), definingFunction p.1) := rfl

theorem collarCoordinates_symm_apply (p : M × ℝ) :
    A.collarCoordinates.symm p =
      (LowRadialHeightCoordinates.point ((A.tubeCoordinates.symm p.1).1, p.2),
        (A.tubeCoordinates.symm p.1).2) := rfl

theorem collarCoordinates_source :
    A.collarCoordinates.source = {p | p.1 ≠ 0 ∧ p.2 ∈ ball (0 : Vector (7 - d)) A.radius} := by
  ext p
  change (p.1 ≠ 0 ∧ True) ∧ (True ∧
    ((SphereRadialRetraction.retract (spherePole d) p.1, p.2) ∈
      A.tubeCoordinates.source ∧ True)) ↔ _
  rw [A.tubeCoordinates_source]
  simp only [openTubeDomain, mem_prod, mem_univ, true_and, and_true, mem_ofPred_eq]

theorem collarCoordinates_target :
    A.collarCoordinates.target = A.tubeCoordinates.target ×ˢ Ioi (-1 : ℝ) := by
  ext p
  change ((p.1 ∈ A.tubeCoordinates.target ∧ True) ∧ True) ∧ (-1 < p.2 ∧ True) ↔ _
  simp only [mem_prod, mem_Ioi, and_true]

theorem map_eq_cylinder_collarCoordinates {x : Vector (d + 1)}
    (hx : x ∈ closedBall 0 1) (hxr : A.innerRadius ≤ ‖x‖)
    {v : Vector (7 - d)} (hv : v ∈ closedBall 0 A.radius) :
    A.map (x, v) = (LowHeightCylinder.heightCylinder d e) (A.collarCoordinates (x, v)) :=
  A.collar_map x hx hxr v hv

theorem frame_eq_cylinder_collarCoordinates {x : Vector (d + 1)}
    (hx : x ∈ closedBall 0 1) (hxr : A.innerRadius ≤ ‖x‖)
    {v : Vector (7 - d)} (hv : v ∈ closedBall 0 A.radius) :
    A.normalFrame (x, v) = boundaryFrameOperator d
      (a.orthonormal (A.collarCoordinates (x, v)).1).val :=
  A.collar_frame x hx hxr v hv

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct
