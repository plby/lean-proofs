import Wikipedia.HopfProblem.DegreeCollapseSevenAttachingTubeCoordinates
import Wikipedia.NoExoticSixSphere.RadialHeightCoordinates
import Wikipedia.NoExoticSixSphere.PartialDiffeomorphProduct
import Wikipedia.HopfProblem.DegreeCollapseGeneralHeightCylinder

/-!
# Actual smooth coordinates across the attaching collar

The map sends `(x,v)` to the original tube point at `(x/‖x‖,v)` and the
signed height `‖x‖² - 1`. Its smooth inverse uses `sqrt (1+t)` and the
constructed inverse of the original attaching tube. On the retained collar,
both the handle map and its normal frame are exactly the cylinder data in
these coordinates.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

def collarRadialChart :
    PartialDiffeomorph (((𝓡 3).prod 𝓘(ℝ, ℝ)).prod (𝓡 4)) ((𝓡 4).prod (𝓡 4))
      ((Sphere 3 × ℝ) × Vector 4) (Vector 4 × Vector 4) ∞ :=
  partialDiffeomorphProd (RadialHeightCoordinates.chart (pole 3))
    (Diffeomorph.refl (𝓡 4) (Vector 4) ∞).toPartialDiffeomorph

def collarReorder : ((Sphere 3 × ℝ) × Vector 4) ≃ₘ⟮
    ((𝓡 3).prod 𝓘(ℝ, ℝ)).prod (𝓡 4), ((𝓡 3).prod (𝓡 4)).prod 𝓘(ℝ, ℝ)⟯
      ((Sphere 3 × Vector 4) × ℝ) where
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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

def tubeHeightCoordinates :
    PartialDiffeomorph (((𝓡 3).prod (𝓡 4)).prod 𝓘(ℝ, ℝ)) ((𝓡 7).prod 𝓘(ℝ, ℝ))
      ((Sphere 3 × Vector 4) × ℝ) (M × ℝ) ∞ :=
  partialDiffeomorphProd A.tubeCoordinates
    (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).toPartialDiffeomorph

def collarCoordinates : PartialDiffeomorph ((𝓡 4).prod (𝓡 4)) ((𝓡 7).prod 𝓘(ℝ, ℝ))
    (Vector 4 × Vector 4) (M × ℝ) ∞ :=
  collarRadialChart.symm.trans (collarReorder.toPartialDiffeomorph.trans A.tubeHeightCoordinates)

theorem mem_tubeHeightCoordinates_source (p : (Sphere 3 × Vector 4) × ℝ) :
    p ∈ A.tubeHeightCoordinates.source ↔ p.1.2 ∈ ball (0 : Vector 4) A.radius := by
  change (p.1 ∈ A.tubeCoordinates.source ∧ True) ↔ _
  rw [A.tubeCoordinates_source]
  simp only [openTubeDomain, mem_prod, mem_univ, true_and, and_true]

theorem collarCoordinates_apply (p : Vector 4 × Vector 4) :
    A.collarCoordinates p =
      (A.tube (SphereRadialRetraction.retract (pole 3) p.1, p.2), definingFunction p.1) := rfl

theorem collarCoordinates_symm_apply (p : M × ℝ) :
    A.collarCoordinates.symm p =
      (RadialHeightCoordinates.point ((A.tubeCoordinates.symm p.1).1, p.2),
        (A.tubeCoordinates.symm p.1).2) := rfl

theorem collarCoordinates_source :
    A.collarCoordinates.source = {p | p.1 ≠ 0 ∧ p.2 ∈ ball (0 : Vector 4) A.radius} := by
  ext p
  change (p.1 ≠ 0 ∧ True) ∧ (True ∧
    ((SphereRadialRetraction.retract (pole 3) p.1, p.2) ∈ A.tubeCoordinates.source ∧ True)) ↔ _
  rw [A.tubeCoordinates_source]
  simp only [openTubeDomain, mem_prod, mem_univ, true_and, and_true, mem_ofPred_eq]

theorem collarCoordinates_target :
    A.collarCoordinates.target = A.tubeCoordinates.target ×ˢ Ioi (-1 : ℝ) := by
  ext p
  change ((p.1 ∈ A.tubeCoordinates.target ∧ True) ∧ True) ∧ (-1 < p.2 ∧ True) ↔ _
  simp only [mem_prod, mem_Ioi, and_true]

theorem map_eq_cylinder_collarCoordinates {x : Vector 4}
    (hx : x ∈ closedBall 0 1) (hxr : A.innerRadius ≤ ‖x‖)
    {v : Vector 4} (hv : v ∈ closedBall 0 A.radius) :
    A.map (x, v) = (HeightCylinder.heightCylinder e) (A.collarCoordinates (x, v)) :=
  A.collar_map x hx hxr v hv

theorem frame_eq_cylinder_collarCoordinates {x : Vector 4}
    (hx : x ∈ closedBall 0 1) (hxr : A.innerRadius ≤ ‖x‖)
    {v : Vector 4} (hv : v ∈ closedBall 0 A.radius) :
    A.normalFrame (x, v) = boundaryFrameOperator
      (a.orthonormal (A.collarCoordinates (x, v)).1).val :=
  A.collar_frame x hx hxr v hv

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct
