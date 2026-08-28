import Wikipedia.NoExoticSixSphere.CollaredSlabEndpoints
import Wikipedia.NoExoticSixSphere.CollaredSlabBoundary

/-!
# Smooth endpoint inclusions in the global slab

The endpoint fibers keep their previously constructed regular-fiber atlases.
Their inclusions factor through the corresponding open collar pieces of the
global slab. Projection back to the spatial manifold proves that the endpoint
differentials are injective.
-/

open scoped Manifold ContDiff
open Module

namespace NoExoticSixSphere.RegularCollaredCylinder

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {b : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J b s t)
  (k : ℕ) (hd : finrank ℝ B = finrank ℝ C + k)
  (Φ : PartialDiffeomorph (𝓡 (k + 1)) ((𝓡∂ 1).prod (𝓡 k))
    (EuclideanSpace ℝ (Fin (k + 1)))
    (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin k))) ∞)
  (hsource : Φ.source = Set.univ)

theorem contMDiff_leftEndpoint_inclusion :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k hd;
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    ContMDiff (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) ∞
      (fun x : {x : M // d.leftMap x = b} ↦ (d.leftEndpoint x).val) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k hd
  let A := d.openCover k hd Φ hsource
  let := A.chartedSpace
  let := d.pieceAtlas k hd Φ hsource .left
  let q : {x : M // d.leftMap x = b} → d.pieceDomain .left :=
    fun x ↦ ⟨(d.leftEndpoint x).val, d.left_mem⟩
  have hq : ContMDiff (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) ∞ q := by
    apply (d.piece_contMDiff_iff_ambient k hd Φ hsource .left q).mpr
    exact contMDiff_const.prodMk
      (regularFiber_contMDiff_subtype_val d.leftMap d.smooth_left b d.regular_left k hd)
  exact (A.contMDiff_inclusion .left).comp hq

theorem contMDiff_rightEndpoint_inclusion :
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k hd;
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    ContMDiff (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) ∞
      (fun x : {x : M // d.rightMap x = b} ↦ (d.rightEndpoint x).val) := by
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k hd
  let A := d.openCover k hd Φ hsource
  let := A.chartedSpace
  let := d.pieceAtlas k hd Φ hsource .right
  let q : {x : M // d.rightMap x = b} → d.pieceDomain .right :=
    fun x ↦ ⟨(d.rightEndpoint x).val, d.right_mem⟩
  have hq : ContMDiff (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) ∞ q := by
    apply (d.piece_contMDiff_iff_ambient k hd Φ hsource .right q).mpr
    exact contMDiff_const.prodMk
      (regularFiber_contMDiff_subtype_val d.rightMap d.smooth_right b d.regular_right k hd)
  exact (A.contMDiff_inclusion .right).comp hq

theorem injective_mfderiv_leftEndpoint_inclusion (x : {x : M // d.leftMap x = b}) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k hd;
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    Function.Injective (mfderiv (𝓡 k) ((𝓡∂ 1).prod (𝓡 k))
      (fun y : {x : M // d.leftMap x = b} ↦ (d.leftEndpoint y).val) x) := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k hd
  let A := d.openCover k hd Φ hsource
  let := A.chartedSpace
  let := A.isManifold
  let e := fun y : {x : M // d.leftMap x = b} ↦ (d.leftEndpoint y).val
  let p := fun y : CylinderFiberSlab.slab d.map b s t ↦ y.val.val.2
  have he : ContMDiff (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) ∞ e :=
    d.contMDiff_leftEndpoint_inclusion k hd Φ hsource
  have hp : ContMDiff ((𝓡∂ 1).prod (𝓡 k)) I ∞ p :=
    contMDiff_snd.comp (d.slab_contMDiff_ambient k hd Φ hsource)
  have hcomp := mfderiv_comp x (hp.mdifferentiable (by simp) (e x))
    (he.mdifferentiable (by simp) x)
  have hinj : Function.Injective (mfderiv (𝓡 k) I (p ∘ e) x) :=
    regularFiber_injective_mfderiv_subtype_val d.leftMap d.smooth_left b d.regular_left k hd x
  rw [hcomp] at hinj
  exact Function.Injective.of_comp hinj

theorem injective_mfderiv_rightEndpoint_inclusion (x : {x : M // d.rightMap x = b}) :
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k hd;
    letI := (d.openCover k hd Φ hsource).chartedSpace;
    Function.Injective (mfderiv (𝓡 k) ((𝓡∂ 1).prod (𝓡 k))
      (fun y : {x : M // d.rightMap x = b} ↦ (d.rightEndpoint y).val) x) := by
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right k hd
  let A := d.openCover k hd Φ hsource
  let := A.chartedSpace
  let := A.isManifold
  let e := fun y : {x : M // d.rightMap x = b} ↦ (d.rightEndpoint y).val
  let p := fun y : CylinderFiberSlab.slab d.map b s t ↦ y.val.val.2
  have he : ContMDiff (𝓡 k) ((𝓡∂ 1).prod (𝓡 k)) ∞ e :=
    d.contMDiff_rightEndpoint_inclusion k hd Φ hsource
  have hp : ContMDiff ((𝓡∂ 1).prod (𝓡 k)) I ∞ p :=
    contMDiff_snd.comp (d.slab_contMDiff_ambient k hd Φ hsource)
  have hcomp := mfderiv_comp x (hp.mdifferentiable (by simp) (e x))
    (he.mdifferentiable (by simp) x)
  have hinj : Function.Injective (mfderiv (𝓡 k) I (p ∘ e) x) :=
    regularFiber_injective_mfderiv_subtype_val d.rightMap d.smooth_right b d.regular_right k hd x
  rw [hcomp] at hinj
  exact Function.Injective.of_comp hinj

end NoExoticSixSphere.RegularCollaredCylinder
