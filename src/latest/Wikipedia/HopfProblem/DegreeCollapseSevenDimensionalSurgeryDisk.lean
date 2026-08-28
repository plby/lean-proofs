import Wikipedia.HopfProblem.DegreeCollapseEightDimensionalFramedProduct
import Wikipedia.NoExoticSixSphere.SpanningDiskCollaredNormalFrame

/-!
# Framed spanning products for three-spheres in dimension seven

The disk is constructed from the original embedded sphere. Its partial
normal frame extends without a parity premise because four complementary
directions remain. The actual disk and its core normal frame retain the
original radial collar, and a framed eight-dimensional thickening is
constructed. Agreement of the full attaching face with a seven-manifold
and the subsequent surgery trace are not asserted here.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

structure DiskProduct {N k : ℕ} (b : NoExoticSixSphere.Sphere 3)
    (f : NoExoticSixSphere.Sphere 3 → Vector N)
    (a : NoExoticSixSphere.Sphere 3 → Space N k) where
  disk : DiskData b f
  coreFrame : Vector 4 → Vector (k + 5) →L[ℝ] Vector (N + 6)
  product : EightDimensionalFramedProduct.FramedProduct disk.toFun coreFrame
  collarRadius : ℝ
  collarRadius_pos : 0 < collarRadius
  collarRadius_lt_one : collarRadius < 1
  boundary_frame : ∀ s : NoExoticSixSphere.Sphere 3,
    product.normalFrame (s.val, 0) = boundaryFrameOperator (a s).val
  collar_map : ∀ x ∈ closedBall (0 : Vector 4) 1, collarRadius ≤ ‖x‖ →
    disk.toFun x = collar b f x
  collar_frame : ∀ x ∈ closedBall (0 : Vector 4) 1, collarRadius ≤ ‖x‖ →
    product.normalFrame (x, 0) =
      boundaryFrameOperator (a (SphereRadialRetraction.retract b x)).val

theorem nonempty_diskProduct {N k : ℕ} (hN : k + 7 = N)
    (b : NoExoticSixSphere.Sphere 3) (f : NoExoticSixSphere.Sphere 3 → Vector N)
    (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (hi : Injective f)
    (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 N) f s))
    (a : NoExoticSixSphere.Sphere 3 → Space N k)
    (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))
    (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ) :
    Nonempty (DiskProduct b f a) := by
  obtain ⟨D⟩ := nonempty_diskData b f hf hi hd
  have hbd (s : NoExoticSixSphere.Sphere 3) :
      ((boundaryFrameMap a has) s).val.range ≤ (fderiv ℝ D.toFun s.val).rangeᗮ := by
    obtain ⟨V, hV, hSV, heq⟩ := D.collar_eq
    exact boundaryFrame_normal_disk b f hf a ha hV hSV heq s
  obtain ⟨T, hTs, hTn, hTr, hTb⟩ := FourDiskNormal.exists_smooth_extension
    (by omega : (k + 5) + 8 ≤ N + 6) D.toFun
    (fun _ _ ↦ D.smooth.contDiffAt) D.immersive (boundaryFrameMap a has)
    (contMDiff_boundaryFrameOperator has) hbd
  obtain ⟨r, hr, hr1, T', hT's, hT'n, hT'r, hT'b, hTc⟩ :=
    D.exists_normalFrame_collar hf a has ha T hTs hTn hTr hTb
  have hDi : InjOn D.toFun (closedBall (0 : Vector 4) 1) := by
    intro x hx y hy he
    exact congrArg Subtype.val (D.embedded.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) he)
  obtain ⟨A⟩ := EightDimensionalFramedProduct.nonempty_framedProduct D.toFun T'
    (fun _ _ ↦ D.smooth.contDiffAt) hDi D.immersive hT's hT'n hT'r (by omega)
  refine ⟨{
    disk := D
    coreFrame := T'
    product := A
    collarRadius := r
    collarRadius_pos := hr
    collarRadius_lt_one := hr1
    boundary_frame := ?_
    collar_map := fun x hx hxr ↦ (hTc x hx hxr).1
    collar_frame := ?_ }⟩
  · intro s
    exact (A.normalFrame_core s.val (sphere_subset_closedBall s.property)).trans (hT'b s)
  · intro x hx hxr
    exact (A.normalFrame_core x hx).trans (hTc x hx hxr).2

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
