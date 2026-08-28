import Wikipedia.NoExoticSixSphere.RegularCylinderDiskCollar
import Wikipedia.NoExoticSixSphere.CollaredDiskOperatorStabilization
import Wikipedia.NoExoticSixSphere.ManifoldFourDiskRawFrame

/-!
# The original disk extension in the prescribed endpoint frame

Transport the actual raw normal-plus-derivative extension by the ordered
normal coordinates and the height-last target coordinates. Append the five
fixed graph axes. The resulting boundary operator is exactly the one for
the prescribed endpoint frame and the derivative of the original disk.
Only the original disk's boundary is required to lie in the constant collar.
-/

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularSlabDiskCollar

open GLOrthonormalization Stiefel RegularCylinderFiber CollaredDiskFrame
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {m n : ℕ} {z : NoExoticSixSphere.Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := NoExoticSixSphere.Sphere m) (𝓡 m) (𝓡 n) z s t}

theorem exists_endpoint_boundary_frame_extension (hd : m = n + 6)
    (f₀ : C(NoExoticSixSphere.Sphere m, NoExoticSixSphere.Sphere n))
    (hf₀ : ContMDiff (𝓡 m) (𝓡 n) ∞ f₀)
    (hreg₀ : ∀ x, f₀ x = z → Surjective (mfderiv (𝓡 m) (𝓡 n) f₀ x))
    (U : Set ℝ) (hU : IsOpen U)
    (hconstant : ∀ c ∈ U, ∀ x, d.map (c, x) = f₀ x)
    (c : ℝ) (hc : c ∈ U) (a : NoExoticSixSphere.Sphere m)
    (f : NoExoticSixSphere.Sphere 3 → {x : NoExoticSixSphere.Sphere m // f₀ x = z}) :
    letI := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
      (CylinderFiberNormalFrame.dimension_eq hd)
    letI := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (by simpa using hd)
    let e := embedding d.map d.smooth_map z d.regular_map 6 hd
    let aN := normalFrame d.map d.smooth_map z d.regular_map 6 hd a
    let e₀ := RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd
    let a₀ := RegularSphereFiber.frame f₀ hf₀ z hreg₀ 6 hd a
    ∀ (g : Vector 4 → {v : ℝ × NoExoticSixSphere.Sphere m // d.map v = z}),
      (∀ q : NoExoticSixSphere.Sphere 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g q.val) →
      (∀ q, g q.val = ⟨(c, (f q).val), (hconstant c hc (f q).val).trans (f q).property⟩) →
      ∀ G : C(Disk (E := Vector 4),
        Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)),
      (∀ q, (G (boundaryToDisk q)).val = e.rawNormalFourDiskOperator aN g q.val) →
      ∃ H : C(Disk (E := Vector 4),
          Monomorphism.Space (e₀.ambientDimension + 6) (((e₀.ambientDimension - 6) + 5) + 4)),
        ∀ q, (H (boundaryToDisk q)).val =
          combined ((ContinuousLinearMap.inl ℝ (Vector e₀.ambientDimension) ℝ).comp
            (a₀.ambient (f q))) (fderiv ℝ (collarDisk c g) q.val) := by
  let := regularFiberAtlas d.map d.smooth_map z d.regular_map 7
    (CylinderFiberNormalFrame.dimension_eq hd)
  let := regularFiberAtlas f₀ hf₀ z hreg₀ 6 (by simpa using hd)
  let e := embedding d.map d.smooth_map z d.regular_map 6 hd
  let aN := normalFrame d.map d.smooth_map z d.regular_map 6 hd a
  let e₀ := RegularSphereFiber.embedding f₀ hf₀ z hreg₀ 6 hd
  let a₀ := RegularSphereFiber.frame f₀ hf₀ z hreg₀ 6 hd a
  dsimp only
  intro g hgs hgb G hG
  obtain ⟨H, hH⟩ := exists_combined_extension_normal_coordinates (collarTargetCoordinates m)
    (collarNormalCoordinates 6 hd) G (fun q ↦ aN.ambient (g q.val))
      (fun q ↦ e.fourDiskDerivative g q.val) hG
  refine ⟨H, ?_⟩
  intro q
  have ha : (collarTargetCoordinates m).toContinuousLinearMap.comp
      ((aN.ambient (g q.val)).comp (collarNormalCoordinates 6 hd).toContinuousLinearMap) =
      (ContinuousLinearMap.inl ℝ (Vector e₀.ambientDimension) ℝ).comp (a₀.ambient (f q)) := by
    rw [hgb]
    exact normalFrame_collar_coordinates 6 hd d.map f₀ z a hconstant d.smooth_map hf₀
      d.regular_map hreg₀ hU c hc (f q)
  have hD : (collarTargetCoordinates m).toContinuousLinearMap.comp
      (e.fourDiskDerivative g q.val) = fderiv ℝ (collarDisk c g) q.val :=
    (fderiv_collarDisk hd c g q.val (hgs q)).symm
  exact (hH q).trans (congrArg₂ combined ha hD)

end NoExoticSixSphere.RegularSlabDiskCollar
