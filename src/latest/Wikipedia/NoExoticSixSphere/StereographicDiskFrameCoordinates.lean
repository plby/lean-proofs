import Wikipedia.NoExoticSixSphere.StereographicAugmentedDifferential
import Wikipedia.NoExoticSixSphere.NormalFrameVariableAmbientCoordinates
import Wikipedia.NoExoticSixSphere.SmoothSphereAmbientExtension

/-!
# Actual compactification frame coordinates extend over the whole spanning disk

Use the original smooth ambient extension of the sphere map. The global
augmented stereographic differential and its inverse can be evaluated on
that extension, giving the exact compactification coordinate change on
the boundary. This preserves the original twisted extension criterion.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.StereographicEquator

open GLOrthonormalization Stiefel DiskBoundary SpanningDiskFrameCoordinates
open Wikipedia.HopfProblem.DegreeCollapse

def diskAugmentedCoordinates (n : ℕ) (f : Sphere 3 → V n)
    (x : DiskCylinder.Disk (E := V 4)) : V (n + 1) ≃L[ℝ] V (n + 1) :=
  augmentedCoordinates n (SmoothSphereAmbient.extension (spherePole 3) f x.val)

theorem diskAugmentedCoordinates_boundary (n : ℕ) (f : Sphere 3 → V n) (s : Sphere 3) :
    diskAugmentedCoordinates n f (DiskCylinder.boundaryToDisk s) =
      augmentedCoordinates n (f s) := by
  change augmentedCoordinates n (SmoothSphereAmbient.extension (spherePole 3) f s.val) = _
  rw [SmoothSphereAmbient.extension_coe]

theorem continuous_diskAugmentedCoordinates (n : ℕ) (f : Sphere 3 → V n)
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, V n) ∞ f) :
    Continuous (fun x ↦ (diskAugmentedCoordinates n f x).toContinuousLinearMap) :=
  (continuous_augmentedCoordinates n).comp
    ((SmoothSphereAmbient.contDiff_extension (spherePole 3) f hf).continuous.comp
      continuous_subtype_val)

theorem continuous_diskAugmentedCoordinates_symm (n : ℕ) (f : Sphere 3 → V n)
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, V n) ∞ f) :
    Continuous (fun x ↦ (diskAugmentedCoordinates n f x).symm.toContinuousLinearMap) :=
  (continuous_augmentedCoordinates_symm n).comp
    ((SmoothSphereAmbient.contDiff_extension (spherePole 3) f hf).continuous.comp
      continuous_subtype_val)

theorem extends_twisted_augmented_iff (n k : ℕ) (f : Sphere 3 → V n)
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, V n) ∞ f)
    (F G : C(Sphere 3, Monomorphism.Space (n + 1) (k + 3)))
    (h : ∀ s, (G s).val = (augmentedCoordinates n (f s)).toContinuousLinearMap.comp (F s).val) :
    Extends (twistedBlockMap G) ↔ Extends (twistedBlockMap F) := by
  apply NormalFrameAmbientCoordinates.extends_twisted_diskTarget_iff
    (diskAugmentedCoordinates n f) (continuous_diskAugmentedCoordinates n f hf)
    (continuous_diskAugmentedCoordinates_symm n f hf) F G
  intro s
  rw [diskAugmentedCoordinates_boundary]
  exact h s

end NoExoticSixSphere.StereographicEquator
