import Wikipedia.NoExoticSixSphere.InternalSphereTube
import Wikipedia.NoExoticSixSphere.SphereRadialProduct

/-!
# The original-manifold tube pulled back to a radial disk collar

The map takes values in the original manifold and keeps its original atlas.
Smoothness is proved away from the disk center on the actual tube domain.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector 3 →L[ℝ] Vector e.ambientDimension)
  (R : TubularRetraction e) (b : Sphere 3)

def radialInternalSphereTube (p : Vector 4 × Vector 3) : M :=
  e.internalSphereTube f C R (SphereRadialRetraction.retract b p.1, p.2)

theorem radialInternalSphereTube_core (x : Vector 4) :
    e.radialInternalSphereTube f C R b (x, 0) = f (SphereRadialRetraction.retract b x) :=
  e.internalSphereTube_core f C R _

theorem radialInternalSphereTube_coe (s : Sphere 3) (v : Vector 3) :
    e.radialInternalSphereTube f C R b (s.val, v) = e.internalSphereTube f C R (s, v) := by
  simp only [radialInternalSphereTube, SphereRadialRetraction.retract_coe]

theorem contMDiffAt_radialInternalSphereTube
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 3 →L[ℝ] Vector e.ambientDimension) ∞ C)
    {x : Vector 4} (hx : x ≠ 0) (v : Vector 3)
    (hp : (SphereRadialRetraction.retract b x, v) ∈ e.sphereTubeDomain f C R) :
    ContMDiffAt 𝓘(ℝ, Vector 4 × Vector 3) (𝓡 6) ∞
      (e.radialInternalSphereTube f C R b) (x, v) := by
  have hI := (e.contMDiffOn_internalSphereTube f C R hf hC).contMDiffAt
    ((e.isOpen_sphereTubeDomain f C R hf hC).mem_nhds hp)
  exact hI.comp (x, v) (SphereRadialProduct.contMDiffAt_radialProduct b hx v)

end NoExoticSixSphere.EuclideanEmbedding
