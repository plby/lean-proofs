import Wikipedia.NoExoticSixSphere.CompactSphereTube
import Wikipedia.NoExoticSixSphere.SphereRadialProduct

/-!
# The original-manifold tube pulled back to a radial disk collar

The map takes values in the original manifold and keeps its original atlas.
Smoothness is proved away from the disk center on the actual tube domain.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization

variable {n d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector d →L[ℝ] Vector e.ambientDimension)
  (R : e.RetractionNear (range f)) (b : Sphere 3)

def radialCompactSphereTube (p : Vector 4 × Vector d) : M :=
  e.compactSphereTube f C R (SphereRadialRetraction.retract b p.1, p.2)

theorem radialCompactSphereTube_core (x : Vector 4) :
    e.radialCompactSphereTube f C R b (x, 0) = f (SphereRadialRetraction.retract b x) :=
  e.compactSphereTube_core f C R _

theorem radialCompactSphereTube_coe (s : Sphere 3) (v : Vector d) :
    e.radialCompactSphereTube f C R b (s.val, v) = e.compactSphereTube f C R (s, v) := by
  simp only [radialCompactSphereTube, SphereRadialRetraction.retract_coe]

theorem contMDiffAt_radialCompactSphereTube
    (hf : ContMDiff (𝓡 3) (𝓡 n) ∞ f)
    (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector d →L[ℝ] Vector e.ambientDimension) ∞ C)
    {x : Vector 4} (hx : x ≠ 0) (v : Vector d)
    (hp : (SphereRadialRetraction.retract b x, v) ∈ e.compactSphereTubeDomain f C R) :
    ContMDiffAt 𝓘(ℝ, Vector 4 × Vector d) (𝓡 n) ∞
      (e.radialCompactSphereTube f C R b) (x, v) := by
  have hI := (e.contMDiffOn_compactSphereTube f C R hf hC).contMDiffAt
    ((e.isOpen_compactSphereTubeDomain f C R hf hC).mem_nhds hp)
  exact hI.comp (x, v) (SphereRadialProduct.contMDiffAt_radialProduct b hx v)

end NoExoticSixSphere.EuclideanEmbedding
