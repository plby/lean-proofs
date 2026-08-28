import Wikipedia.NoExoticSixSphere.NormalHomotopyObstruction
import Wikipedia.NoExoticSixSphere.ImmersedDiskNormalObstruction
import Wikipedia.NoExoticSixSphere.SpatialDerivativeFamily

/-!
# Actual smooth immersed-disk homotopies preserve normal-frame parity

Joint smoothness supplies continuity of the actual spatial derivative.
Injectivity throughout the closed parameter–disk cylinder supplies its
normal ranks. The boundary frame may vary continuously while remaining
normal, and its endpoint parities are equal.
-/

noncomputable section

open scoped ContDiff

namespace NoExoticSixSphere.DiskHomotopy

open GLOrthonormalization Stiefel ProjectionHomotopy
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable (r : ℕ) (f : ℝ → Vector 4 → Vector (r + 9))
  (hf : ContDiff ℝ ∞ (Function.uncurry f))

def differential : C(ProjectionCylinder.Base, Vector 4 →L[ℝ] Vector (r + 9)) :=
  ⟨fun q ↦ fderiv ℝ (f (q.1 : ℝ)) q.2.val,
    (continuous_spatial_fderiv f hf).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))⟩

include hf in
theorem contDiff_slice (t : ℝ) : ContDiff ℝ ∞ (f t) :=
  hf.comp (contDiff_const.prodMk contDiff_id)

variable (hi : ∀ t : unitInterval, ∀ x ∈ Metric.closedBall (0 : Vector 4) 1,
    Function.Injective (fderiv ℝ (f (t : ℝ)) x))

include hi in
theorem differential_injective (q : ProjectionCylinder.Base) :
    Function.Injective (differential r f hf q) := hi q.1 q.2.val q.2.property

variable (a : C(unitInterval × NoExoticSixSphere.Sphere 3, Space (r + 9) (r + 2)))
  (ha : ∀ q, (a q).val.range ≤ (fderiv ℝ (f (q.1 : ℝ)) q.2.val).rangeᗮ)

theorem parity_endpoints :
    ImmersedDisk.parity r (f 0) (fun _ _ ↦ (contDiff_slice r f hf 0).contDiffAt) (hi 0)
        (slice a 0) (fun s ↦ ha (0, s)) =
      ImmersedDisk.parity r (f 1) (fun _ _ ↦ (contDiff_slice r f hf 1).contDiffAt) (hi 1)
        (slice a 1) (fun s ↦ ha (1, s)) :=
  NormalHomotopy.parity_endpoints r (differential r f hf) (differential_injective r f hf hi)
    a ha

end NoExoticSixSphere.DiskHomotopy
