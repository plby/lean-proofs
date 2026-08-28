import Wikipedia.NoExoticSixSphere.StabilizedDiskRadialNormal
import Wikipedia.NoExoticSixSphere.ComplementaryOperatorCoordinates

/-!
# The original internal normal space remains complementary on the disk collar

At every retained collar point, the stabilized old vectors perpendicular to
both the original normal frame and sphere derivative are perpendicular to the
combined radial frame and actual disk derivative. This is an exact derivative
and coordinate calculation, not a continuity inference from boundary values.
-/

noncomputable section

open Function Set Filter Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.StabilizedSpanningDisk

open GLOrthonormalization

theorem map_normal_le_combined_orthogonal_radial {N k : ℕ} (b : Sphere 3)
    (f : Sphere 3 → Vector N) (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f)
    {G : Vector 4 → Vector (N + 6)} {V : Set (Vector 4)} (hV : IsOpen V)
    (heq : EqOn G (collar b f) V) {x : Vector 4} (hxV : x ∈ V)
    (hx : (1 / 2 : ℝ) < ‖x‖) (a : Vector k →L[ℝ] Vector N) :
    (a.rangeᗮ ⊓
        (mfderiv (𝓡 3) (𝓡 N) f (SphereRadialRetraction.retract b x)).rangeᗮ).map
        (appendZeroMap N 6).toLinearMap ≤
      (OperatorSum.operator (boundaryFrameOperator a) (fderiv ℝ G x)).rangeᗮ := by
  have he : G =ᶠ[𝓝 x] collar b f := Filter.mem_of_superset (hV.mem_nhds hxV) heq
  rw [OperatorSum.range_operator, ← Submodule.inf_orthogonal]
  rintro _ ⟨w, hw, rfl⟩
  have hwc : appendZeroMap N 6 w = coordinates N 4 ((w, 0), 0) :=
    (coordinates_old N 4 w).symm
  constructor
  · apply (Submodule.mem_orthogonal _ _).mpr
    rintro _ ⟨v, rfl⟩
    change inner ℝ (boundaryFrameOperator a v) (appendZeroMap N 6 w) = 0
    rw [boundaryFrameOperator_apply, hwc, inner_coordinates]
    simp only [Prod.fst_zero, Prod.snd_zero, inner_zero_right, add_zero]
    exact (Submodule.mem_orthogonal a.range w).mp hw.1 _ ⟨_, rfl⟩
  · apply (Submodule.mem_orthogonal _ _).mpr
    rintro _ ⟨v, rfl⟩
    change inner ℝ (fderiv ℝ G x v) (appendZeroMap N 6 w) = 0
    rw [he.fderiv_eq, fderiv_collar_apply_at b f hf, hwc, inner_coordinates]
    simp only [Prod.fst_zero, Prod.snd_zero, inner_zero_right, add_zero]
    exact Submodule.inner_right_of_mem_orthogonal
      ((SmoothSphereAmbient.range_fderiv_extension_le_radial b f hf hx) ⟨v, rfl⟩) hw.2

end NoExoticSixSphere.StabilizedSpanningDisk
