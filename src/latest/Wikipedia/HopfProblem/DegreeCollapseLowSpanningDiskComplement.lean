import Wikipedia.HopfProblem.DegreeCollapseLowFramedSpanningDisk
import Wikipedia.HopfProblem.DegreeCollapseLowRadialNormalFrame
import Wikipedia.NoExoticSixSphere.ComplementaryOperatorCoordinates

/-!

# Actual low-surgery complementary planes along the retained radial collar

The original vectors perpendicular to both the original normal columns and
the sphere derivative remain perpendicular after stabilization. The proof
uses exact coordinate inner products and the actual radial disk derivative
at each collar point. No normality is inferred merely from continuity.
-/

noncomputable section

open Function Set Filter Metric
open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

theorem map_normal_le_combined_orthogonal_radial {d N k : ℕ} (b : NoExoticSixSphere.Sphere d)
    (f : NoExoticSixSphere.Sphere d → Vector N) (hf : ContMDiff (𝓡 d) (𝓡 N) ∞ f)
    {G : Vector (d + 1) → Vector (N + (1 + (1 + (d + 1))))}
    {V : Set (Vector (d + 1))} (hV : IsOpen V)
    (heq : EqOn G (collar b f) V) {x : Vector (d + 1)} (hxV : x ∈ V)
    (hx : (1 / 2 : ℝ) < ‖x‖) (a : Vector k →L[ℝ] Vector N) :
    (a.rangeᗮ ⊓
        (mfderiv (𝓡 d) (𝓡 N) f (SphereRadialRetraction.retract b x)).rangeᗮ).map
        (appendZeroMap N (1 + (1 + (d + 1)))).toLinearMap ≤
      (OperatorSum.operator (boundaryFrameOperator d a) (fderiv ℝ G x)).rangeᗮ := by
  have he : G =ᶠ[𝓝 x] collar b f := Filter.mem_of_superset (hV.mem_nhds hxV) heq
  rw [OperatorSum.range_operator, ← Submodule.inf_orthogonal]
  rintro _ ⟨w, hw, rfl⟩
  have hwc : appendZeroMap N (1 + (1 + (d + 1))) w = coordinates N (d + 1) ((w, 0), 0) :=
    (coordinates_old N (d + 1) w).symm
  constructor
  · apply (Submodule.mem_orthogonal _ _).mpr
    rintro _ ⟨v, rfl⟩
    change inner ℝ (boundaryFrameOperator d a v) (appendZeroMap N (1 + (1 + (d + 1))) w) = 0
    rw [boundaryFrameOperator_apply, hwc, inner_coordinates]
    simp only [Prod.fst_zero, Prod.snd_zero, inner_zero_right, add_zero]
    exact (Submodule.mem_orthogonal a.range w).mp hw.1 _ ⟨_, rfl⟩
  · apply (Submodule.mem_orthogonal _ _).mpr
    rintro _ ⟨v, rfl⟩
    change inner ℝ (fderiv ℝ G x v) (appendZeroMap N (1 + (1 + (d + 1))) w) = 0
    rw [he.fderiv_eq, fderiv_collar_apply_at b f hf, hwc, inner_coordinates]
    simp only [Prod.fst_zero, Prod.snd_zero, inner_zero_right, add_zero]
    exact Submodule.inner_right_of_mem_orthogonal
      ((SmoothSphereAmbient.range_fderiv_extension_le_radial b f hf hx) ⟨v, rfl⟩) hw.2

namespace FramedDisk

theorem map_normal_le_combined_orthogonal {d N k r : ℕ}
    {b : NoExoticSixSphere.Sphere d} {f : NoExoticSixSphere.Sphere d → Vector N}
    {a : NoExoticSixSphere.Sphere d → Space N k} (D : FramedDisk b f a)
    (hf : ContMDiff (𝓡 d) (𝓡 N) ∞ f) (s : NoExoticSixSphere.Sphere d)
    (c : Vector r →L[ℝ] Vector N) :
    (c.rangeᗮ ⊓ (mfderiv (𝓡 d) (𝓡 N) f s).rangeᗮ).map
        (appendZeroMap N (1 + (1 + (d + 1)))).toLinearMap ≤
      (OperatorSum.operator (boundaryFrameOperator d c) (fderiv ℝ D.map s.val)).rangeᗮ := by
  have he : D.map =ᶠ[𝓝 s.val] collar b f :=
    Filter.mem_of_superset
      (D.collar_open.mem_nhds (D.boundary_in_collar s.property)) D.collar_eq
  rw [OperatorSum.range_operator, ← Submodule.inf_orthogonal]
  rintro _ ⟨w, hw, rfl⟩
  have hwc : appendZeroMap N (1 + (1 + (d + 1))) w =
      coordinates N (d + 1) ((w, 0), 0) := (coordinates_old N (d + 1) w).symm
  constructor
  · apply (Submodule.mem_orthogonal _ _).mpr
    rintro _ ⟨v, rfl⟩
    change inner ℝ (boundaryFrameOperator d c v)
      (appendZeroMap N (1 + (1 + (d + 1))) w) = 0
    rw [boundaryFrameOperator_apply, hwc, inner_coordinates]
    simp only [Prod.fst_zero, Prod.snd_zero, inner_zero_right, add_zero]
    exact (Submodule.mem_orthogonal c.range w).mp hw.1 _ ⟨_, rfl⟩
  · apply (Submodule.mem_orthogonal _ _).mpr
    rintro _ ⟨v, rfl⟩
    change inner ℝ (fderiv ℝ D.map s.val v)
      (appendZeroMap N (1 + (1 + (d + 1))) w) = 0
    rw [he.fderiv_eq, fderiv_collar_apply b f hf, hwc, inner_coordinates]
    simp only [Prod.fst_zero, Prod.snd_zero, inner_zero_right, add_zero]
    exact Submodule.inner_right_of_mem_orthogonal
      ((SmoothSphereAmbient.range_fderiv_extension_le b f hf s) ⟨v, rfl⟩) hw.2

end FramedDisk

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
