import Wikipedia.NoExoticSixSphere.ImmersedDiskCombinedOperator
import Wikipedia.NoExoticSixSphere.SpanningDiskDimension

/-!
# The combined boundary operator of an actual stabilized spanning disk

The operator retains the original normal columns, the five graph axes, and
all four actual disk-derivative columns. Its extension detects the original
disk parity, and its boundary derivative is exactly the retained collar's.
-/

noncomputable section

open Function Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.StabilizedSpanningDisk.DiskData

open GLOrthonormalization Stiefel DiskBoundary

variable {N k : ℕ} {b : Sphere 3} {f : Sphere 3 → Vector N} (D : DiskData b f)
  (hf : ContMDiff (𝓡 3) (𝓡 N) ∞ f) (a : Sphere 3 → Space N k)
  (has : ContMDiff (𝓡 3) 𝓘(ℝ, Vector k →L[ℝ] Vector N) ∞ (fun s ↦ (a s).val))
  (ha : ∀ s, (a s).val.range ≤ (mfderiv (𝓡 3) (𝓡 N) f s).rangeᗮ)

include hf ha in
theorem combinedOperator_injective (s : Sphere 3) :
    Injective (OperatorSum.operator (boundaryFrame (a s)).val (fderiv ℝ D.toFun s.val)) := by
  obtain ⟨V, hV, hSV, heq⟩ := D.collar_eq
  have hn := boundaryFrame_normal_disk b f hf a ha hV hSV heq s
  exact OperatorSum.injective_operator _ _ (Stiefel.injective _)
    (D.immersive s.val (Metric.sphere_subset_closedBall s.property))
    ((fderiv ℝ D.toFun s.val).range.orthogonal_disjoint.symm.mono_left hn)

def combinedMap : C(Sphere 3, Monomorphism.Space (N + 6) ((k + 5) + 4)) where
  toFun s := ⟨OperatorSum.operator (boundaryFrame (a s)).val (fderiv ℝ D.toFun s.val),
    D.combinedOperator_injective hf a ha s⟩
  continuous_toFun := (OperatorSum.continuous_operator _ _
    (contMDiff_boundaryFrameOperator has).continuous
    (D.smooth.continuous_fderiv (by simp) |>.comp continuous_subtype_val)).subtype_mk _

theorem combinedMap_value (s : Sphere 3) :
    (D.combinedMap hf a has ha s).val =
      OperatorSum.operator (boundaryFrameOperator (a s).val) (fderiv ℝ D.toFun s.val) := rfl

theorem fderiv_eq_collar (s : Sphere 3) :
    fderiv ℝ D.toFun s.val = fderiv ℝ (collar b f) s.val := by
  obtain ⟨V, hV, hSV, heq⟩ := D.collar_eq
  have he : D.toFun =ᶠ[𝓝 s.val] collar b f :=
    Filter.mem_of_superset (hV.mem_nhds (hSV s.property)) heq
  exact he.fderiv_eq

theorem combinedMap_collar (s : Sphere 3) :
    (D.combinedMap hf a has ha s).val =
      OperatorSum.operator (boundaryFrameOperator (a s).val) (fderiv ℝ (collar b f) s.val) := by
  rw [D.combinedMap_value, D.fderiv_eq_collar]

theorem parityOfDimension_zero_iff_combined_extension (hN : N = k + 6) :
    D.parityOfDimension hN hf a has ha = 0 ↔ Extends (D.combinedMap hf a has ha) := by
  subst N
  exact ImmersedDisk.parity_zero_iff_combined_extension (k + 3) D.toFun
    (fun _ _ ↦ D.smooth.contDiffAt) D.immersive (boundaryFrameMap a has)
    (D.normal_boundaryFrameMap hf a has ha)

end NoExoticSixSphere.StabilizedSpanningDisk.DiskData
