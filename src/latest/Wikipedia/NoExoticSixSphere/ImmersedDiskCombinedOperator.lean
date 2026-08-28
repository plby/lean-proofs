import Wikipedia.NoExoticSixSphere.NormalDiskCombinedOperator
import Wikipedia.NoExoticSixSphere.ImmersedDiskNormalObstruction

/-!
# Combined operators use the actual derivative of the immersed disk

The exact normal-disk extension criterion applies to the genuine differential
of the smooth disk. A homotopy of the combined boundary operators therefore
preserves its original normal-disk parity.
-/

noncomputable section

open scoped ContDiff

namespace NoExoticSixSphere.Stiefel.ImmersedDisk

open GLOrthonormalization DiskBoundary

variable (r : ℕ) (f : Vector 4 → Vector (r + 9))
  (hf : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ f x)
  (hi : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, Function.Injective (fderiv ℝ f x))
  (a : C(Sphere 3, Space (r + 9) (r + 2)))
  (ha : ∀ s, (a s).val.range ≤ (fderiv ℝ f s.val).rangeᗮ)

def combinedMap : C(Sphere 3, Monomorphism.Space (r + 9) ((r + 2) + 4)) :=
  DiskNormal.combinedMap r (differential r f hf) (differential_injective r f hf hi) a ha

theorem combinedMap_value (s : Sphere 3) :
    (combinedMap r f hf hi a ha s).val = OperatorSum.operator (a s).val (fderiv ℝ f s.val) := rfl

theorem parity_zero_iff_combined_extension :
    parity r f hf hi a ha = 0 ↔ Extends (combinedMap r f hf hi a ha) :=
  DiskNormal.parity_zero_iff_combined_extension r (differential r f hf)
    (differential_injective r f hf hi) a ha

theorem parity_eq_of_combined_homotopic (g : Vector 4 → Vector (r + 9))
    (hg : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ g x)
    (hgi : ∀ x ∈ Metric.closedBall (0 : Vector 4) 1, Function.Injective (fderiv ℝ g x))
    (b : C(Sphere 3, Space (r + 9) (r + 2)))
    (hb : ∀ s, (b s).val.range ≤ (fderiv ℝ g s.val).rangeᗮ)
    (H : (combinedMap r f hf hi a ha).Homotopic (combinedMap r g hg hgi b hb)) :
    parity r f hf hi a ha = parity r g hg hgi b hb := by
  apply zmodTwo_eq_of_zero_iff
  rw [parity_zero_iff_combined_extension, parity_zero_iff_combined_extension]
  exact extends_homotopic_iff H

end NoExoticSixSphere.Stiefel.ImmersedDisk
