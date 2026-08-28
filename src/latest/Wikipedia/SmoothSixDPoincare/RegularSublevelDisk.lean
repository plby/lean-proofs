import Wikipedia.SmoothSixDPoincare.SublevelDisk
import Wikipedia.SmoothSixDPoincare.RegularSublevelHomeomorph

/-!
# Transporting a boundary-compatible disk through a regular band

The regular-sublevel homeomorphism preserves the actual top level, so a
standard disk description of the lower sublevel extends to the upper one
with its sphere boundary still identified exactly.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare

namespace SublevelDisk

variable {M : Type*} [TopologicalSpace M] {n : ℕ} {f : M → ℝ} {a b : ℝ}

/-- Transport a sublevel disk through a homeomorphism preserving its exact top level. -/
def transport (d : SublevelDisk n f a)
    (e : {x : M // f x ≤ a} ≃ₜ {x : M // f x ≤ b})
    (he : ∀ x, f (e x).1 = b ↔ f x.1 = a) : SublevelDisk n f b where
  homeomorph := d.homeomorph.trans e
  boundary_iff v := (he (d.homeomorph v)).trans (d.boundary_iff v)

end SublevelDisk

namespace FlowConstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- A disk sublevel remains a disk across a band containing no critical point. -/
theorem nonempty_regularSublevelDisk {n : ℕ} {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c a b : ℝ} (hca : c < a) (hcb : c < b)
    (hband : ∀ x, f x ∈ Icc c (max a b) → x ∉ ManifoldMorse.criticalPoints E f)
    (d : SublevelDisk n f a) : Nonempty (SublevelDisk n f b) := by
  obtain ⟨e, he⟩ := exists_regularSublevelHomeomorph_with_level hf hca hcb hband
  exact ⟨d.transport e he⟩

end FlowConstruction
end Wikipedia.SmoothSixDPoincare
