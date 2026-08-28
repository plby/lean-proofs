import Wikipedia.NoExoticSixSphere.FiniteLoweringStep

/-!
# Fixed-neighborhood quantitative lowering data

This package records the actual relative-homotopy interface used by the finite
construction. A spatial tolerance is chosen only after the neighborhood and
endpoint threshold have been fixed. No classification statement is a field.
-/

open Set

namespace NoExoticSixSphere.FiniteControlledLowering

variable {M Y : Type*} [TopologicalSpace M] [PseudoMetricSpace Y]

structure LocalLoweringData (M : Type*) [TopologicalSpace M]
    (energy : Y → ℝ) (admissible : Set Y) (floor level cap : ℝ) where
  domain : Set Y
  open_domain : IsOpen domain
  domain_subset : domain ⊆ admissible
  domain_above : ∀ z ∈ domain, floor < energy z
  threshold : ℝ
  floor_lt_threshold : floor < threshold
  threshold_lt_level : threshold < level
  control : ∀ ρ > 0, ∃ ζ > 0, ∀ ξ : ℝ, 0 < ξ → ξ ≤ ζ →
    StepProperty (M := M) energy admissible domain floor threshold cap ξ ζ ρ

theorem StepProperty.smaller_window {energy : Y → ℝ} {admissible V : Set Y}
    {floor k cap ξ ζ ζ' ρ : ℝ}
    (h : StepProperty (M := M) energy admissible V floor k cap ξ ζ' ρ) (hle : ζ ≤ ζ') :
    StepProperty (M := M) energy admissible V floor k cap ξ ζ ρ := by
  intro p hp K hK hKV
  obtain ⟨q, hq, G, hG⟩ := h p hp K hK hKV
  refine ⟨q, hq, G, fun t x ↦ ⟨(hG t x).1, (hG t x).2.1, (hG t x).2.2.1, ?_⟩⟩
  intro hLoss
  apply (hG t x).2.2.2
  linarith

end NoExoticSixSphere.FiniteControlledLowering
