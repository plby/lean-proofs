import Wikipedia.SmoothSixDPoincare.MinimumSublevelDisk
import Wikipedia.SmoothSixDPoincare.RegularSublevelDisk

/-!
# Propagating an extremal disk up to any intervening regular level

Start with the constructed small disk at the unique minimum, then use a
slightly enlarged regular band to transport it while retaining the exact
boundary-level correspondence.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

include c

/-- A sublevel below the next critical point is a standard disk with its correct boundary. -/
theorem nonempty_sublevelDisk_before_next_critical
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b)
    (hregular : ∀ x, f p < f x → f x ≤ b → x ∉ criticalPoints E f) :
    Nonempty (SublevelDisk (Module.finrank ℝ E) f b) := by
  obtain ⟨a, ha, ⟨d⟩⟩ := c.exists_minimumSublevelDisk hf.continuous hunique hb
  obtain ⟨l, hpl, hla⟩ := exists_between ha.1
  apply FlowConstruction.nonempty_regularSublevelDisk hf hla (hla.trans ha.2) _ d
  intro x hx
  apply hregular x (hpl.trans_le hx.1)
  exact hx.2.trans (max_le ha.2.le le_rfl)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
