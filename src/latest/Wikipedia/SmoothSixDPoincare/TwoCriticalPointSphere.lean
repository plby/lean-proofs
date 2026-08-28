import Wikipedia.SmoothSixDPoincare.MorseDiskPropagation
import Wikipedia.SmoothSixDPoincare.MorseNegation
import Wikipedia.SmoothSixDPoincare.ManifoldFermat
import Wikipedia.SmoothSixDPoincare.SublevelDiskGluing

/-!
# Sphere recognition from a genuine Morse function with two critical points

Compactness and Fermat identify the two ordered critical values with the
unique minimum and maximum. The actual small extremal disks are extended
through regular bands to a common level and glued along their true boundaries.

Producing such a two-critical-point function from the homotopy-sphere
hypothesis still requires the separate six-dimensional cancellation argument.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- A smooth Morse function with exactly two critical points at distinct ordered values yields
a homeomorphism of the original manifold with the standard sphere of its model dimension. -/
theorem nonempty_homeomorphSphere_of_two_critical_points {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    {p q : M} (hpq : f p < f q) (hcrit : criticalPoints E f = {p, q}) :
    Nonempty (M ≃ₜ Hemisphere.Sphere (Module.finrank ℝ E)) := by
  have hcover : ∀ x ∈ criticalPoints E f, x = p ∨ x = q := by
    intro x hx
    rw [hcrit] at hx
    simpa only [mem_insert_iff, mem_singleton_iff] using hx
  have hp : p ∈ criticalPoints E f := by rw [hcrit]; simp
  have hq : q ∈ criticalPoints E f := by rw [hcrit]; simp
  obtain ⟨hmin, hmax⟩ := unique_extrema_of_two_critical_values hf hpq hcover
  obtain ⟨cp⟩ := nonempty_signedMorseChart hf hm p hp
  obtain ⟨cq⟩ := nonempty_signedMorseChart hf hm q hq
  let a := (f p + f q) / 2
  have hpa : f p < a := by dsimp [a]; linarith
  have haq : a < f q := by dsimp [a]; linarith
  have hregularL : ∀ x, f p < f x → f x ≤ a → x ∉ criticalPoints E f := by
    intro x hxlo hxhi hxcrit
    rcases hcover x hxcrit with h | h
    · rw [h] at hxlo
      exact lt_irrefl _ hxlo
    · rw [h] at hxhi
      exact not_le_of_gt haq hxhi
  obtain ⟨L⟩ := cp.nonempty_sublevelDisk_before_next_critical hf hmin hpa hregularL
  have hminNeg : ∀ x, -f x ≤ -f q → x = q :=
    fun x hx => hmax x (neg_le_neg_iff.mp hx)
  have hregularR : ∀ x, -f q < -f x → -f x ≤ -a →
      x ∉ criticalPoints E (fun y => -f y) := by
    intro x hxlo hxhi hxcrit
    have hxcrit' : x ∈ criticalPoints E f := by
      rw [← criticalPoints_neg (E := E) f]
      exact hxcrit
    rcases hcover x hxcrit' with h | h
    · rw [h] at hxhi
      linarith
    · rw [h] at hxlo
      exact lt_irrefl _ hxlo
  obtain ⟨R⟩ := cq.neg.nonempty_sublevelDisk_before_next_critical hf.neg hminNeg
    (neg_lt_neg haq) hregularR
  exact ⟨homeomorphSphereOfSublevelDisks L R⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse
