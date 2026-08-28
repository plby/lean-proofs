import Wikipedia.SmoothSixDPoincare.MinimumDiskSublevel
import Wikipedia.SmoothSixDPoincare.MinimumDiskCoordinates
import Wikipedia.SmoothSixDPoincare.SublevelDisk

/-!
# A standard, boundary-compatible disk at a unique Morse minimum

The exact height formula and the isometric dimension identification
produce the standard disk together with its correct level-set boundary.
-/

noncomputable section

open Set Metric Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

include c

open Classical in
/-- Construct a standard closed sublevel disk with its exact sphere boundary at a unique minimum. -/
theorem exists_minimumSublevelDisk (hf : Continuous f)
    (hunique : ∀ x, f x ≤ f p → x = p) {b : ℝ} (hb : f p < b) :
    ∃ a ∈ Ioo (f p) b, Nonempty (SublevelDisk (Module.finrank ℝ E) f a) := by
  have hglobal : ∀ x, f p ≤ f x := by
    intro x
    by_contra! h
    have hxp := hunique x h.le
    rw [hxp] at h
    exact lt_irrefl _ h
  have hmin : IsLocalMin f p := Filter.Eventually.of_forall hglobal
  obtain ⟨ρ, hρ, hab, e, he⟩ :=
    exists_minimum_disk_sublevel_with_height c hf hunique hb
  let d := (c.minimumDiskHomeomorph hmin).symm.trans e
  have hd (v : Hemisphere.Ball (Module.finrank ℝ E)) :
      f (d v).1 = f p + ρ ^ 2 * ‖(v : Hemisphere.Ambient (Module.finrank ℝ E))‖ ^ 2 := by
    change f (e ((c.minimumDiskHomeomorph hmin).symm v)).1 = _
    rw [he, c.norm_minimumDiskHomeomorph_symm]
  refine ⟨f p + ρ ^ 2, ⟨by linarith [sq_pos_of_pos hρ], hab⟩, ⟨⟨d, ?_⟩⟩⟩
  intro v
  rw [hd]
  constructor
  · intro h
    have hs : ‖(v : Hemisphere.Ambient (Module.finrank ℝ E))‖ ^ 2 = 1 :=
      mul_left_cancel₀ (pow_ne_zero 2 hρ.ne') (by linarith)
    nlinarith [norm_nonneg (v : Hemisphere.Ambient (Module.finrank ℝ E))]
  · intro h
    rw [h, one_pow, mul_one]

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
