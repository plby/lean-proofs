import Wikipedia.SmoothSixDPoincare.ManifoldImageAvoidance
import Wikipedia.SmoothSixDPoincare.ChartMapHomotopy

/-!
# One relative general-position step in a finite chart cover

The new map avoids the obstacle throughout one bump support, preserves every
previously avoiding point, stays compatible with all remaining charts, and
is homotopic to the old map relative to the prescribed fixed set.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.GeneralPosition

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ G K)
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace N] [ChartedSpace K N]

/-- A genuine chart and a compactly supported smooth source cutoff fixed on `C`. -/
structure MapAvoidancePatch (C : Set X) where
  chart : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞
  cutoff : X → ℝ
  smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ cutoff
  compact : HasCompactSupport cutoff
  fixed : ∀ x ∈ C, cutoff x = 0

variable {I J}

def MapAvoidancePatch.Compatible {C : Set X} (p : MapAvoidancePatch I J (N := N) C)
    (f : X → N) : Prop := MapsTo f (tsupport p.cutoff) p.chart.source

variable {E' H' Y : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ G]
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [IsManifold I ∞ X] [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
  [LindelofSpace (X × Y)]

/-- One patch can be treated while all finitely many future chart conditions remain valid. -/
theorem exists_patch_step {ι : Type*} [Finite ι] {C : Set X}
    (p : ι → MapAvoidancePatch I J (N := N) C) (i : ι)
    (f : C(X, N)) (g : C(Y, N)) (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ (∀ j, (p j).Compatible f') ∧
      f.HomotopicRel f' C ∧
      ∀ x, (f x ∉ range g ∨ (p i).cutoff x ≠ 0) → f' x ∉ range g := by
  have hkeep : ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply eventually_all.mpr
    intro j
    exact ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf
      (p i).smooth (hcompatible i) (p j).compact.isCompact (p j).chart.open_source (hcompatible j)
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hkeep
  obtain ⟨r, hr, hvalid⟩ := ChartMapPerturbation.exists_radius_valid (p i).chart hf
    (p i).smooth (p i).compact (hcompatible i)
  obtain ⟨a, ha, _, hsmooth, havoid⟩ := ChartMapPerturbation.exists_small_avoiding_parameter
    (p i).chart hf hg (p i).smooth (p i).compact (hcompatible i) hdim (lt_min hδ hr)
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).1
  have har : ‖a‖ < r := (lt_min_iff.mp ha).2
  let f' : C(X, N) := ⟨_, hsmooth.continuous⟩
  have H := ChartMapPerturbation.homotopyRel (p i).chart hf (p i).smooth
    (hcompatible i) hvalid har
  refine ⟨f', hsmooth, ?_, ?_, ?_⟩
  · exact hδkeep (by simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  · exact ⟨{ toHomotopy := H.toHomotopy
             prop' := fun t x hx => H.prop t x ((p i).fixed x hx) }⟩
  · intro x hx
    by_cases hzero : (p i).cutoff x = 0
    · have hold : f x ∉ range g := hx.resolve_right (not_not.mpr hzero)
      change ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a x ∉ range g
      rwa [ChartMapPerturbation.perturb_eq_of_zero _ _ _ _ hzero]
    · rintro ⟨y, hy⟩
      exact havoid x hzero y hy.symm

end Wikipedia.SmoothSixDPoincare.GeneralPosition
