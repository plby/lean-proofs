import Wikipedia.SmoothSixDPoincare.ChartSmoothing
import Wikipedia.SmoothSixDPoincare.ChartPerturbationTargetControl

/-!
# A relative smoothing step preserving a finite target-chart cover

Two nested cutoffs give globally defined coordinates and a unit plateau on
which those coordinates can be replaced by a smooth approximation. Smallness
preserves the finitely many remaining target-chart conditions.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldSmoothing

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ G K)
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace N] [ChartedSpace K N]

/-- A target chart and nested compact smooth cutoffs on the source. -/
structure MapSmoothingPatch where
  chart : PartialDiffeomorph J 𝓘(ℝ, G) N G ∞
  cutoff : X → ℝ
  outer : X → ℝ
  smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ cutoff
  outer_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ outer
  compact : HasCompactSupport cutoff
  outer_compact : HasCompactSupport outer
  nested : ∀ x ∈ tsupport cutoff, outer x = 1

variable {I J}

namespace MapSmoothingPatch

variable (p : MapSmoothingPatch I J (X := X) (N := N))

def Compatible (f : X → N) : Prop := MapsTo f (tsupport p.outer) p.chart.source

def plateau : Set X := interior {x | p.cutoff x = 1}

theorem inner_support_subset_outer : tsupport p.cutoff ⊆ tsupport p.outer := by
  intro x hx
  apply subset_tsupport p.outer
  change p.outer x ≠ 0
  rw [p.nested x hx]
  exact one_ne_zero

theorem inner_compatible {f : X → N} (hf : p.Compatible f) :
    tsupport p.cutoff ⊆ f ⁻¹' p.chart.source :=
  fun _ hx => hf (p.inner_support_subset_outer hx)

theorem plateau_eventually_one {x : X} (hx : x ∈ p.plateau) :
    p.cutoff =ᶠ[𝓝 x] (fun _ => 1) := by
  filter_upwards [isOpen_interior.mem_nhds hx] with y hy
  exact interior_subset (s := {y : X | p.cutoff y = 1}) hy

end MapSmoothingPatch

variable [FiniteDimensional ℝ E] [IsManifold I ∞ X] [SigmaCompactSpace X] [T2Space X]

/-- Smooth one plateau, retain all previously smooth points, and fix the prescribed closed set. -/
theorem exists_smoothing_patch_step_within_target {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch I J (X := X) (N := N)) (i : ι)
    (f : C(X, N)) (hcompatible : ∀ j, (p j).Compatible f)
    {C U : Set X} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) {D : Set X} {O : Set N}
    (hsource : (p i).chart.source ⊆ O) (hmaps : MapsTo f D O) :
    ∃ f' : C(X, N), (∀ j, (p j).Compatible f') ∧ HomotopicRelWithin f f' C D O ∧
      ∀ x, ContMDiffAt I J ∞ f x ∨ x ∈ (p i).plateau → ContMDiffAt I J ∞ f' x := by
  have hinner := (p i).inner_compatible (hcompatible i)
  have hkeep : ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply eventually_all.mpr
    intro j
    exact ChartMapPerturbation.eventually_maps_compact_into_open_of_continuous
      (p i).chart f.continuous (p i).smooth.continuous hinner
      (p j).outer_compact.isCompact (p j).chart.open_source (hcompatible j)
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp hkeep
  obtain ⟨r, hr, hvalid⟩ := ChartMapPerturbation.exists_radius_valid_of_continuous
    (p i).chart f.continuous (p i).smooth.continuous (p i).compact hinner
  obtain ⟨g, hg, happrox, heq⟩ := ChartMapPerturbation.exists_smooth_coordinate_approximation
    (p i).chart f.continuous (p i).outer_smooth (hcompatible i) hC hU hCU hfU (lt_min hδ hr)
  let a : X → G := fun x => g x - ChartMapPerturbation.cutoffCoordinates (p i).chart f (p i).outer x
  have ha : Continuous a := hg.continuous.sub
    (ChartMapPerturbation.continuous_cutoffCoordinates (p i).chart f.continuous
      (p i).outer_smooth.continuous (hcompatible i))
  have hbound (x : X) : ‖a x‖ < min δ r := by
    simpa only [a, dist_eq_norm] using happrox x
  have haδ (x : X) : ‖a x‖ < δ := (lt_min_iff.mp (hbound x)).1
  have har (x : X) : ‖a x‖ < r := (lt_min_iff.mp (hbound x)).2
  let f' : C(X, N) := ⟨ChartMapPerturbation.variablePerturb (p i).chart f (p i).cutoff a,
    ChartMapPerturbation.continuous_variablePerturb (p i).chart f.continuous
      (p i).smooth.continuous hinner ha (fun x => hvalid _ (har x))⟩
  refine ⟨f', ?_, ?_, ?_⟩
  · intro j x hx
    have hh := hδkeep (show a x ∈ Metric.ball 0 δ by
      simpa only [Metric.mem_ball, dist_zero_right] using haδ x)
    exact hh j hx
  · exact ChartMapPerturbation.variableHomotopicRelWithin_of_source_subset
      (p i).chart f.continuous (p i).smooth.continuous hinner ha hvalid har
      (fun x hx => Or.inr (sub_eq_zero.mpr (heq hx))) hsource hmaps
  · intro x hx
    rcases hx with hold | hplateau
    · exact ChartMapPerturbation.contMDiffAt_smoothedMap_of_old (p i).chart hinner
        (hcompatible i) hold (p i).smooth.contMDiffAt (p i).outer_smooth.contMDiffAt
        hg.contMDiffAt (hvalid _ (har x))
    · exact ChartMapPerturbation.contMDiffAt_smoothedMap_on_plateau (p i).chart hinner
        (p i).nested ((p i).plateau_eventually_one hplateau) hg.contMDiffAt (hvalid _ (har x))

/-- Forgetting target containment retains the original local smoothing API. -/
theorem exists_smoothing_patch_step {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch I J (X := X) (N := N)) (i : ι)
    (f : C(X, N)) (hcompatible : ∀ j, (p j).Compatible f)
    {C U : Set X} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) :
    ∃ f' : C(X, N), (∀ j, (p j).Compatible f') ∧ f.HomotopicRel f' C ∧
      ∀ x, ContMDiffAt I J ∞ f x ∨ x ∈ (p i).plateau → ContMDiffAt I J ∞ f' x := by
  obtain ⟨f', hc, hrel, hsm⟩ :=
    exists_smoothing_patch_step_within_target p i f hcompatible hC hU hCU hfU
      (subset_univ _) (mapsTo_univ f univ)
  exact ⟨f', hc, hrel.homotopicRel, hsm⟩

end Wikipedia.SmoothSixDPoincare.ManifoldSmoothing
