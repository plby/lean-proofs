import Wikipedia.SmoothSixDPoincare.SelfIntersectionParameters
import Wikipedia.SmoothSixDPoincare.ChartPerturbationImmersionStability
import Wikipedia.SmoothSixDPoincare.ImageAvoidancePatch
import Wikipedia.SmoothSixDPoincare.ChartPerturbationTargetControl

/-!
# One self-intersection removal step preserving immersion and future charts

The small parameter simultaneously retains injective derivatives on the
compact region, preserves the finite collection of target-chart conditions,
and removes all coincidences whose values of the chosen cutoff differ.
No new coincidences are introduced, even outside the compact region.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open GeneralPosition (MapAvoidancePatch)

variable {E G H N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

/-- A finite-cover step removes every collision distinguished by the chosen cutoff while
preserving compact immersion, the fixed set, and all future target charts. -/
theorem exists_selfIntersection_removal_step_within_target
    {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (i : ι)
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hK : IsCompact K) (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    {D : Set E} {O : Set N} (hsource : (p i).chart.source ⊆ O) (hmaps : MapsTo f D O) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ g ∧ (∀ j, (p j).Compatible g) ∧
      HomotopicRelWithin f g C D O ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x)) ∧
      ∀ x y, g x = g y → f x = f y ∧ (p i).cutoff x = (p i).cutoff y := by
  have hkeep : ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply eventually_all.mpr
    intro j
    exact ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf
      (p i).smooth (hcompatible i) (p j).compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold := ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf
    (p i).smooth (p i).compact (hcompatible i) hK hinj
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp (hkeep.and hold)
  obtain ⟨r, hr, hvalid⟩ := ChartMapPerturbation.exists_radius_valid (p i).chart hf
    (p i).smooth (p i).compact (hcompatible i)
  obtain ⟨a, ha, -, hsmooth, hremove⟩ :=
    ChartMapPerturbation.exists_small_collision_removing_parameter
      (p i).chart hf (p i).smooth (p i).compact (hcompatible i) hdim (lt_min hδ hr)
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).1
  have har : ‖a‖ < r := (lt_min_iff.mp ha).2
  let g : C(E, N) := ⟨_, hsmooth.continuous⟩
  have hretained := hδkeep (show a ∈ Metric.ball 0 δ by
    simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  refine ⟨g, hsmooth, hretained.1, ?_, hretained.2, hremove⟩
  have hrel := ChartMapPerturbation.homotopicRelWithin_of_source_subset
    (p i).chart hf (p i).smooth (hcompatible i) hvalid har hsource hmaps
  exact hrel.mono (fun x hx => (p i).fixed x hx) (Subset.refl D) (Subset.refl O)

/-- The original collision-removal step, without an additional controlled target. -/
theorem exists_selfIntersection_removal_step {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (i : ι)
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hdim : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hK : IsCompact K) (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ g ∧ (∀ j, (p j).Compatible g) ∧
      f.HomotopicRel g C ∧ (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g x)) ∧
      ∀ x y, g x = g y → f x = f y ∧ (p i).cutoff x = (p i).cutoff y := by
  obtain ⟨g, hg, hc, hrel, hi, hp⟩ :=
    exists_selfIntersection_removal_step_within_target p i f hf hcompatible hdim hK hinj
      (subset_univ _) (mapsTo_univ f univ)
  exact ⟨g, hg, hc, hrel.homotopicRel, hi, hp⟩

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
