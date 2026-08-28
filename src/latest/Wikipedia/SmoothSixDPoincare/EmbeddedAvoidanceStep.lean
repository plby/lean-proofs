import Wikipedia.SmoothSixDPoincare.EmbeddingAvoidanceParameters
import Wikipedia.SmoothSixDPoincare.ChartPerturbationImmersionStability
import Wikipedia.SmoothSixDPoincare.ImageAvoidancePatch
import Wikipedia.SmoothSixDPoincare.ControlledRelativeHomotopy

/-!
# One obstacle-avoidance step retaining compact immersion and all injective restrictions

A single small parameter meets the compact derivative and future-chart
conditions while avoiding both bad-parameter images. Thus obstacle avoidance
does not require sacrificing injectivity and then reconstructing it later.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open GeneralPosition (MapAvoidancePatch)

variable {E E' G H H' Y N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H']
  {J : ModelWithCorners ℝ G H} {I' : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [LindelofSpace (E × Y)]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

/-- Treat one obstacle patch while preserving all previously avoiding points, all existing
injective restrictions, compact native immersion, and every future target chart. -/
theorem exists_embedded_image_avoidance_step_controlled {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (i : ι)
    (f : C(E, N)) (g : C(Y, N)) (A : Set Y)
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    (hK : IsCompact K) (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    {O : Set N} (hO : IsOpen O) (hmaps : MapsTo f K O) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ (∀ j, (p j).Compatible f') ∧
      HomotopicRelWithin f f' C K O ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      (∀ x y, f' x = f' y → f x = f y) ∧ MapsTo f' K O ∧
      ∀ x, (f x ∉ g '' A ∨ (p i).cutoff x ≠ 0) → f' x ∉ g '' A := by
  have hkeep : ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a) := by
    apply eventually_all.mpr
    intro j
    exact ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf
      (p i).smooth (hcompatible i) (p j).compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold := ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf
    (p i).smooth (p i).compact (hcompatible i) hK hderiv
  have hstay := ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf
    (p i).smooth (hcompatible i) hK hO hmaps
  obtain ⟨δ, hδ, hδkeep⟩ := Metric.mem_nhds_iff.mp (hkeep.and (hold.and hstay))
  obtain ⟨r, hr, hvalid⟩ := ChartMapPerturbation.exists_radius_valid (p i).chart hf
    (p i).smooth (p i).compact (hcompatible i)
  obtain ⟨a, ha, -, hsmooth, hnoNew, havoid⟩ :=
    ChartMapPerturbation.exists_small_embedding_avoiding_parameter (p i).chart hf hg
      (p i).smooth (p i).compact (hcompatible i) hself hobstacle (lt_min hδ hr)
  have haδ : ‖a‖ < δ := (lt_min_iff.mp ha).1
  have har : ‖a‖ < r := (lt_min_iff.mp ha).2
  let f' : C(E, N) := ⟨_, hsmooth.continuous⟩
  have hretained := hδkeep (show a ∈ Metric.ball 0 δ by
    simpa only [Metric.mem_ball, dist_zero_right] using haδ)
  let Hrel := ChartMapPerturbation.homotopyRel (p i).chart hf (p i).smooth
    (hcompatible i) hvalid har
  refine ⟨f', hsmooth, hretained.1, ?_, hretained.2.1, hnoNew, hretained.2.2, ?_⟩
  · refine ⟨{ Hrel.toHomotopy with
      prop' := fun t x hx => Hrel.eq_fst t ((p i).fixed x hx) }, ?_⟩
    intro t x hx
    change ChartMapPerturbation.perturb (p i).chart f (p i).cutoff ((t : ℝ) • a) x ∈ O
    have hsmall : (t : ℝ) • a ∈ Metric.ball (0 : G) δ := by
      simpa only [Metric.mem_ball, dist_zero_right] using
        ChartMapPerturbation.norm_interval_smul_lt haδ t
    exact (hδkeep hsmall).2.2 hx
  · intro x hx
    by_cases hzero : (p i).cutoff x = 0
    · have hold : f x ∉ g '' A := hx.resolve_right (not_not.mpr hzero)
      change ChartMapPerturbation.perturb (p i).chart f (p i).cutoff a x ∉ g '' A
      rwa [ChartMapPerturbation.perturb_eq_of_zero _ _ _ _ hzero]
    · rintro ⟨y, _, hy⟩
      exact havoid x hzero y hy.symm

/-- Forgetting trace control gives the original compact-region avoidance API. -/
theorem exists_embedded_image_avoidance_step {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (i : ι)
    (f : C(E, N)) (g : C(Y, N)) (A : Set Y)
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    (hK : IsCompact K) (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    {O : Set N} (hO : IsOpen O) (hmaps : MapsTo f K O) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ (∀ j, (p j).Compatible f') ∧
      f.HomotopicRel f' C ∧ (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      (∀ x y, f' x = f' y → f x = f y) ∧ MapsTo f' K O ∧
      ∀ x, (f x ∉ g '' A ∨ (p i).cutoff x ≠ 0) → f' x ∉ g '' A := by
  obtain ⟨f', hf', hc, hhom, hd, hnoNew, hmaps', havoid⟩ :=
    exists_embedded_image_avoidance_step_controlled p i f g A hf hg hcompatible
      hself hobstacle hK hderiv hO hmaps
  exact ⟨f', hf', hc, hhom.homotopicRel, hd, hnoNew, hmaps', havoid⟩

/-- Treat a whole smooth obstacle image without an additional compact-region target constraint. -/
theorem exists_embedded_avoidance_step {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C) (i : ι)
    (f : C(E, N)) (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    (hK : IsCompact K) (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x)) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ (∀ j, (p j).Compatible f') ∧
      f.HomotopicRel f' C ∧ (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      (∀ x y, f' x = f' y → f x = f y) ∧
      ∀ x, (f x ∉ range g ∨ (p i).cutoff x ≠ 0) → f' x ∉ range g := by
  obtain ⟨f', hf', hc, hhom, hd, hnoNew, -, havoid⟩ :=
    exists_embedded_image_avoidance_step p i f g univ hf hg hcompatible hself hobstacle
      hK hderiv isOpen_univ (fun _ _ => mem_univ _)
  refine ⟨f', hf', hc, hhom, hd, hnoNew, ?_⟩
  simpa only [image_univ] using havoid

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
