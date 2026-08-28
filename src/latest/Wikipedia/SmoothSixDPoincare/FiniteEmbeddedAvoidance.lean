import Wikipedia.SmoothSixDPoincare.EmbeddedAvoidanceStep

/-!
# Finite obstacle avoidance without losing embeddedness

The no-new-coincidence implication and preservation of every previously
avoiding point compose through the entire finite patch construction.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

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

/-- Finite obstacle avoidance preserves compact native immersion and introduces no new
coincidences anywhere, hence retains every initial injective restriction. -/
theorem exists_finite_embedded_image_avoidance_controlled {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C)
    (f : C(E, N)) (g : C(Y, N)) (A : Set Y)
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    (hK : IsCompact K) (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    {O : Set N} (hO : IsOpen O) (hmaps : MapsTo f K O) (s : Finset ι) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ (∀ j, (p j).Compatible f') ∧
      HomotopicRelWithin f f' C K O ∧
      (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      (∀ x y, f' x = f' y → f x = f y) ∧ MapsTo f' K O ∧
      ∀ x, (f x ∉ g '' A ∨ ∃ i ∈ s, (p i).cutoff x ≠ 0) → f' x ∉ g '' A := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, HomotopicRelWithin.refl f C hmaps,
      hderiv, (fun _ _ hxy => hxy), hmaps, ?_⟩
    intro x hx
    simpa only [Finset.notMem_empty, false_and, exists_false, or_false] using hx
  | @insert i s _ ih =>
    obtain ⟨f₁, hf₁, hc₁, hhom₁, hd₁, hnoNew₁, hmaps₁, havoid₁⟩ := ih
    obtain ⟨f₂, hf₂, hc₂, hhom₂, hd₂, hnoNew₂, hmaps₂, havoid₂⟩ :=
      exists_embedded_image_avoidance_step_controlled p i f₁ g A hf₁ hg hc₁ hself hobstacle
        hK hd₁ hO hmaps₁
    refine ⟨f₂, hf₂, hc₂, hhom₁.trans hhom₂, hd₂,
      (fun x y hxy => hnoNew₁ x y (hnoNew₂ x y hxy)), hmaps₂, ?_⟩
    intro x hx
    apply havoid₂ x
    rcases hx with hold | ⟨j, hj, hactive⟩
    · exact Or.inl (havoid₁ x (Or.inl hold))
    · rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hactive
      · exact Or.inl (havoid₁ x (Or.inr ⟨j, hjs, hactive⟩))

/-- The original finite avoidance theorem, forgetting containment of the full homotopy. -/
theorem exists_finite_embedded_image_avoidance {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C)
    (f : C(E, N)) (g : C(Y, N)) (A : Set Y)
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    (hK : IsCompact K) (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    {O : Set N} (hO : IsOpen O) (hmaps : MapsTo f K O) (s : Finset ι) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ (∀ j, (p j).Compatible f') ∧
      f.HomotopicRel f' C ∧ (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      (∀ x y, f' x = f' y → f x = f y) ∧ MapsTo f' K O ∧
      ∀ x, (f x ∉ g '' A ∨ ∃ i ∈ s, (p i).cutoff x ≠ 0) → f' x ∉ g '' A := by
  obtain ⟨f', hf', hc, hhom, hd, hnoNew, hmaps', havoid⟩ :=
    exists_finite_embedded_image_avoidance_controlled p f g A hf hg hcompatible
      hself hobstacle hK hderiv hO hmaps s
  exact ⟨f', hf', hc, hhom.homotopicRel, hd, hnoNew, hmaps', havoid⟩

/-- Finite avoidance of a whole smooth image, with no extra compact-region target constraint. -/
theorem exists_finite_embedded_avoidance {ι : Type*} [Finite ι] {C K : Set E}
    (p : ι → MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C)
    (f : C(E, N)) (g : C(Y, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hcompatible : ∀ j, (p j).Compatible f)
    (hself : 2 * Module.finrank ℝ E < Module.finrank ℝ G)
    (hobstacle : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    (hK : IsCompact K) (hderiv : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f x))
    (s : Finset ι) :
    ∃ f' : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ f' ∧ (∀ j, (p j).Compatible f') ∧
      f.HomotopicRel f' C ∧ (∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f' x)) ∧
      (∀ x y, f' x = f' y → f x = f y) ∧
      ∀ x, (f x ∉ range g ∨ ∃ i ∈ s, (p i).cutoff x ≠ 0) → f' x ∉ range g := by
  obtain ⟨f', hf', hc, hhom, hd, hnoNew, -, havoid⟩ :=
    exists_finite_embedded_image_avoidance p f g univ hf hg hcompatible hself hobstacle
      hK hderiv isOpen_univ (fun _ _ => mem_univ _) s
  refine ⟨f', hf', hc, hhom, hd, hnoNew, ?_⟩
  simpa only [image_univ] using havoid

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
