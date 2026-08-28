import Wikipedia.SmoothSixDPoincare.CurveImmersionPatch
import Wikipedia.SmoothSixDPoincare.ChartPerturbationImmersionStability
import Wikipedia.SmoothSixDPoincare.MapSmoothingPatch

/-!
# Finite relative curve-immersion improvement

A small parameter repairs the next plateau, retains the already immersive
compact region, and preserves all future target-chart constraints. The actual
relative homotopies concatenate, and every prescribed fixed point stays fixed.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open ManifoldSmoothing (MapSmoothingPatch)

variable {G H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

/-- Add one immersive curve patch while retaining the old region and all future chart domains. -/
theorem exists_curve_immersion_patch_step_within_target {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch 𝓘(ℝ, ℝ) J (X := ℝ) (N := N)) (i : ι)
    (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hcompatible : ∀ j, (p j).Compatible f) (hdim : 3 ≤ Module.finrank ℝ G)
    {K L C : Set ℝ} (hK : IsCompact K)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hLsub : L ⊆ (p i).plateau) (hfixed : ∀ t ∈ C, (p i).cutoff t = 0)
    {D : Set ℝ} {O : Set N} (hsource : (p i).chart.source ⊆ O) (hmaps : MapsTo f D O) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
      (∀ j, (p j).Compatible g) ∧ HomotopicRelWithin f g C D O ∧
      ∀ t ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let w := CurveImmersion.weight (p i).cutoff
  have hw : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ w :=
    (CurveImmersion.contDiff_weight (p i).smooth.contDiff).contMDiff
  have hinner := (p i).inner_compatible (hcompatible i)
  have hwsupport : tsupport w ⊆ f ⁻¹' (p i).chart.source :=
    (CurveImmersion.tsupport_weight_subset (p i).cutoff).trans hinner
  have hkeep : ∀ᶠ a : G in 𝓝 0,
      ∀ j, (p j).Compatible (ChartMapPerturbation.perturb (p i).chart f w a) := by
    apply eventually_all.mpr
    intro j
    exact ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf hw
      hwsupport (p j).outer_compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold := ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf hw
    (CurveImmersion.hasCompactSupport_weight (p i).compact) hwsupport hK hinj
  let Q : (ℝ → N) → Prop := fun g => (∀ j, (p j).Compatible g) ∧
    ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t)
  have hQ : ∀ᶠ a : G in 𝓝 0, Q (ChartMapPerturbation.perturb (p i).chart f w a) :=
    hkeep.and hold
  obtain ⟨g, hg, ⟨hc, hKnew⟩, hrel, hplateau⟩ :=
    exists_curve_immersion_patch_with_property_within_target (p i).chart f hf
      (p i).smooth.contDiff (p i).outer_smooth.contDiff (p i).compact
      (hcompatible i) (p i).nested hdim Q hQ hsource hmaps
  refine ⟨g, hg, hc, ?_, ?_⟩
  · exact hrel.mono hfixed (Subset.refl D) (Subset.refl O)
  · intro t ht
    rcases ht with ht | ht
    · exact hKnew t ht
    · exact hplateau t (hLsub ht)

/-- The original local immersion step, forgetting its controlled target. -/
theorem exists_curve_immersion_patch_step {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch 𝓘(ℝ, ℝ) J (X := ℝ) (N := N)) (i : ι)
    (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hcompatible : ∀ j, (p j).Compatible f) (hdim : 3 ≤ Module.finrank ℝ G)
    {K L C : Set ℝ} (hK : IsCompact K)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hLsub : L ⊆ (p i).plateau) (hfixed : ∀ t ∈ C, (p i).cutoff t = 0) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
      (∀ j, (p j).Compatible g) ∧ f.HomotopicRel g C ∧
      ∀ t ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  obtain ⟨g, hg, hc, hrel, hi⟩ :=
    exists_curve_immersion_patch_step_within_target p i f hf hcompatible hdim hK hinj
      hLsub hfixed (subset_univ _) (mapsTo_univ f univ)
  exact ⟨g, hg, hc, hrel.homotopicRel, hi⟩

/-- Finite immersion improvement with its complete trace in the prescribed target. -/
theorem exists_finite_curve_patch_immersion_within_target {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch 𝓘(ℝ, ℝ) J (X := ℝ) (N := N))
    (L : ι → Set ℝ) (hL : ∀ i, IsCompact (L i)) (hLsub : ∀ i, L i ⊆ (p i).plateau)
    (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hcompatible : ∀ i, (p i).Compatible f) (hdim : 3 ≤ Module.finrank ℝ G)
    {K C : Set ℝ} (hK : IsCompact K)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hfixed : ∀ i t, t ∈ C → (p i).cutoff t = 0)
    {D : Set ℝ} {O : Set N} (hsource : ∀ i, (p i).chart.source ⊆ O)
    (hmaps : MapsTo f D O) (s : Finset ι) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
      (∀ i, (p i).Compatible g) ∧ HomotopicRelWithin f g C D O ∧
      ∀ t ∈ K ∪ ⋃ i ∈ s, L i, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, HomotopicRelWithin.refl f C hmaps, ?_⟩
    simpa only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, union_empty] using hinj
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hinj₁⟩ := ih
    have hKold : IsCompact (K ∪ ⋃ j ∈ s, L j) :=
      hK.union (s.isCompact_biUnion (fun j _ => hL j))
    obtain ⟨g₂, hg₂, hc₂, hhom₂, hinj₂⟩ :=
      exists_curve_immersion_patch_step_within_target p i g₁ hg₁ hc₁
        hdim hKold hinj₁ (hLsub i) (hfixed i) (hsource i) hhom₁.mapsTo_right
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, ?_⟩
    intro t ht
    apply hinj₂ t
    rcases ht with ht | ht
    · exact Or.inl (Or.inl ht)
    · obtain ⟨j, hj, htj⟩ := mem_iUnion₂.mp ht
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr htj
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨j, hjs, htj⟩))

/-- The original finite immersion API, with target control forgotten. -/
theorem exists_finite_curve_patch_immersion {ι : Type*} [Finite ι]
    (p : ι → MapSmoothingPatch 𝓘(ℝ, ℝ) J (X := ℝ) (N := N))
    (L : ι → Set ℝ) (hL : ∀ i, IsCompact (L i)) (hLsub : ∀ i, L i ⊆ (p i).plateau)
    (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hcompatible : ∀ i, (p i).Compatible f) (hdim : 3 ≤ Module.finrank ℝ G)
    {K C : Set ℝ} (hK : IsCompact K)
    (hinj : ∀ t ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t))
    (hfixed : ∀ i t, t ∈ C → (p i).cutoff t = 0) (s : Finset ι) :
    ∃ g : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
      (∀ i, (p i).Compatible g) ∧ f.HomotopicRel g C ∧
      ∀ t ∈ K ∪ ⋃ i ∈ s, L i, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  obtain ⟨g, hg, hc, hrel, hi⟩ :=
    exists_finite_curve_patch_immersion_within_target p L hL hLsub f hf hcompatible hdim
      hK hinj hfixed (fun _ => subset_univ _) (mapsTo_univ f univ) s
  exact ⟨g, hg, hc, hrel.homotopicRel, hi⟩

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
