import Wikipedia.HopfProblem.OrbitPairCleanCollisionArcs
import Wikipedia.HopfProblem.OrbitPairNativeLocalInjectivity

/-!
# Saturated two-branch neighborhoods of a collision-arc boundary

The full fixed-time preimage of the two projected boundary arcs is exactly
the union of their two source arcs. Compact injectivity neighborhoods and
compactness of the source then give one open target neighborhood whose
entire slice preimage splits into two disjoint injective open branches.

This controls the full time slice, not just the chosen parametrizations.
It does not yet give a time-uniform neighborhood of the six-dimensional
track or the adapted chart around a Whitney disk.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [PathConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [T2Space N]

theorem CollisionArcPair.preimage_image_source_arcs
    {F : ℝ × M → N} {t : ℝ} {x₀ x₁ y₀ y₁ : M}
    (a : CollisionArcPair (I := I) (J := J) F t x₀ x₁ y₀ y₁) :
    (fun z => F (t, z)) ⁻¹'
        ((fun z => F (t, z)) ''
          (range (fun s : unitInterval => a.firstArc s) ∪
            range (fun s : unitInterval => a.secondArc s))) =
      range (fun s : unitInterval => a.firstArc s) ∪
        range (fun s : unitInterval => a.secondArc s) := by
  ext z
  constructor
  · rintro ⟨w, (⟨s, rfl⟩ | ⟨s, rfl⟩), heq⟩
    · rcases (a.first_fiber s s.property z).mp heq.symm with hz | ⟨-, hz⟩ | ⟨-, hz⟩
      · exact Or.inl ⟨s, hz.symm⟩
      · exact Or.inr ⟨0, a.second_zero.trans hz.symm⟩
      · exact Or.inr ⟨1, a.second_one.trans hz.symm⟩
    · rcases (a.second_fiber s s.property z).mp heq.symm with hz | ⟨-, hz⟩ | ⟨-, hz⟩
      · exact Or.inr ⟨s, hz.symm⟩
      · exact Or.inl ⟨0, a.first_zero.trans hz.symm⟩
      · exact Or.inl ⟨1, a.first_one.trans hz.symm⟩
  · intro hz
    exact ⟨z, hz, rfl⟩

variable [FiniteDimensional ℝ G] [J.Boundaryless] [IsManifold J ∞ N] [CompactSpace M]

theorem CollisionArcPair.exists_saturated_slice_neighborhoods
    {F : ℝ × M → N} {t : ℝ} {x₀ x₁ y₀ y₁ : M}
    (a : CollisionArcPair (I := I) (J := J) F t x₀ x₁ y₀ y₁)
    (hF : ContMDiff I J ∞ (fun z => F (t, z)))
    (hi : ∀ z, Injective (mfderiv I J (fun w => F (t, w)) z)) :
    ∃ O : Set N, IsOpen O ∧ ∃ U V : Set M,
      IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧
      U ∪ V = (fun z => F (t, z)) ⁻¹' O ∧
      (∀ s ∈ Icc (0 : ℝ) 1, a.firstArc s ∈ U ∧ a.secondArc s ∈ V) ∧
      InjOn (fun z => F (t, z)) U ∧ InjOn (fun z => F (t, z)) V := by
  let A : Set M := range (fun s : unitInterval => a.firstArc s)
  let B : Set M := range (fun s : unitInterval => a.secondArc s)
  have hA : IsCompact A := isCompact_range (a.firstArc.continuous.comp continuous_subtype_val)
  have hB : IsCompact B := isCompact_range (a.secondArc.continuous.comp continuous_subtype_val)
  obtain ⟨R₁, R₂, hR₁, hR₂, hAR₁, hBR₂, hRdisj⟩ :=
    SeparatedNhds.of_isCompact_isCompact hA hB a.source_disjoint
  have hAi : InjOn (fun z => F (t, z)) A := by
    rintro _ ⟨s, rfl⟩ _ ⟨u, rfl⟩ heq
    exact congrArg (fun v : unitInterval => a.firstArc v) (a.target_first_embedding.injective heq)
  have hBi : InjOn (fun z => F (t, z)) B := by
    rintro _ ⟨s, rfl⟩ _ ⟨u, rfl⟩ heq
    exact congrArg (fun v : unitInterval => a.secondArc v) (a.target_second_embedding.injective heq)
  obtain ⟨W₁, hW₁, hAW₁, hW₁R₁, hWi₁⟩ :=
    NativeImmersion.exists_open_injOn_near_compact hR₁ hF.contMDiffOn hA hAR₁ hAi
      (fun z _ => hi z)
  obtain ⟨W₂, hW₂, hBW₂, hW₂R₂, hWi₂⟩ :=
    NativeImmersion.exists_open_injOn_near_compact hR₂ hF.contMDiffOn hB hBR₂ hBi
      (fun z _ => hi z)
  have hWdisj : Disjoint W₁ W₂ := hRdisj.mono hW₁R₁ hW₂R₂
  have hpre : (fun z => F (t, z)) ⁻¹' ((fun z => F (t, z)) '' (A ∪ B)) ⊆ W₁ ∪ W₂ := by
    rw [a.preimage_image_source_arcs]
    exact union_subset_union hAW₁ hBW₂
  let O : Set N := ((fun z => F (t, z)) '' (W₁ ∪ W₂)ᶜ)ᶜ
  have hO : IsOpen O :=
    ((hW₁.union hW₂).isClosed_compl.isCompact.image hF.continuous).isClosed.isOpen_compl
  have hCO : ∀ z ∈ A ∪ B, F (t, z) ∈ O := by
    intro z hz hbad
    obtain ⟨w, hw, heq⟩ := hbad
    exact hw (hpre ⟨z, hz, heq.symm⟩)
  have hOW : (fun z => F (t, z)) ⁻¹' O ⊆ W₁ ∪ W₂ := by
    intro z hz
    by_contra hn
    exact hz ⟨z, hn, rfl⟩
  let U : Set M := W₁ ∩ (fun z => F (t, z)) ⁻¹' O
  let V : Set M := W₂ ∩ (fun z => F (t, z)) ⁻¹' O
  have hUV : U ∪ V = (fun z => F (t, z)) ⁻¹' O := by
    apply subset_antisymm (union_subset inter_subset_right inter_subset_right)
    intro z hz
    rcases hOW hz with hzw | hzw
    · exact Or.inl ⟨hzw, hz⟩
    · exact Or.inr ⟨hzw, hz⟩
  refine ⟨O, hO, U, V, hW₁.inter (hO.preimage hF.continuous),
    hW₂.inter (hO.preimage hF.continuous),
    hWdisj.mono inter_subset_left inter_subset_left, hUV, ?_,
    hWi₁.mono inter_subset_left, hWi₂.mono inter_subset_left⟩
  intro s hs
  have hfa : a.firstArc s ∈ A := ⟨⟨s, hs⟩, rfl⟩
  have hgb : a.secondArc s ∈ B := ⟨⟨s, hs⟩, rfl⟩
  exact ⟨⟨hAW₁ hfa, hCO _ (Or.inl hfa)⟩, ⟨hBW₂ hgb, hCO _ (Or.inr hgb)⟩⟩

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
