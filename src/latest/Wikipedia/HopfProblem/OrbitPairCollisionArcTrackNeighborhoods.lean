import Wikipedia.HopfProblem.OrbitPairCollisionArcNeighborhoods
import Wikipedia.HopfProblem.OrbitPairSaturatedTwoBranchNeighborhood
import Wikipedia.HopfProblem.OrbitPairNativeFamilyTrack
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Saturated branch neighborhoods in the full time-retaining track

The track `(t,x) ↦ (t,F(t,x))` is proper when the spatial source is compact:
its projection to time is the proper product projection. The exact slice
fibers along the two arcs determine their complete track fibers because
equality of track values forces equality of times.

The resulting open target neighborhood controls all source times. Its
entire preimage splits into two disjoint injective immersive branches,
contained in any prescribed time band about the selected collision pair.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.NativeFamily

theorem track_isProperMap {M N : Type*}
    [TopologicalSpace M] [CompactSpace M] [TopologicalSpace N] [T2Space N]
    {F : ℝ × M → N} (hF : Continuous F) : IsProperMap (track F) := by
  apply isProperMap_of_comp_of_t2 (continuous_fst.prodMk hF)
    (continuous_fst : Continuous (Prod.fst : ℝ × N → ℝ))
  exact isProperMap_fst_of_compactSpace

variable {E G H K M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [PathConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace K N] [T2Space N]

theorem CollisionArcPair.preimage_image_track_arcs
    {F : ℝ × M → N} {t : ℝ} {x₀ x₁ y₀ y₁ : M}
    (a : CollisionArcPair (I := I) (J := J) F t x₀ x₁ y₀ y₁) :
    track F ⁻¹' (track F ''
        (range (fun s : unitInterval => (t, a.firstArc s)) ∪
          range (fun s : unitInterval => (t, a.secondArc s)))) =
      range (fun s : unitInterval => (t, a.firstArc s)) ∪
        range (fun s : unitInterval => (t, a.secondArc s)) := by
  ext q
  constructor
  · rintro ⟨w, (⟨s, rfl⟩ | ⟨s, rfl⟩), heq⟩
    · have hqt : q.1 = t := (congrArg (fun z : ℝ × N => z.1) heq).symm
      have hvalue : F (t, q.2) = F (t, a.firstArc s) := by
        have hh := (congrArg (fun z : ℝ × N => z.2) heq).symm
        change F q = F (t, a.firstArc s) at hh
        simpa only [← hqt] using hh
      rcases (a.first_fiber s s.property q.2).mp hvalue with hz | ⟨-, hz⟩ | ⟨-, hz⟩
      · exact Or.inl ⟨s, Prod.ext hqt.symm hz.symm⟩
      · exact Or.inr ⟨0, Prod.ext hqt.symm (a.second_zero.trans hz.symm)⟩
      · exact Or.inr ⟨1, Prod.ext hqt.symm (a.second_one.trans hz.symm)⟩
    · have hqt : q.1 = t := (congrArg (fun z : ℝ × N => z.1) heq).symm
      have hvalue : F (t, q.2) = F (t, a.secondArc s) := by
        have hh := (congrArg (fun z : ℝ × N => z.2) heq).symm
        change F q = F (t, a.secondArc s) at hh
        simpa only [← hqt] using hh
      rcases (a.second_fiber s s.property q.2).mp hvalue with hz | ⟨-, hz⟩ | ⟨-, hz⟩
      · exact Or.inr ⟨s, Prod.ext hqt.symm hz.symm⟩
      · exact Or.inl ⟨0, Prod.ext hqt.symm (a.first_zero.trans hz.symm)⟩
      · exact Or.inl ⟨1, Prod.ext hqt.symm (a.first_one.trans hz.symm)⟩
  · intro hq
    exact ⟨q, hq, rfl⟩

variable [FiniteDimensional ℝ G] [J.Boundaryless] [IsManifold J ∞ N] [CompactSpace M]

theorem CollisionArcPair.exists_saturated_track_neighborhoods
    {F : ℝ × M → N} {t : ℝ} {x₀ x₁ y₀ y₁ : M}
    (a : CollisionArcPair (I := I) (J := J) F t x₀ x₁ y₀ y₁)
    (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    (hi : ∀ s x, Injective (mfderiv I J (fun z => F (s, z)) x))
    {c d : ℝ} (ht : t ∈ Ioo c d)
    {O₀ : Set (ℝ × N)} (hO₀ : IsOpen O₀)
    (hcurveO₀ : ∀ s ∈ Icc (0 : ℝ) 1,
      track F (t, a.firstArc s) ∈ O₀ ∧ track F (t, a.secondArc s) ∈ O₀) :
    ∃ O : Set (ℝ × N), IsOpen O ∧ O ⊆ O₀ ∧ ∃ U V : Set (ℝ × M),
      IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = track F ⁻¹' O ∧
      (∀ s ∈ Icc (0 : ℝ) 1, (t, a.firstArc s) ∈ U ∧ (t, a.secondArc s) ∈ V) ∧
      U ⊆ Ioo c d ×ˢ univ ∧ V ⊆ Ioo c d ×ˢ univ ∧
      InjOn (track F) U ∧ InjOn (track F) V ∧
      (∀ q ∈ track F ⁻¹' O,
        Injective (mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (track F) q)) := by
  let A : Set (ℝ × M) := range (fun s : unitInterval => (t, a.firstArc s))
  let B : Set (ℝ × M) := range (fun s : unitInterval => (t, a.secondArc s))
  have hA : IsCompact A := isCompact_range
    (continuous_const.prodMk (a.firstArc.continuous.comp continuous_subtype_val))
  have hB : IsCompact B := isCompact_range
    (continuous_const.prodMk (a.secondArc.continuous.comp continuous_subtype_val))
  have hdisj : Disjoint A B := by
    apply disjoint_left.mpr
    rintro q ⟨s, rfl⟩ ⟨u, heq⟩
    exact disjoint_left.mp a.source_disjoint ⟨s, rfl⟩
      ⟨u, congrArg (fun z : ℝ × M => z.2) heq⟩
  have hAi : InjOn (track F) A := by
    rintro _ ⟨s, rfl⟩ _ ⟨u, rfl⟩ heq
    have hsu := a.target_first_embedding.injective (congrArg (fun z : ℝ × N => z.2) heq)
    exact congrArg (fun v : unitInterval => (t, a.firstArc v)) hsu
  have hBi : InjOn (track F) B := by
    rintro _ ⟨s, rfl⟩ _ ⟨u, rfl⟩ heq
    have hsu := a.target_second_embedding.injective (congrArg (fun z : ℝ × N => z.2) heq)
    exact congrArg (fun v : unitInterval => (t, a.secondArc v)) hsu
  have hsmooth : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) ∞ (track F) :=
    contMDiff_fst.prodMk hF
  have hderiv : ∀ q : ℝ × M,
      Injective (mfderiv (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod J) (track F) q) :=
    fun q => injective_mfderiv_track q (hF.mdifferentiableAt (by simp)) (hi q.1 q.2)
  have hAW : A ∪ B ⊆ Ioo c d ×ˢ (univ : Set M) := by
    rintro q (⟨s, rfl⟩ | ⟨s, rfl⟩) <;> exact ⟨ht, mem_univ _⟩
  have hAO : MapsTo (track F) (A ∪ B) O₀ := by
    rintro q (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · exact (hcurveO₀ s s.property).1
    · exact (hcurveO₀ s s.property).2
  obtain ⟨O, hO, hOO₀, U, V, hU, hV, hUVdisj, hUV, hAU, hBV,
      hUW, hVW, hiU, hiV⟩ := NativeImmersion.exists_saturated_two_branch_neighborhood
    hsmooth (track_isProperMap hF.continuous).isClosedMap hA hB hdisj hAi hBi
    (fun q _ => hderiv q) a.preimage_image_track_arcs (isOpen_Ioo.prod isOpen_univ) hAW hO₀ hAO
  refine ⟨O, hO, hOO₀, U, V, hU, hV, hUVdisj, hUV, ?_, hUW, hVW, hiU, hiV,
    fun q _ => hderiv q⟩
  intro s hs
  exact ⟨hAU ⟨⟨s, hs⟩, rfl⟩, hBV ⟨⟨s, hs⟩, rfl⟩⟩

end Wikipedia.HopfProblem.OrbitPair.NativeFamily
