import Wikipedia.SmoothSixDPoincare.NativeWhitneyArcPair
import Wikipedia.SmoothSixDPoincare.ConstructedCornerStrip
import Wikipedia.SmoothSixDPoincare.CornerStripData
import Wikipedia.SmoothSixDPoincare.StripPairOverlap
import Wikipedia.SmoothSixDPoincare.StripPatchRestriction
import Wikipedia.SmoothSixDPoincare.ConstructedCleanBigonBoundary
import Wikipedia.SmoothSixDPoincare.SmoothCleanBigonBoundary

/-!
# Two constructed native strips using the same two corner maps

Construct both arcs, both native corners, and both positive-width clean strips.
The second strip uses the first corner maps with their axes swapped, so the
two strips retain genuinely common corner germs. No arc, ambient chart, normal
field, corner map, or strip is an input hypothesis of this construction.

Shrinking controls every mutual intersection by one of the two actual corner
coordinate identifications. The strips then construct a compact clean embedded
immersive neighborhood of the entire cornered boundary. Filling the disk and
the required Whitney framing remain separate obligations.
-/

noncomputable section

open Set Function Module Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [TopologicalSpace P] [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P]
  [T2Space N] [CompactSpace N] [T2Space P] [CompactSpace P]

/-- Construct both native strips with exact contacts and the same two endpoint corner maps. -/
theorem exists_native_shared_corner_strip_pair {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hinjF : Injective F) (hinjG : Injective G)
    (hiF : ∀ x, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hiG : ∀ y, Injective (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y))
    (hdimD : 3 ≤ finrank ℝ D) (hdimZ : 3 ≤ finrank ℝ Z)
    (hcodim : finrank ℝ D + finrank ℝ Z = finrank ℝ E)
    (ht : ∀ x y, G y = F x → Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    {x₀ x₁ : N} {y₀ y₁ : P} (hcross₀ : G y₀ = F x₀) (hcross₁ : G y₁ = F x₁)
    (hxy : x₀ ≠ x₁) (γ : Path x₀ x₁) (η : Path y₀ y₁)
    {u₀ u₁ : D} {v₀ v₁ : Z} (hu₀ : u₀ ≠ 0) (hu₁ : u₁ ≠ 0)
    (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0) :
    ∃ f : C(ℝ, N), ∃ g : C(ℝ, P),
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f ∧ ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) ∞ g ∧
      f 0 = x₀ ∧ f 1 = x₁ ∧ g 0 = y₀ ∧ g 1 = y₁ ∧
      IsClosedEmbedding (fun t : unitInterval => f t) ∧
      IsClosedEmbedding (fun t : unitInterval => g t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) g t)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, F (f t) ∉ range G) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, G (g t) ∉ range F) ∧
      range (fun t : unitInterval => F (f t)) ∩ range (fun t : unitInterval => G (g t)) =
        {F x₀, F x₁} ∧
      ∃ c₀ : CleanCornerPatch (E := E) (range F) (range G)
          (fun t => F (NativeParametrization.centered (D := D) x₀ (t • u₀)))
          (fun t => G (NativeParametrization.centered (D := Z) y₀ (t • v₀))),
        ∃ c₁ : CleanCornerPatch (E := E) (range F) (range G)
            (fun t => F (NativeParametrization.centered (D := D) x₁ (t • u₁)))
            (fun t => G (NativeParametrization.centered (D := Z) y₁ (t • v₁))),
          ∃ k : CleanStripPatch (E := E) (range F) (range G) (F ∘ f) c₀.map c₁.map,
            ∃ l : CleanStripPatch (E := E) (range G) (range F) (G ∘ g)
                c₀.swap.map c₁.swap.map,
              Nonempty (StripNormalData (EuclideanSpace ℝ (Fin (finrank ℝ D - 1)))
                (EuclideanSpace ℝ (Fin (finrank ℝ Z))) (E := E) (range F) k.map) ∧
              Nonempty (StripNormalData (EuclideanSpace ℝ (Fin (finrank ℝ Z - 1)))
                (EuclideanSpace ℝ (Fin (finrank ℝ D))) (E := E) (range G) l.map) ∧
              (∀ p ∈ k.domain, ∀ q ∈ l.domain, k.map p = l.map q →
                p = q.swap ∨
                  StripCoordinates.reverse p = (StripCoordinates.reverse q).swap) ∧
              ∀ h : ℝ, 0 < h →
                Nonempty (CleanBigonBoundary (E := E)
                  (range F) (range G) (F ∘ f) (G ∘ g) k.map l.map h) ∧
                ∀ _e : M ≃ₕ SixSphere, Nonempty (SmoothCleanBigonBoundary (E := E)
                  (range F) (range G) (F ∘ f) (G ∘ g) k.map l.map h) := by
  obtain ⟨f, g, hf, hg, hf0, hf1, hg0, hg1, hfg0, hfg1, hgg0, hgg1,
      hembf, hembg, hif, hig, havoidf, havoidg, hinter⟩ :=
    exists_native_whitney_arc_pair hF hG hinjF hinjG hdimD hdimZ hcodim ht
      hcross₀ hcross₁ hxy γ η hu₀ hu₁ hv₀ hv₁
  have hembF := (hF.continuous.isClosedEmbedding hinjF).isEmbedding
  have hembG := (hG.continuous.isClosedEmbedding hinjG).isEmbedding
  have ht₀ := ht x₀ y₀ hcross₀
  have ht₁ := ht x₁ y₁ hcross₁
  obtain ⟨c₀⟩ := nonempty_cleanCornerPatch_of_native_crossing
    hF hG hembF hembG x₀ y₀ hcross₀ hcodim ht₀ hu₀ hv₀
  obtain ⟨c₁⟩ := nonempty_cleanCornerPatch_of_native_crossing
    hF hG hembF hembG x₁ y₁ hcross₁ hcodim ht₁ hu₁ hv₁
  have hinjf : InjOn f (Icc (0 : ℝ) 1) := by
    intro t ht s hs heq
    exact congrArg Subtype.val (hembf.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) heq)
  have hinjg : InjOn g (Icc (0 : ℝ) 1) := by
    intro t ht s hs heq
    exact congrArg Subtype.val (hembg.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) heq)
  obtain ⟨ε, hε, W, hW, hrect, k, hk, hinjk, _, hembk, hik, hcF, hcG, hcenter, hleft,
      hright, hnormalF⟩ :=
    exists_strip_along_arc_matching_native_corners hF hG hembF hiF hf hinjf hif hf0 hf1
      hcross₀ hcross₁ ht₀ ht₁ (finrank ℝ D - 1) (by omega) hcodim (by omega)
      hv₀ hv₁ hfg0 hfg1 havoidf c₀.smooth c₁.smooth c₀.open_domain c₁.open_domain
      c₀.contains_zero c₁.contains_zero c₀.axis_first c₁.axis_first c₀.axis_second c₁.axis_second
      (fun p hp => (c₀.sheets p hp).2) (fun p hp => (c₁.sheets p hp).2)
      isOpen_univ (fun _ _ => mem_univ _)
  let stripF : CleanStripPatch (E := E) (range F) (range G) (F ∘ f) c₀.map c₁.map := {
    width := ε, width_pos := hε, domain := W, open_domain := hW, contains_strip := hrect,
    map := k, smooth := hk, injective := hinjk, closed_embedding := hembk,
    derivative_injective := hik, first_sheet := hcF, second_sheet := hcG,
    center := hcenter, left_germ := hleft, right_germ := hright }
  let DF₀ : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x₀
  let DF₁ : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x₁
  let DG₀ : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y₀
  let DG₁ : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y₁
  have ht₀' : Surjective (DG₀.coprod DF₀) :=
    TransverseCoordinates.surjective_coprod_swap DF₀ DG₀ ht₀
  have ht₁' : Surjective (DG₁.coprod DF₁) :=
    TransverseCoordinates.surjective_coprod_swap DF₁ DG₁ ht₁
  have hcodim' : finrank ℝ Z + finrank ℝ D = finrank ℝ E := by omega
  obtain ⟨δ, hδ, V, hV, hrectV, l, hl, hinjl, _, hembl, hil, hcG', hcF',
      hcenter', hleft', hright', hnormalG⟩ :=
    exists_strip_along_arc_matching_native_corners hG hF hembG hiG hg hinjg hig hg0 hg1
      hcross₀.symm hcross₁.symm ht₀' ht₁' (finrank ℝ Z - 1) (by omega) hcodim' (by omega)
      hu₀ hu₁ hgg0 hgg1 havoidg c₀.swap.smooth c₁.swap.smooth
      c₀.swap.open_domain c₁.swap.open_domain
      c₀.swap.contains_zero c₁.swap.contains_zero c₀.swap.axis_first c₁.swap.axis_first
      c₀.swap.axis_second c₁.swap.axis_second
      (fun p hp => (c₀.swap.sheets p hp).2) (fun p hp => (c₁.swap.sheets p hp).2)
      isOpen_univ (fun _ _ => mem_univ _)
  let stripG : CleanStripPatch (E := E) (range G) (range F) (G ∘ g) c₀.swap.map c₁.swap.map := {
    width := δ, width_pos := hδ, domain := V, open_domain := hV, contains_strip := hrectV,
    map := l, smooth := hl, injective := hinjl, closed_embedding := hembl,
    derivative_injective := hil, first_sheet := hcG', second_sheet := hcF',
    center := hcenter', left_germ := hleft', right_germ := hright' }
  have hcoinc : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      (F ∘ f) t = (G ∘ g) s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1) := by
    intro t ht s hs heq
    have hmem : F (f t) ∈ ({F x₀, F x₁} : Set M) := by
      rw [← hinter]
      exact ⟨⟨⟨t, ht⟩, rfl⟩, ⟨⟨s, hs⟩, heq.symm⟩⟩
    change F (f t) = F x₀ ∨ F (f t) = F x₁ at hmem
    have h0 : (0 : ℝ) ∈ Icc 0 1 := ⟨le_rfl, zero_le_one⟩
    have h1 : (1 : ℝ) ∈ Icc 0 1 := ⟨zero_le_one, le_rfl⟩
    rcases hmem with hleft | hright
    · left
      constructor
      · exact hinjf ht h0 (hinjF (hleft.trans (congrArg F hf0).symm))
      · apply hinjg hs h0
        apply hinjG
        exact heq.symm.trans (hleft.trans ((congrArg G hg0).trans hcross₀).symm)
    · right
      constructor
      · exact hinjf ht h1 (hinjF (hright.trans (congrArg F hf1).symm))
      · apply hinjg hs h1
        apply hinjG
        exact heq.symm.trans (hright.trans ((congrArg G hg1).trans hcross₁).symm)
  obtain ⟨ε', hε', δ', hδ', U', V', hU', hV', hrectU', hrectV', hU'sub, hV'sub,
      hoverlap⟩ := exists_clean_strip_pair_neighborhoods c₀ c₁ stripF stripG hcoinc
  let k' := stripF.restrict hε' hU' hrectU' hU'sub
  let l' := stripG.restrict hδ' hV' hrectV' hV'sub
  have hoverlap' : ∀ p ∈ k'.domain, ∀ q ∈ l'.domain, k'.map p = l'.map q →
      p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap := hoverlap
  refine ⟨f, g, hf, hg, hf0, hf1, hg0, hg1, hembf, hembg, hif, hig, havoidf, havoidg,
    hinter, c₀, c₁, k', l', hnormalF, hnormalG, hoverlap', ?_⟩
  intro h hh
  obtain ⟨d⟩ := nonempty_cleanBigonBoundary hh c₀ c₁ k' l' hoverlap'
  exact ⟨⟨d⟩, fun e => nonempty_smoothCleanBigonBoundary e d⟩

end Wikipedia.SmoothSixDPoincare
