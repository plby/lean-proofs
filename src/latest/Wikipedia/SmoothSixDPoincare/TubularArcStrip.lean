import Wikipedia.SmoothSixDPoincare.ParametrizedCornerStrip
import Wikipedia.SmoothSixDPoincare.CornerStripData

/-!
# Clean strips matching shared corners of actual tubular arcs

The opposite arc's tubular chart supplies the vertical corner coordinates.
At the second endpoint it is translated and its time direction reversed.
The resulting strip retains the original arc and the two shared corner maps,
with all full-sheet contact and native normal-derivative data.
-/

noncomputable section

open Set Function Filter Module Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z B N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [TopologicalSpace P] [ChartedSpace Z P]
  [T2Space N] [CompactSpace N] [CompactSpace P]

/-- Assemble a clean strip from the actual arc and the shared arc-adapted corners. -/
theorem exists_cleanStripPatch_of_tubular_arc_corners
    {F : N → M} {G : P → M} {f : ℝ → N} {g : ℝ → P}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding F) (hiF : ∀ x, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f) (hinjf : InjOn f (Icc (0 : ℝ) 1))
    (hif : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t))
    (d : PartialDiffeomorph 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z) (ℝ × B) P ∞)
    (hd : ∀ t, d (t, 0) = g t)
    (hd₀ : ((0 : ℝ), (0 : B)) ∈ d.source) (hd₁ : ((1 : ℝ), (0 : B)) ∈ d.source)
    (hcross₀ : G (g 0) = F (f 0)) (hcross₁ : G (g 1) = F (f 1))
    (ht₀ : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 0))))
    (ht₁ : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 1))))
    (n : ℕ) (hsheet : 1 + n = finrank ℝ D)
    (hcodim : finrank ℝ D + finrank ℝ Z = finrank ℝ E) (hdimZ : 2 ≤ finrank ℝ Z)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, F (f t) ∉ range G)
    (c₀ : CleanCornerPatch (E := E) (range F) (range G) (F ∘ f) (G ∘ g))
    (c₁ : CleanCornerPatch (E := E) (range F) (range G)
      (fun t => F (f (1 - t))) (fun t => G (g (1 - t))))
    {O : Set M} (hO : IsOpen O) (hfO : MapsTo (F ∘ f) (Icc (0 : ℝ) 1) O) :
    ∃ k : CleanStripPatch (E := E) (range F) (range G) (F ∘ f) c₀.map c₁.map,
      Nonempty (StripNormalData (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin (finrank ℝ Z))) (E := E) (range F) k.map) ∧
      MapsTo k.map k.domain O := by
  let d' := (NativeParametrization.translation ((1 : ℝ), (0 : B))).toPartialDiffeomorph.trans d
  have hd'₀ : (0 : ℝ × B) ∈ d'.source := by
    refine ⟨mem_univ _, ?_⟩
    change 0 + ((1 : ℝ), (0 : B)) ∈ d.source
    rw [zero_add]
    exact hd₁
  have hd0 : d (0 : ℝ × B) = g 0 := hd 0
  have hd1 : d' (0 : ℝ × B) = g 1 := by
    change d (0 + ((1 : ℝ), (0 : B))) = g 1
    rw [zero_add, hd]
  have hcross₀' : G (d 0) = F (f 0) := by rw [hd0]; exact hcross₀
  have hcross₁' : G (d' 0) = F (f 1) := by rw [hd1]; exact hcross₁
  have ht₀' : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))) := by rw [hd0]; exact ht₀
  have ht₁' : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d' 0))) := by rw [hd1]; exact ht₁
  have hv₀ : ((1 : ℝ), (0 : B)) ≠ 0 := fun he => one_ne_zero (congrArg Prod.fst he)
  have hv₁ : ((-1 : ℝ), (0 : B)) ≠ 0 := by
    intro he
    have he' : (-1 : ℝ) = 0 := congrArg Prod.fst he
    norm_num at he'
  have hleft₀ : (fun t : ℝ => c₀.map (t, 0)) =ᶠ[𝓝 0] (F ∘ f) := by
    have haxis := (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (c₀.open_domain.mem_nhds c₀.contains_zero)
    filter_upwards [haxis] with t ht
    exact c₀.axis_first t ht
  have hleft₁ : (fun t : ℝ => c₁.map (t, 0)) =ᶠ[𝓝 0] fun t => F (f (1 - t)) := by
    have haxis := (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (c₁.open_domain.mem_nhds c₁.contains_zero)
    filter_upwards [haxis] with t ht
    exact c₁.axis_first t ht
  have hcurve₀ (s : ℝ) : d (s • ((1 : ℝ), (0 : B))) = g s := by
    simpa only [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero] using hd s
  have hcurve₁ (s : ℝ) : d' (s • ((-1 : ℝ), (0 : B))) = g (1 - s) := by
    change d (s • ((-1 : ℝ), (0 : B)) + (1, 0)) = g (1 - s)
    have he : s • ((-1 : ℝ), (0 : B)) + (1, 0) = (1 - s, 0) := by
      simp [smul_eq_mul, sub_eq_add_neg, add_comm]
    rw [he, hd]
  obtain ⟨ε, hε, W, hW, hrect, k, hk, hinj, hmap, hemb, hi, hfirst, hsecond,
      hcenter, hleft, hright, hnormal⟩ :=
    exists_strip_along_arc_matching_parametrized_corners hF hG hembF hiF hf hinjf hif
      d d' hd₀ hd'₀ hcross₀' hcross₁' ht₀' ht₁' n hsheet hcodim hdimZ hv₀ hv₁ havoid
      c₀.smooth c₁.smooth c₀.open_domain c₁.open_domain c₀.contains_zero c₁.contains_zero
      hleft₀ hleft₁
      (fun s hs => (c₀.axis_second s hs).trans (congrArg G (hcurve₀ s).symm))
      (fun s hs => (c₁.axis_second s hs).trans (congrArg G (hcurve₁ s).symm))
      (fun p hp => (c₀.sheets p hp).2) (fun p hp => (c₁.sheets p hp).2) hO hfO
  let strip : CleanStripPatch (E := E) (range F) (range G) (F ∘ f) c₀.map c₁.map := {
    width := ε, width_pos := hε, domain := W, open_domain := hW, contains_strip := hrect,
    map := k, smooth := hk, injective := hinj, closed_embedding := hemb,
    derivative_injective := hi, first_sheet := hfirst, second_sheet := hsecond,
    center := hcenter, left_germ := hleft, right_germ := hright }
  exact ⟨strip, hnormal, hmap⟩

end Wikipedia.SmoothSixDPoincare
