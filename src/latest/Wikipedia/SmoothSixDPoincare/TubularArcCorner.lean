import Wikipedia.SmoothSixDPoincare.ParametrizedTransverseCorner
import Wikipedia.SmoothSixDPoincare.CenteredParametrization
import Wikipedia.SmoothSixDPoincare.CornerStripData

/-!
# Clean corners matching the full germs of existing tubular arcs

Recenter the actual inside-sheet tubular charts at the common endpoint.
The prescribed-parametrization crossing theorem constructs the corner with
exact axis values from the original arcs. Nonzero time scalings allow either
orientation at either endpoint. No prior prescribed arc-germ construction
or replacement of the original sheet images is required.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace Wikipedia.SmoothSixDPoincare

variable {E M D Z N P A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace N] [ChartedSpace D N]
  [TopologicalSpace P] [ChartedSpace Z P]

/-- Actual tubular arc coordinates construct a native corner with both full original arc germs. -/
theorem exists_clean_corner_of_tubular_arcs {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding F) (hembG : IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, ℝ × A) 𝓘(ℝ, D) (ℝ × A) N ∞)
    (d : PartialDiffeomorph 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z) (ℝ × B) P ∞)
    {f : ℝ → N} {g : ℝ → P} (hc : ∀ t, c (t, 0) = f t) (hd : ∀ t, d (t, 0) = g t)
    {t₀ : ℝ} (htc : (t₀, (0 : A)) ∈ c.source) (htd : (t₀, (0 : B)) ∈ d.source)
    (hxy : G (g t₀) = F (f t₀))
    (hdim : Module.finrank ℝ (ℝ × A) + Module.finrank ℝ (ℝ × B) = Module.finrank ℝ E)
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f t₀)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g t₀))))
    {σ τ : ℝ} (hσ : σ ≠ 0) (hτ : τ ≠ 0)
    {O : Set M} (hO : IsOpen O) (hxO : F (f t₀) ∈ O) :
    ∃ W : Set (ℝ × ℝ), IsOpen W ∧ (0 : ℝ × ℝ) ∈ W ∧ ∃ k : (ℝ × ℝ) → M,
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧ InjOn k W ∧ MapsTo k W O ∧
      k 0 = F (f t₀) ∧
      (∀ p ∈ W, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
      (∀ p ∈ W, (k p ∈ range F ↔ p.2 = 0) ∧ (k p ∈ range G ↔ p.1 = 0)) ∧
      (∀ s, (s, 0) ∈ W → k (s, 0) = F (f (t₀ + s * σ))) ∧
      (∀ t, (0, t) ∈ W → k (0, t) = G (g (t₀ + t * τ))) := by
  let c' := (NativeParametrization.translation (t₀, (0 : A))).toPartialDiffeomorph.trans c
  let d' := (NativeParametrization.translation (t₀, (0 : B))).toPartialDiffeomorph.trans d
  have hc0 : (0 : ℝ × A) ∈ c'.source := by
    refine ⟨mem_univ _, ?_⟩
    change 0 + (t₀, (0 : A)) ∈ c.source
    rw [zero_add]
    exact htc
  have hd0 : (0 : ℝ × B) ∈ d'.source := by
    refine ⟨mem_univ _, ?_⟩
    change 0 + (t₀, (0 : B)) ∈ d.source
    rw [zero_add]
    exact htd
  have hcx : c' 0 = f t₀ := by
    change c (0 + (t₀, (0 : A))) = f t₀
    rw [zero_add, hc]
  have hdy : d' 0 = g t₀ := by
    change d (0 + (t₀, (0 : B))) = g t₀
    rw [zero_add, hd]
  have hxy' : G (d' 0) = F (c' 0) := by rw [hcx, hdy]; exact hxy
  have ht' : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c' 0)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d' 0))) := by
    rw [hcx, hdy]
    exact ht
  have hxO' : F (c' 0) ∈ O := by rw [hcx]; exact hxO
  have hu : (σ, (0 : A)) ≠ 0 := fun he => hσ (congrArg Prod.fst he)
  have hv : (τ, (0 : B)) ≠ 0 := fun he => hτ (congrArg Prod.fst he)
  obtain ⟨W, hW, h0W, k, hk, hinj, hWO, hcenter, hi, hclean, hlo, hhi⟩ :=
    exists_native_clean_corner_of_parametrizations hF hG hembF hembG c' d' hc0 hd0
      hxy' hdim ht' hu hv hO hxO'
  refine ⟨W, hW, h0W, k, hk, hinj, hWO, hcenter.trans (congrArg F hcx),
    hi, hclean, ?_, ?_⟩
  · intro s hs
    rw [hlo s hs]
    apply congrArg F
    change c (s • (σ, (0 : A)) + (t₀, 0)) = f (t₀ + s * σ)
    have he : s • (σ, (0 : A)) + (t₀, 0) = (t₀ + s * σ, 0) := by
      simp [smul_eq_mul, add_comm]
    rw [he, hc]
  · intro t ht
    rw [hhi t ht]
    apply congrArg G
    change d (t • (τ, (0 : B)) + (t₀, 0)) = g (t₀ + t * τ)
    have he : t • (τ, (0 : B)) + (t₀, 0) = (t₀ + t * τ, 0) := by
      simp [smul_eq_mul, add_comm]
    rw [he, hd]

/-- Package the constructed corner for the shared-strip gluing API. -/
theorem nonempty_cleanCornerPatch_of_tubular_arcs {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : IsEmbedding F) (hembG : IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, ℝ × A) 𝓘(ℝ, D) (ℝ × A) N ∞)
    (d : PartialDiffeomorph 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z) (ℝ × B) P ∞)
    {f : ℝ → N} {g : ℝ → P} (hc : ∀ t, c (t, 0) = f t) (hd : ∀ t, d (t, 0) = g t)
    {t₀ : ℝ} (htc : (t₀, (0 : A)) ∈ c.source) (htd : (t₀, (0 : B)) ∈ d.source)
    (hxy : G (g t₀) = F (f t₀))
    (hdim : Module.finrank ℝ (ℝ × A) + Module.finrank ℝ (ℝ × B) = Module.finrank ℝ E)
    (ht : Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f t₀)).coprod
      (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g t₀))))
    {σ τ : ℝ} (hσ : σ ≠ 0) (hτ : τ ≠ 0) :
    Nonempty (CleanCornerPatch (E := E) (range F) (range G)
      (fun s => F (f (t₀ + s * σ))) (fun t => G (g (t₀ + t * τ)))) := by
  obtain ⟨W, hW, h0W, k, hk, hinj, _, _, hi, hsheets, hlo, hhi⟩ :=
    exists_clean_corner_of_tubular_arcs hF hG hembF hembG c d hc hd htc htd hxy
      hdim ht hσ hτ isOpen_univ (mem_univ _)
  exact ⟨{
    domain := W, open_domain := hW, contains_zero := h0W, map := k,
    smooth := hk, injective := hinj, derivative_injective := hi, sheets := hsheets,
    axis_first := hlo, axis_second := hhi }⟩

end Wikipedia.SmoothSixDPoincare
