import Wikipedia.SmoothSixDPoincare.SharedCornerStripPair
import Wikipedia.SmoothSixDPoincare.TwoSheetTubularBigon

/-!
# A fully constructed tubular bigon from original native three-dimensional sheets

The original homotopy equivalence, compact transverse sheet embeddings, two
crossings, joining paths, and nonzero endpoint directions construct the arcs,
corners, strips, clean closed neighborhood, smooth filling, and tubular chart.
No disk, boundary neighborhood, chart, or extension map is an input.

The sheets share their three-dimensional normed model. The resulting tube
does not yet carry a proved Whitney framing or cancel an actual handle pair.
-/

noncomputable section

open Set Function ContinuousMap Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E M D N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [TopologicalSpace P] [ChartedSpace D P] [IsManifold 𝓘(ℝ, D) ∞ P]
  [T2Space N] [CompactSpace N] [T2Space P] [CompactSpace P]

/-- Construct the full tubular bigon and its actual native boundary data
in a homotopy six-sphere. -/
theorem exists_native_two_sheet_tubular_bigon (e : M ≃ₕ SixSphere)
    (hdim : Module.finrank ℝ E = 6) (hsheet : Module.finrank ℝ D = 3)
    {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ G)
    (hinjF : Injective F) (hinjG : Injective G)
    (hiF : ∀ x, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hiG : ∀ y, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y))
    (ht : ∀ x y, G y = F x → Surjective ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
      (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y)))
    {x₀ x₁ : N} {y₀ y₁ : P} (hcross₀ : G y₀ = F x₀) (hcross₁ : G y₁ = F x₁)
    (hxy : x₀ ≠ x₁) (γ : Path x₀ x₁) (η : Path y₀ y₁)
    {u₀ u₁ v₀ v₁ : D} (hu₀ : u₀ ≠ 0) (hu₁ : u₁ ≠ 0)
    (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0) {h : ℝ} (hh : 0 < h) :
    ∃ f : C(ℝ, N), ∃ g : C(ℝ, P),
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f ∧ ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ g ∧
      f 0 = x₀ ∧ f 1 = x₁ ∧ g 0 = y₀ ∧ g 1 = y₁ ∧
      IsClosedEmbedding (fun t : unitInterval => f t) ∧
      IsClosedEmbedding (fun t : unitInterval => g t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) g t)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, F (f t) ∉ range G) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, G (g t) ∉ range F) ∧
      range (fun t : unitInterval => F (f t)) ∩ range (fun t : unitInterval => G (g t)) =
        {F x₀, F x₁} ∧
      ∃ c₀ : CleanCornerPatch (E := E) (range F) (range G)
          (fun t => F (NativeParametrization.centered (D := D) x₀ (t • u₀)))
          (fun t => G (NativeParametrization.centered (D := D) y₀ (t • v₀))),
        ∃ c₁ : CleanCornerPatch (E := E) (range F) (range G)
            (fun t => F (NativeParametrization.centered (D := D) x₁ (t • u₁)))
            (fun t => G (NativeParametrization.centered (D := D) y₁ (t • v₁))),
          ∃ k : CleanStripPatch (E := E) (range F) (range G) (F ∘ f) c₀.map c₁.map,
            ∃ l : CleanStripPatch (E := E) (range G) (range F) (G ∘ g)
                c₀.swap.map c₁.swap.map,
              Nonempty (StripNormalData (EuclideanSpace ℝ (Fin 2))
                (EuclideanSpace ℝ (Fin 3)) (E := E) (range F) k.map) ∧
              Nonempty (StripNormalData (EuclideanSpace ℝ (Fin 2))
                (EuclideanSpace ℝ (Fin 3)) (E := E) (range G) l.map) ∧
              Nonempty (TubularBigon (E := E) (range F) (range G)
                (F ∘ f) (G ∘ g) k.map l.map h) := by
  have hdimD : 3 ≤ Module.finrank ℝ D := hsheet.ge
  have hcodim : Module.finrank ℝ D + Module.finrank ℝ D = Module.finrank ℝ E := by omega
  obtain ⟨f, g, hf, hg, hf0, hf1, hg0, hg1, hembf, hembg, hif, hig, havoidf, havoidg,
      hinter, c₀, c₁, k, l, hnormalF, hnormalG, _, hboundary⟩ :=
    exists_native_shared_corner_strip_pair hF hG hinjF hinjG hiF hiG hdimD hdimD hcodim ht
      hcross₀ hcross₁ hxy γ η hu₀ hu₁ hv₀ hv₁
  obtain ⟨d⟩ := (hboundary h hh).2 e
  have htube := nonempty_tubularBigon_of_smoothCleanBoundary hF hG hdim hsheet.le d
  refine ⟨f, g, hf, hg, hf0, hf1, hg0, hg1, hembf, hembg, hif, hig, havoidf, havoidg,
    hinter, c₀, c₁, k, l, ?_, ?_, htube⟩
  · rw [hsheet] at hnormalF
    exact hnormalF
  · rw [hsheet] at hnormalG
    exact hnormalG

end Wikipedia.SmoothSixDPoincare
