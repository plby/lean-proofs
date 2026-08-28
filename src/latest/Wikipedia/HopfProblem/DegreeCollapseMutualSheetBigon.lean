import Wikipedia.SmoothSixDPoincare.SharedCornerStripPair
import Wikipedia.SmoothSixDPoincare.TwoSheetTubularBigon
import Wikipedia.HopfProblem.DegreeCollapseSmoothBigonFromLoops

/-!
# Constructed mutual-sheet bigons in simply connected six-manifolds

Two compact embedded three-dimensional sheets, their actual transverse
crossings, and paths in the sheets construct the complete clean tubular
bigon. Simple connectivity supplies its filling. No homotopy-sphere
identification, disk, strip chart, or Whitney framing is assumed.
-/

noncomputable section

open Set Function ContinuousMap Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.MutualSheets

open Wikipedia.SmoothSixDPoincare

variable {E M D N P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N]
  [TopologicalSpace P] [ChartedSpace D P] [IsManifold 𝓘(ℝ, D) ∞ P]
  [T2Space N] [CompactSpace N] [T2Space P] [CompactSpace P]

structure BigonData (F : N → M) (G : P → M) (x₀ x₁ : N) (y₀ y₁ : P) where
  leftArc : C(ℝ, N)
  rightArc : C(ℝ, P)
  smooth_left : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ leftArc
  smooth_right : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ rightArc
  left_zero : leftArc 0 = x₀
  left_one : leftArc 1 = x₁
  right_zero : rightArc 0 = y₀
  right_one : rightArc 1 = y₁
  lowerStart : (ℝ × ℝ) → M
  lowerEnd : (ℝ × ℝ) → M
  upperStart : (ℝ × ℝ) → M
  upperEnd : (ℝ × ℝ) → M
  lower : CleanStripPatch (E := E) (range F) (range G)
    (F ∘ leftArc) lowerStart lowerEnd
  upper : CleanStripPatch (E := E) (range G) (range F)
    (G ∘ rightArc) upperStart upperEnd
  lowerNormal : StripNormalData (EuclideanSpace ℝ (Fin 2))
    (EuclideanSpace ℝ (Fin 3)) (E := E) (range F) lower.map
  upperNormal : StripNormalData (EuclideanSpace ℝ (Fin 2))
    (EuclideanSpace ℝ (Fin 3)) (E := E) (range G) upper.map
  tube : TubularBigon (E := E) (range F) (range G)
    (F ∘ leftArc) (G ∘ rightArc) lower.map upper.map 1

theorem nonempty_bigonData [SimplyConnectedSpace M]
    (hdim : Module.finrank ℝ E = 6) (hsheet : Module.finrank ℝ D = 3)
    {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ G)
    (hinjF : Injective F) (hinjG : Injective G)
    (hiF : ∀ x, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hiG : ∀ y, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y))
    (ht : ∀ x y, G y = F x → Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod
        (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) G y)))
    {x₀ x₁ : N} {y₀ y₁ : P} (hc₀ : G y₀ = F x₀) (hc₁ : G y₁ = F x₁)
    (hne : x₀ ≠ x₁) (γ : Path x₀ x₁) (η : Path y₀ y₁)
    {u₀ u₁ v₀ v₁ : D} (hu₀ : u₀ ≠ 0) (hu₁ : u₁ ≠ 0)
    (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0) :
    Nonempty (BigonData (E := E) (D := D) F G x₀ x₁ y₀ y₁) := by
  have hd : 3 ≤ Module.finrank ℝ D := hsheet.ge
  have hcodim : Module.finrank ℝ D + Module.finrank ℝ D = Module.finrank ℝ E := by omega
  obtain ⟨f, g, hf, hg, hf0, hf1, hg0, hg1, _, _, _, _, _, _, _,
      c₀, c₁, k, l, hnF, hnG, _, hboundary⟩ :=
    exists_native_shared_corner_strip_pair hF hG hinjF hinjG hiF hiG hd hd hcodim ht
      hc₀ hc₁ hne γ η hu₀ hu₁ hv₀ hv₁
  obtain ⟨b⟩ := (hboundary 1 (by norm_num)).1
  obtain ⟨d⟩ := ImmersedSource.nonempty_smoothCleanBigonBoundary_of_simplyConnected b
  obtain ⟨tube⟩ := nonempty_tubularBigon_of_smoothCleanBoundary hF hG hdim hsheet.le d
  rw [hsheet] at hnF hnG
  obtain ⟨nF⟩ := hnF
  obtain ⟨nG⟩ := hnG
  exact ⟨{
    leftArc := f, rightArc := g, smooth_left := hf, smooth_right := hg
    left_zero := hf0, left_one := hf1, right_zero := hg0, right_one := hg1
    lowerStart := c₀.map, lowerEnd := c₁.map
    upperStart := c₀.swap.map, upperEnd := c₁.swap.map
    lower := k, upper := l, lowerNormal := nF, upperNormal := nG, tube := tube }⟩

end Wikipedia.HopfProblem.DegreeCollapse.MutualSheets
