import Wikipedia.SmoothSixDPoincare.MorseSignedWhitneyCorners
import Wikipedia.SmoothSixDPoincare.MorseBeltBigon
import Wikipedia.SmoothSixDPoincare.RankThreeRelativeCancellation

/-!
# Cancel an actual opposite-sign Morse-belt intersection pair

The original lower-level circle contractions construct the correct belt
complement contractions and the actual tubular bigon. Opposite signs of the
original finite Morse intersection set supply its Whitney corner signs.
The constructed native isotopy then removes exactly those two intersections.
No strips, bigon, framing, or corner-determinant sign are additional hypotheses.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {f : M → ℝ} {p : M} (D : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
/-- Opposite actual signs give exact native Whitney cancellation against the original Morse belt. -/
theorem exists_belt_whitney_cancellation_of_opposite_signs
    (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull : ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
      ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3)
    (g : C(Hemisphere.Sphere 2, D.UpperLevel)) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
    letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ g)
      (_hinj : Injective g)
      (_hi : ∀ x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) g x))
      (_ht : ∀ x y, NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, RegularLevel.Model E)
        g D.surgery.beltSphere x y)
      (x₀ x₁ : Hemisphere.Sphere 2),
      x₀ ∈ D.beltIntersectionPoints 2 g → x₁ ∈ D.beltIntersectionPoints 2 g →
      D.beltIntersectionSign 2 r g x₀ * D.beltIntersectionSign 2 r g x₁ = -1 →
      ∃ K : Set D.UpperLevel, IsCompact K ∧
        Disjoint K ((range g ∩ range D.surgery.beltSphere) \ {g x₀, g x₁}) ∧
        ∃ A : ℝ × D.UpperLevel → D.UpperLevel,
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, RegularLevel.Model E))
          𝓘(ℝ, RegularLevel.Model E) ∞ A ∧
        (∀ y, A (0, y) = y) ∧
        (∀ t, ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          D.UpperLevel D.UpperLevel ∞, ∀ y, A (t, y) = e y) ∧
        (∀ t y, y ∉ K → A (t, y) = y) ∧
        ((fun y => A (1, y)) '' range g) ∩ range D.surgery.beltSphere =
          (range g ∩ range D.surgery.beltSphere) \ {g x₀, g x₁} := by
  let _ := RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  intro hg hinj hi ht x₀ x₁ hx₀ hx₁ hsign
  obtain ⟨y₀, hy₀⟩ := hx₀
  obtain ⟨y₁, hy₁⟩ := hx₁
  have hne : x₀ ≠ x₁ := by
    intro heq
    rw [heq] at hsign
    have hs : ∀ s : SignType, s * s ≠ -1 := by decide
    exact hs _ hsign
  obtain ⟨a, b, ha₀, ha₁, _, _, k₀, k₁, l₀, l₁, k, l, ⟨d⟩, ⟨e⟩, htube⟩ :=
    D.exists_belt_tubular_strip_pair hf hdim hindex hnull g hg hinj hi
      (fun x y hxy => ht x y hxy) x₀ x₁ y₀ y₁ hy₀ hy₁ hne
  obtain ⟨tube⟩ := htube 1 (by norm_num)
  have hcenter₀ : g x₀ = d.chart (StripCoordinates.center 0) :=
    ha₀.symm.trans ((k.center 0 (by simp)).symm.trans (d.center 0))
  have hcenter₁ : g x₁ = d.chart (StripCoordinates.center 1) :=
    ha₁.symm.trans ((k.center 1 (by simp)).symm.trans (d.center 1))
  have hcorner := (D.opposite_beltIntersectionSigns_iff_Whitney_corners hf hdim hindex r g
    hg hinj hi ht tube d e x₀ x₁ hcenter₀ hcenter₁).mp hsign
  obtain ⟨K, hK, _, hdisjoint, A, hA, hA₀, hAt, hfix, hcancel⟩ :=
    tube.exists_rankThree_relative_cancellation d e (isCompact_range g.continuous).isClosed
      D.belt_isClosedEmbedding.isClosed_range hcorner
  rw [ha₀, ha₁] at hcancel hdisjoint
  exact ⟨K, hK, hdisjoint, A, hA, hA₀, hAt, hfix, hcancel⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
