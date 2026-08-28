import Wikipedia.HopfProblem.DegreeCollapseThreeBeltWhitneyCorners
import Wikipedia.HopfProblem.DegreeCollapseNativeThreeBeltBigon
import Wikipedia.HopfProblem.DegreeCollapseThreeSheetRelativeCancellation

/-!
# Remove an actual opposite-sign three-belt intersection pair

The original lower-level circle contractions construct the actual clean
tubular bigon. The signs of the original sphere/belt intersections give the
required native Whitney corner condition and hence the compatible framing.
The constructed compactly supported ambient isotopy removes precisely those
two intersections and fixes every other crossing germ. No disk, strip,
framing, corner determinant, or isotopy is supplied as geometric input.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}

theorem exists_three_belt_whitney_cancellation_of_opposite_signs
    (D : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 7)
    [Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1)]
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 3)
    (hnull : ∀ γ : C(Hemisphere.Sphere 1, D.LowerLevel),
      ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 4)
    (g : C(Hemisphere.Sphere 3, D.UpperLevel))
    (hgood : IsNativeTransverseBeltSphere D hf 3 3 g)
    (x₀ x₁ : Hemisphere.Sphere 3)
    (hx₀ : x₀ ∈ D.beltIntersectionPoints 3 g) (hx₁ : x₁ ∈ D.beltIntersectionPoints 3 g)
    (hsign : D.beltIntersectionSign 3 r g x₀ * D.beltIntersectionSign 3 r g x₁ = -1) :
    letI := RegularLevel.chartedSpace hf D.upper_regular
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
  obtain ⟨hg, hinj, hi, ht⟩ := hgood
  obtain ⟨y₀, hy₀⟩ := hx₀
  obtain ⟨y₁, hy₁⟩ := hx₁
  have hne : x₀ ≠ x₁ := by
    intro heq
    rw [heq] at hsign
    have hs : ∀ s : SignType, s * s ≠ -1 := by decide
    exact hs _ hsign
  obtain ⟨α, β, _, _, hα₀, hα₁, _, _, k₀, k₁, l₀, l₁, k, l, ⟨d⟩, ⟨e⟩, htube⟩ :=
    exists_native_three_belt_tubular_strip_pair D hf hdim hindex hnull g
      ⟨hg, hinj, hi, ht⟩ x₀ x₁ y₀ y₁ hy₀ hy₁ hne
  obtain ⟨tube⟩ := htube 1 (by norm_num)
  have ha₀ : (g ∘ α) 0 = g x₀ := congrArg g hα₀
  have ha₁ : (g ∘ α) 1 = g x₁ := congrArg g hα₁
  have hcenter₀ : g x₀ = d.chart (StripCoordinates.center 0) :=
    ha₀.symm.trans ((k.center 0 (by simp)).symm.trans (d.center 0))
  have hcenter₁ : g x₁ = d.chart (StripCoordinates.center 1) :=
    ha₁.symm.trans ((k.center 1 (by simp)).symm.trans (d.center 1))
  have hcorner := (opposite_three_beltIntersectionSigns_iff_Whitney_corners D hf hindex r g
    hg hinj hi ht tube d e x₀ x₁ hcenter₀ hcenter₁).mp hsign
  obtain ⟨K, hK, _, hdisjoint, A, hA, hA₀, hAt, hfix, hcancel⟩ :=
    exists_three_sheet_relative_cancellation tube d e (isCompact_range g.continuous).isClosed
      D.belt_isClosedEmbedding.isClosed_range hcorner
  rw [ha₀, ha₁] at hcancel hdisjoint
  exact ⟨K, hK, hdisjoint, A, hA, hA₀, hAt, hfix, hcancel⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
