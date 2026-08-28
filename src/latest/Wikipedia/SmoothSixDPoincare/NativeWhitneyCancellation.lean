import Wikipedia.SmoothSixDPoincare.CompatibleChartCancellation

/-!
# Native Whitney cancellation from the actual opposite corner signs

The compatible chart, its compactly supported motion, and the exact removal
of two intersections are all constructed. The input is the embedded native
bigon with its retained sheet data and the actual corner determinant signs.
No chart-compatible framing or ambient isotopy is assumed as an input.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}

/-- Opposite native corner determinants give exact, compactly supported sheet cancellation. -/
theorem exists_cancellation_of_opposite_corner_signs
    (tube : TubularBigon (E := E) S T a b k.map l.map h)
    (d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map)
    (e : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) T l.map)
    (hS : IsClosed S) (hT : IsClosed T)
    (hsign : tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ tube.chart.target ∧ ∃ A : ℝ × M → M,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
      (∀ y, A (0, y) = y) ∧
      (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = D y) ∧
      (∀ t y, y ∉ K → A (t, y) = y) ∧
      ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨c⟩ := tube.nonempty_compatibleChart_of_opposite_corner_signs d e hS hT hsign
  obtain ⟨K, hK, hKtarget, A, hA⟩ := c.exists_cancellation
  exact ⟨K, hK, hKtarget.trans c.target_subset, A, hA⟩

/-- For compact original sheet images, closedness is derived rather than assumed. -/
theorem exists_cancellation_of_compact_sheet_images
    {N P : Type*} [TopologicalSpace N] [CompactSpace N]
    [TopologicalSpace P] [CompactSpace P]
    {F : N → M} {G : P → M} (hF : Continuous F) (hG : Continuous G)
    {k : CleanStripPatch (E := E) (range F) (range G) a k₀ k₁}
    {l : CleanStripPatch (E := E) (range G) (range F) b l₀ l₁}
    (tube : TubularBigon (E := E) (range F) (range G) a b k.map l.map h)
    (d : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (range F) k.map)
    (e : StripNormalData Plane (EuclideanSpace ℝ (Fin 3)) (E := E) (range G) l.map)
    (hsign : tube.sheetPairDet d e 0 * tube.sheetPairDet d e 1 < 0) :
    ∃ K : Set M, IsCompact K ∧ K ⊆ tube.chart.target ∧ ∃ A : ℝ × M → M,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
      (∀ y, A (0, y) = y) ∧
      (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = D y) ∧
      (∀ t y, y ∉ K → A (t, y) = y) ∧
      ((fun y => A (1, y)) '' range F) ∩ range G = (range F ∩ range G) \ {a 0, a 1} :=
  tube.exists_cancellation_of_opposite_corner_signs d e
    (isCompact_range hF).isClosed (isCompact_range hG).isClosed hsign

end Wikipedia.SmoothSixDPoincare.TubularBigon
