import Wikipedia.SmoothSixDPoincare.TwoDimensionalConnectingArc
import Wikipedia.SmoothSixDPoincare.NormedStarConvexTubularNeighborhood

/-!
# Constructed tubular coordinates along connecting arcs

From a continuous path and a finite obstacle set, construct a smooth embedded
immersive connecting arc and genuine tubular coordinates along its entire
closed parameter interval, including both endpoints, in dimension at least two.
The chart target avoids
all obstacle points except the two selected endpoints. These coordinates can
be used inside a sheet when joining the local Whitney corners.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {G N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N]
  [T2Space N] [CompactSpace N]

/-- The arc, its endpoint neighborhoods, and its whole positive-radius tubular chart are
constructed without assuming an initial smooth curve, frame, or neighborhood chart. -/
theorem exists_tubular_connecting_arc_avoiding_finite_with_global_zero
    {x y : N} (γ : Path x y) (hxy : x ≠ y)
    (hdim : 2 ≤ Module.finrank ℝ G) (n : ℕ) (hcodim : 1 + n = Module.finrank ℝ G)
    {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, G) ∞ f ∧ f 0 = x ∧ f 1 = y ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, G) f t)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ S) ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, G)
            (ℝ × EuclideanSpace ℝ (Fin n)) N ∞,
          Icc (0 : ℝ) 1 ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
          (∀ t, Φ (t, 0) = f t) ∧ Φ.target ⊆ (S \ {x, y})ᶜ := by
  obtain ⟨f, hf, hf0, hf1, hemb, hi, havoid⟩ :=
    exists_embedded_connecting_arc_avoiding_finite_dim_two (J := 𝓘(ℝ, G)) γ hxy hdim hS
  have hinj : InjOn f (Icc (0 : ℝ) 1) := by
    intro t ht s hs hts
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) hts)
  have hO : IsOpen (S \ {x, y})ᶜ := (hS.subset sdiff_subset).isClosed.isOpen_compl
  have hfO : MapsTo f (Icc (0 : ℝ) 1) (S \ {x, y})ᶜ := by
    intro t ht
    change f t ∉ S \ {x, y}
    by_cases ht0 : t = 0
    · rw [ht0, hf0]
      exact fun hx => hx.2 (by simp)
    by_cases ht1 : t = 1
    · rw [ht1, hf1]
      exact fun hy => hy.2 (by simp)
    have hti : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    exact fun hs => havoid t hti hs.1
  have hstar : StarConvex ℝ (0 : ℝ) (Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).starConvex (by simp)
  obtain ⟨ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf
      isCompact_Icc (by simp) hstar hinj hi n (by simpa only [Module.finrank_self] using hcodim)
      hO hfO
  exact ⟨f, hf, hf0, hf1, hemb, hi, havoid, ε, hε, Φ, hsource, hzero, htarget⟩

/-- The interval-restricted API follows from the stronger globally exact zero section. -/
theorem exists_tubular_connecting_arc_avoiding_finite {x y : N} (γ : Path x y) (hxy : x ≠ y)
    (hdim : 2 ≤ Module.finrank ℝ G) (n : ℕ) (hcodim : 1 + n = Module.finrank ℝ G)
    {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, G) ∞ f ∧ f 0 = x ∧ f 1 = y ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, G) f t)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ S) ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∃ Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, G)
            (ℝ × EuclideanSpace ℝ (Fin n)) N ∞,
          Icc (0 : ℝ) 1 ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
          (∀ t ∈ Icc (0 : ℝ) 1, Φ (t, 0) = f t) ∧ Φ.target ⊆ (S \ {x, y})ᶜ := by
  obtain ⟨f, hf, hf0, hf1, hemb, hi, havoid, ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_tubular_connecting_arc_avoiding_finite_with_global_zero γ hxy hdim n hcodim hS
  exact ⟨f, hf, hf0, hf1, hemb, hi, havoid, ε, hε, Φ, hsource, fun t _ => hzero t, htarget⟩

end Wikipedia.SmoothSixDPoincare
