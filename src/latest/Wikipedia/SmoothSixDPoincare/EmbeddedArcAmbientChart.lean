import Wikipedia.SmoothSixDPoincare.CleanEmbeddedSheetNeighborhood
import Wikipedia.SmoothSixDPoincare.StripCoordinateBlend

/-!
# A constructed clean ambient chart along a specified embedded sheet arc

The inside-sheet tubular chart uses its globally exact zero section. The
ambient chart therefore agrees with the supplied arc at every center point
in its source, not just on the closed unit interval. In particular it retains
the actual prescribed endpoint germs needed by the corner-strip assembly.
-/

noncomputable section

open Set Function Module Metric Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

variable {E M G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N]
  [T2Space N] [CompactSpace N]

/-- Construct a clean ambient chart along the given arc, retaining all its center germs. -/
theorem exists_clean_ambient_chart_along_embedded_arc {F : N → M} {f : ℝ → N}
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F) (hembF : IsEmbedding F)
    (hiF : ∀ x, Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, G) ∞ f) (hinjf : InjOn f (Icc (0 : ℝ) 1))
    (hif : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, G) f t))
    (n m : ℕ) (hsheet : 1 + n = finrank ℝ G) (hcodim : finrank ℝ G + m = finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hfO : MapsTo (F ∘ f) (Icc (0 : ℝ) 1) O) :
    ∃ Φ : PartialDiffeomorph
        𝓘(ℝ, StripCoordinates.Space (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
        𝓘(ℝ, E)
        (StripCoordinates.Space (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) M ∞,
      MapsTo StripCoordinates.center (Icc (0 : ℝ) 1) Φ.source ∧ Φ.target ⊆ O ∧
      (∀ t, StripCoordinates.center t ∈ Φ.source → Φ (StripCoordinates.center t) = F (f t)) ∧
      (∀ q ∈ Φ.source, Φ q ∈ range F ↔ q.2 = 0) := by
  have hstar : StarConvex ℝ (0 : ℝ) (Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).starConvex (by simp)
  obtain ⟨a, ha, c, hprod, hzero, _⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero
      hf isCompact_Icc (by simp) hstar hinjf hif n
      (by simpa only [finrank_self] using hsheet) isOpen_univ (fun _ _ => mem_univ _)
  let K := Icc (0 : ℝ) 1 ×ˢ {(0 : EuclideanSpace ℝ (Fin n))}
  have hK : IsCompact K := isCompact_Icc.prod isCompact_singleton
  have h0K : (0 : ℝ × EuclideanSpace ℝ (Fin n)) ∈ K := by simp [K]
  have hstarK : StarConvex ℝ (0 : ℝ × EuclideanSpace ℝ (Fin n)) K :=
    hstar.prod (starConvex_singleton _)
  have hKc : K ⊆ c.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hprod ⟨ht, mem_closedBall_self ha.le⟩
  have hFO : MapsTo (F ∘ c) K O := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change F (c (t, 0)) ∈ O
    rw [hzero]
    exact hfO ht
  have hdim : finrank ℝ (ℝ × EuclideanSpace ℝ (Fin n)) + m = finrank ℝ E := by
    simpa only [finrank_prod, finrank_self, finrank_euclideanSpace_fin, hsheet] using hcodim
  obtain ⟨b, hb, Φ, hΦprod, _, htarget, hΦzero, hclean⟩ :=
    exists_clean_embedded_sheet_neighborhood hF hembF c hK h0K hstarK hKc
      (fun x _ => hiF (c x)) m hdim hO hFO
  refine ⟨Φ, ?_, htarget, ?_, hclean⟩
  · intro t ht
    exact hΦprod ⟨⟨ht, rfl⟩, mem_closedBall_self hb.le⟩
  · intro t ht
    exact (hΦzero (t, 0) ht).trans (congrArg F (hzero t))

end Wikipedia.SmoothSixDPoincare
