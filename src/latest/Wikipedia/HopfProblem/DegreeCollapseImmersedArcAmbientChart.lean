import Wikipedia.HopfProblem.DegreeCollapseEmbeddedPatchCoordinates
import Wikipedia.SmoothSixDPoincare.EmbeddedArcAmbientChart

/-!
# Ambient tubular coordinates along an embedded branch of an immersion

The ambient map is only assumed embedded on the selected source patch.
Actual source tubular coordinates and the patch's embedding topology
construct an ambient chart recognizing the full patch image by a zero
normal coordinate. The original joining arc and all its center germs remain
unchanged.
-/

noncomputable section

open Set Function Module Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open Wikipedia.SmoothSixDPoincare

variable {E M D G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace N] [ChartedSpace G N]

theorem exists_clean_patch_tubular_neighborhood {F : N → M} {L : Set N}
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    (hembF : IsEmbedding (fun x : L => F x))
    (c : PartialDiffeomorph 𝓘(ℝ, D) 𝓘(ℝ, G) D N ∞) (hcL : c.target ⊆ L)
    {K : Set D} (hK : IsCompact K) (hz : (0 : D) ∈ K)
    (hstar : StarConvex ℝ (0 : D) K) (hKc : K ⊆ c.source)
    (hiF : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F (c x)))
    (n : ℕ) (hcodim : finrank ℝ D + n = finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hFO : MapsTo (F ∘ c) K O) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
          (D × EuclideanSpace ℝ (Fin n)) M ∞,
        K ×ˢ closedBall 0 ε ⊆ Φ.source ∧
        Φ.source ⊆ c.source ×ˢ univ ∧ Φ.target ⊆ O ∧
        (∀ x, (x, 0) ∈ Φ.source → Φ (x, 0) = F (c x)) ∧
        (∀ q ∈ Φ.source, Φ q ∈ F '' L ↔ q.2 = 0) := by
  have hf : ContMDiffOn 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (F ∘ c) c.source :=
    hF.comp_contMDiffOn c.contMDiffOn_toFun
  have hemb := isEmbedding_patch_coordinates hembF c hcL
  have hi : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) (F ∘ c) x) := by
    intro x hx
    rw [mfderiv_comp x (hF.mdifferentiableAt (by simp))
      (c.mdifferentiableAt (by simp) (hKc hx))]
    exact (hiF x hx).comp (PartialChart.bijective_mfderiv c (hKc hx)).1
  obtain ⟨A, hA, hFA, hwindow⟩ := exists_patch_coordinate_window hembF c hcL
  obtain ⟨ε, hε, Φ, hprod, hsource, htarget, hzero, himage⟩ :=
    exists_clean_tubularNeighborhood_of_embedded_starConvex hf hK hz hstar c.open_source
      hKc hemb hi n hcodim (hO.inter hA) (fun x hx => ⟨hFO hx, hFA (hKc hx)⟩)
  refine ⟨ε, hε, Φ, hprod, hsource, fun _ hy => (htarget hy).1, hzero, ?_⟩
  intro q hq
  exact (hwindow (Φ q) (htarget (Φ.map_source' hq)).2).trans (himage q hq)

variable [FiniteDimensional ℝ G] [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N] [CompactSpace N]

theorem exists_clean_ambient_chart_along_patch_arc {F : N → M} {f : ℝ → N}
    {L U : Set N} (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    (hembF : IsEmbedding (fun x : L => F x))
    (hiF : ∀ x, Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, G) ∞ f)
    (hinjf : InjOn f (Icc (0 : ℝ) 1))
    (hif : ∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, G) f t))
    (hU : IsOpen U) (hUL : U ⊆ L) (hfU : MapsTo f (Icc (0 : ℝ) 1) U)
    (n m : ℕ) (hsheet : 1 + n = finrank ℝ G) (hcodim : finrank ℝ G + m = finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hfO : MapsTo (F ∘ f) (Icc (0 : ℝ) 1) O) :
    ∃ Φ : PartialDiffeomorph
        𝓘(ℝ, StripCoordinates.Space (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
        𝓘(ℝ, E)
        (StripCoordinates.Space (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) M ∞,
      MapsTo StripCoordinates.center (Icc (0 : ℝ) 1) Φ.source ∧ Φ.target ⊆ O ∧
      (∀ t, StripCoordinates.center t ∈ Φ.source → Φ (StripCoordinates.center t) = F (f t)) ∧
      (∀ q ∈ Φ.source, Φ q ∈ F '' L ↔ q.2 = 0) := by
  have hstar : StarConvex ℝ (0 : ℝ) (Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).starConvex (by simp)
  obtain ⟨a, ha, c, hprod, hzero, htargetc⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero
      hf isCompact_Icc (by simp) hstar hinjf hif n
      (by simpa only [finrank_self] using hsheet) hU hfU
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
    exists_clean_patch_tubular_neighborhood hF hembF c (htargetc.trans hUL)
      hK h0K hstarK hKc (fun x _ => hiF (c x)) m hdim hO hFO
  refine ⟨Φ, ?_, htarget, ?_, hclean⟩
  · intro t ht
    exact hΦprod ⟨⟨ht, rfl⟩, mem_closedBall_self hb.le⟩
  · intro t ht
    exact (hΦzero (t, 0) ht).trans (congrArg F (hzero t))

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
