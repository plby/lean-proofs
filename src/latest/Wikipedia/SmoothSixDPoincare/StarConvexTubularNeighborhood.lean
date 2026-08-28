import Wikipedia.SmoothSixDPoincare.DiskTubularNeighborhood
import Wikipedia.SmoothSixDPoincare.StarConvexProjectionFrame

/-!
# Genuine tubular charts for compact star-convex regions

The source region may have corners. It is a subset of a vector space, not
a boundaryless manifold in disguise. A smooth ambient immersion, injective
on that region, gives a constructed intrinsic normal frame and an actual
smooth partial diffeomorphism on an open neighborhood of a positive-radius
normal product. No framing or tubular chart is an input hypothesis.

The frame is not asserted to agree with a prescribed boundary frame.
-/

noncomputable section

open Set Function Module
open scoped Manifold ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding

variable {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] (e : NativeEuclideanEmbedding E M)

/-- Radial transport constructs the intrinsic normal frame over a compact star-convex region. -/
theorem exists_smooth_normalFrame_near_starConvex {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D}
    (hK : IsCompact K) (hz : (0 : D) ∈ K) (hstar : StarConvex ℝ (0 : D) K)
    (hi : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : finrank ℝ D + n = finrank ℝ E) :
    ∃ V : Set D, IsOpen V ∧ K ⊆ V ∧
      ∃ A : D → EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin e.ambientDimension),
        ContDiffOn ℝ ∞ A V ∧
          ∀ x ∈ K, Injective (A x) ∧ (A x).range = e.diskNormalSpace f x := by
  obtain ⟨U, hU, hKU, hsP, hP⟩ := e.exists_open_diskNormalProjection hf hi
  have hidem : ∀ x ∈ K, IsIdempotentElem (e.diskNormalProjection f x) := by
    intro x hx
    rw [hP x (hKU hx)]
    exact (e.diskNormalSpace f x).isIdempotentElem_starProjection
  obtain ⟨V, hV, hKV, A, hA, hAi⟩ :=
    DiskFraming.exists_smooth_frame_near_starConvex hK hstar hU hKU
      (e.diskNormalProjection f) hidem hsP
  have hr : (e.diskNormalProjection f 0).range = e.diskNormalSpace f 0 := by
    rw [hP 0 (hKU hz), Submodule.range_starProjection]
  have hdim : finrank ℝ (e.diskNormalSpace f 0) = n := by
    have h := e.finrank_diskTangent_add_normal hf (hi 0 hz)
    omega
  have hcenter : finrank ℝ (e.diskNormalProjection f 0).range = n :=
    (congrArg (fun S : Submodule ℝ (EuclideanSpace ℝ (Fin e.ambientDimension)) =>
      finrank ℝ S) hr).trans hdim
  let φ : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      (e.diskNormalProjection f 0).range :=
    ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin.trans hcenter.symm)
  refine ⟨V, hV, hKV, fun x => (A x).comp φ.toContinuousLinearMap,
    hA.clm_comp contDiffOn_const, ?_⟩
  intro x hx
  refine ⟨((hAi x hx).1).comp φ.injective, ?_⟩
  calc
    ((A x).comp φ.toContinuousLinearMap).range = (A x).range :=
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr φ.surjective)
    _ = (e.diskNormalProjection f x).range := (hAi x hx).2
    _ = e.diskNormalSpace f x := by rw [hP x (hKU hx), Submodule.range_starProjection]

end Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding

namespace Wikipedia.SmoothSixDPoincare

variable {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]

/-- A compact star-convex embedded immersive region has a genuine positive-radius tubular chart,
with its entire target inside any prescribed open neighborhood of its image. -/
theorem exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D}
    (hK : IsCompact K) (hz : (0 : D) ∈ K) (hstar : StarConvex ℝ (0 : D) K)
    (hinj : InjOn f K)
    (hi : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : finrank ℝ D + n = finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hfO : MapsTo f K O) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
          (D × EuclideanSpace ℝ (Fin n)) M ∞,
        K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
        (∀ x, Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  let : Nonempty M := ⟨f 0⟩
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  obtain ⟨V, hV, hKV, A, hA, hframe⟩ :=
    e.exists_smooth_normalFrame_near_starConvex hf hK hz hstar hi n hcodim
  obtain ⟨Φ, hzero, -, hΦ⟩ := r.exists_diskTubularNeighborhood hf
    hK hV hKV hinj hi hA (fun x hx => (hframe x hx).1) (fun x hx => (hframe x hx).2)
  let W := Φ.source ∩ Φ ⁻¹' O
  have hW : IsOpen W :=
    Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source hO
  have hWloc : IsLocalDiffeomorphOn 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ Φ W :=
    fun p => ⟨Φ, p.property.1, fun _ _ => rfl⟩
  let Ψ := partialDiffeomorphOfInjectiveLocal hW
    (Φ.toPartialEquiv.injOn.mono inter_subset_left) hWloc
  have hzeroΨ : K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Ψ.source := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    refine ⟨hzero ⟨hx, rfl⟩, ?_⟩
    change Φ (x, 0) ∈ O
    rw [hΦ, r.diskCoordinates_zero]
    exact hfO hx
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset hK Ψ.open_source hzeroΨ
  refine ⟨ε, hε, Ψ, hprod, ?_, ?_⟩
  · intro x
    change Φ (x, 0) = f x
    rw [hΦ, r.diskCoordinates_zero]
  · change Φ '' W ⊆ O
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2

/-- The zero-section identity restricted to the specified compact source region. -/
theorem exists_tubularNeighborhood_in_open_of_embedded_starConvex {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K : Set D}
    (hK : IsCompact K) (hz : (0 : D) ∈ K) (hstar : StarConvex ℝ (0 : D) K)
    (hinj : InjOn f K)
    (hi : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : finrank ℝ D + n = finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hfO : MapsTo f K O) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
          (D × EuclideanSpace ℝ (Fin n)) M ∞,
        K ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
        (∀ x ∈ K, Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  obtain ⟨ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero
      hf hK hz hstar hinj hi n hcodim hO hfO
  exact ⟨ε, hε, Φ, hsource, fun x _ => hzero x, htarget⟩

end Wikipedia.SmoothSixDPoincare
