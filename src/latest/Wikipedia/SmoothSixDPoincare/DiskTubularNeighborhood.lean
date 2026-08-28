import Wikipedia.SmoothSixDPoincare.NativeDiskCoordinates
import Wikipedia.SmoothSixDPoincare.CompactLocalDiffeomorph
import Mathlib.Topology.MetricSpace.Thickening

/-!
# A genuine tubular coordinate neighborhood of the closed disk

The retracted normal-frame displacement is a smooth local diffeomorphism along
the disk and is injective there. Compactness produces a single smooth partial
diffeomorphism whose source contains a positive-radius closed normal product.
Its zero section is exactly the original disk, including the boundary.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.DiskFraming

variable {D Z : Type*} [TopologicalSpace D] [NormedAddCommGroup Z]

/-- An open neighborhood of a compact zero section contains a uniform closed normal product. -/
theorem exists_pos_prod_closedBall_subset {K : Set D} {U : Set (D × Z)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ×ˢ {(0 : Z)} ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ K ×ˢ Metric.closedBall (0 : Z) ε ⊆ U := by
  obtain ⟨A, B, -, hB, hKA, hzeroB, hAB⟩ :=
    generalized_tube_lemma hK (isCompact_singleton (x := (0 : Z))) hU hKU
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hB.mem_nhds (hzeroB (mem_singleton (0 : Z))))
  refine ⟨ε, hε, ?_⟩
  rintro ⟨x, z⟩ ⟨hx, hz⟩
  exact hAB ⟨hKA hx, hball hz⟩

end Wikipedia.SmoothSixDPoincare.DiskFraming

namespace Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding.SmoothRetraction

variable {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  {e : NativeEuclideanEmbedding E M} (r : e.SmoothRetraction) {n : ℕ}

/-- The actual framed displacement is one smooth coordinate chart
near the compact embedded locus. -/
theorem exists_diskTubularNeighborhood {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f) {K V : Set D}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) (hinj : InjOn f K)
    (hi : ∀ x ∈ K, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    {A : D → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin e.ambientDimension)}
    (hA : ContDiffOn ℝ ∞ A V)
    (hAi : ∀ x ∈ K, Injective (A x))
    (hAr : ∀ x ∈ K, (A x).range = e.diskNormalSpace f x) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
        (D × EuclideanSpace ℝ (Fin n)) M ∞,
      K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Φ.source ∧
      Φ.source ⊆ r.diskCoordinateDomain f A V ∧
      (Φ : D × EuclideanSpace ℝ (Fin n) → M) = r.diskCoordinates f A := by
  have hzeroInj : InjOn (r.diskCoordinates f A) (K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))}) := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩ ⟨y, w⟩ ⟨hy, hw⟩ hxy
    have hv0 : v = 0 := hv
    have hw0 : w = 0 := hw
    subst v
    subst w
    rw [r.diskCoordinates_zero, r.diskCoordinates_zero] at hxy
    exact Prod.ext (hinj hx hy hxy) rfl
  have hlocal : ∀ p ∈ K ×ˢ {(0 : EuclideanSpace ℝ (Fin n))},
      IsLocalDiffeomorphAt 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞
        (r.diskCoordinates f A) p := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    exact r.isLocalDiffeomorphAt_diskCoordinates_zero hf hV hA (hKV hx)
      (hi x hx) (hAi x hx) (hAr x hx)
  apply exists_partialDiffeomorph_near_compact (hK.prod isCompact_singleton)
    hzeroInj hlocal (r.isOpen_diskCoordinateDomain hf hV hA)
  rintro ⟨x, v⟩ ⟨hx, hv⟩
  have hv0 : v = 0 := hv
  subst v
  exact r.zero_mem_diskCoordinateDomain f A (hKV hx)

end Wikipedia.SmoothSixDPoincare.NativeEuclideanEmbedding.SmoothRetraction

namespace Wikipedia.SmoothSixDPoincare

variable {E M D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]

/-- The embedding, retraction, frame, positive radius, and actual smooth disk-neighborhood chart
are all constructed from the original compact manifold and its embedded immersive disk. -/
theorem exists_tubularNeighborhood_in_open_of_embedded_closedBall {f : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hinj : InjOn f (Metric.closedBall (0 : D) 1))
    (hi : ∀ x ∈ Metric.closedBall (0 : D) 1,
      Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (n : ℕ) (hcodim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hfO : MapsTo f (Metric.closedBall (0 : D) 1) O) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E)
          (D × EuclideanSpace ℝ (Fin n)) M ∞,
        Metric.closedBall (0 : D) 1 ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
        (∀ x ∈ Metric.closedBall (0 : D) 1, Φ (x, 0) = f x) ∧ Φ.target ⊆ O := by
  let : Nonempty M := ⟨f 0⟩
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  obtain ⟨V, hV, hKV, A, hA, hframe⟩ :=
    e.exists_smooth_normalFrame_near_closedBall hf hi n hcodim
  obtain ⟨Φ, hzero, -, hΦ⟩ := r.exists_diskTubularNeighborhood hf
    (isCompact_closedBall 0 1) hV hKV hinj hi hA
    (fun x hx => (hframe x (hKV hx)).1) (fun x hx => (hframe x (hKV hx)).2)
  let W := Φ.source ∩ Φ ⁻¹' O
  have hW : IsOpen W :=
    Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source hO
  have hWloc : IsLocalDiffeomorphOn 𝓘(ℝ, D × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, E) ∞ Φ W :=
    fun p => ⟨Φ, p.property.1, fun _ _ => rfl⟩
  let Ψ := partialDiffeomorphOfInjectiveLocal hW
    (Φ.toPartialEquiv.injOn.mono inter_subset_left) hWloc
  have hzeroΨ : Metric.closedBall (0 : D) 1 ×ˢ {(0 : EuclideanSpace ℝ (Fin n))} ⊆ Ψ.source := by
    rintro ⟨x, v⟩ ⟨hx, hv⟩
    have hv0 : v = 0 := hv
    subst v
    refine ⟨hzero ⟨hx, rfl⟩, ?_⟩
    change Φ (x, 0) ∈ O
    rw [hΦ, r.diskCoordinates_zero]
    exact hfO hx
  obtain ⟨ε, hε, hprod⟩ := DiskFraming.exists_pos_prod_closedBall_subset
    (isCompact_closedBall 0 1) Ψ.open_source hzeroΨ
  refine ⟨ε, hε, Ψ, hprod, ?_, ?_⟩
  · intro x _
    change Φ (x, 0) = f x
    rw [hΦ, r.diskCoordinates_zero]
  · change Φ '' W ⊆ O
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2

end Wikipedia.SmoothSixDPoincare
