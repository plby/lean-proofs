import Wikipedia.SmoothSixDPoincare.RegularLevelTransverseCoordinates
import Wikipedia.SmoothSixDPoincare.RegularBandFlow
import Wikipedia.SmoothSixDPoincare.DiskTubularNeighborhood

/-!
# A constructed smooth collar of an actual compact regular level

The transverse field, Euclidean embedding, smooth retraction, and compact
inverse neighborhood are all constructed. The zero section is the original
level inclusion. The original height has unit derivative in the transverse
direction there; straightening that height throughout the collar is a
separate step.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.RegularLevel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)

include hf hreg in
/-- Construct a smooth native field with unit height derivative on the entire regular level. -/
theorem exists_unitHeightField :
    ∃ V : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      ∀ x : {x : M // f x = b}, mvfderiv 𝓘(ℝ, E) f (x : M) (V x) = 1 := by
  have hband : ∀ x, f x ∈ Icc b b → x ∉ ManifoldMorse.criticalPoints E f :=
    fun x hx => hreg x (le_antisymm hx.2 hx.1)
  obtain ⟨φ, W, -, -, hW, hφ, V, hV, hheight⟩ :=
    FlowConstruction.exists_regularBandField hf hband
  refine ⟨V, hV, ?_⟩
  intro x
  exact (hheight x).trans (hφ (hW (by rw [x.property]; exact ⟨le_rfl, le_rfl⟩)))

/-- Construct one smooth collar chart containing a uniform full product around the actual level. -/
theorem exists_transverseCollar [Nonempty {x : M // f x = b}] :
    letI := chartedSpace hf hreg
    ∃ ε : ℝ, 0 < ε ∧
      ∃ Φ : PartialDiffeomorph (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E)
          ({x : M // f x = b} × ℝ) M ∞,
        (univ : Set {x : M // f x = b}) ×ˢ closedBall (0 : ℝ) ε ⊆ Φ.source ∧
        (∀ x : {x : M // f x = b}, Φ (x, 0) = x) ∧
        ∀ x : {x : M // f x = b}, HasDerivAt (fun t : ℝ => f (Φ (x, t))) 1 0 := by
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  let _ : CompactSpace {x : M // f x = b} :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Nonempty M := Nonempty.map (fun x : {x : M // f x = b} => (x : M)) inferInstance
  obtain ⟨e⟩ := nonempty_nativeEuclideanEmbedding (E := E) (M := M)
  obtain ⟨r⟩ := e.nonempty_smoothRetraction
  obtain ⟨V, hV, hunit⟩ := exists_unitHeightField hf hreg
  let K : Set ({x : M // f x = b} × ℝ) := univ ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := isCompact_univ.prod isCompact_singleton
  have hinj : InjOn (transverseCoordinates r V) K := by
    rintro ⟨x, s⟩ ⟨-, hs⟩ ⟨y, t⟩ ⟨-, ht⟩ hxy
    have hs0 : s = 0 := hs
    have ht0 : t = 0 := ht
    subst s
    subst t
    rw [transverseCoordinates_zero r V x, transverseCoordinates_zero r V y] at hxy
    exact Prod.ext (Subtype.ext hxy) rfl
  have hloc : ∀ z ∈ K,
      IsLocalDiffeomorphAt (𝓘(ℝ, Model E).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (transverseCoordinates r V) z := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact isLocalDiffeomorphAt_transverseCoordinates_zero r V hf hreg hV x (hunit x)
  have hKD : K ⊆ transverseCoordinateDomain r V := by
    rintro ⟨x, t⟩ ⟨-, ht⟩
    have ht0 : t = 0 := ht
    subst t
    exact zero_mem_transverseCoordinateDomain r V x
  obtain ⟨Φ, hKΦ, -, heq⟩ := exists_partialDiffeomorph_near_compact hK hinj hloc
    (isOpen_transverseCoordinateDomain r V hf hreg hV) hKD
  obtain ⟨ε, hε, hsource⟩ := DiskFraming.exists_pos_prod_closedBall_subset
    isCompact_univ Φ.open_source hKΦ
  refine ⟨ε, hε, Φ, hsource, ?_, ?_⟩
  · intro x
    exact (congrFun heq (x, 0)).trans (transverseCoordinates_zero r V x)
  · intro x
    have hh : (fun t : ℝ => f (Φ (x, t))) =
        fun t : ℝ => f (transverseCoordinates r V (x, t)) :=
      funext (fun t => congrArg f (congrFun heq (x, t)))
    rw [hh]
    exact hasDerivAt_height_transverseCoordinates_zero r V hf hreg hV x (hunit x)

end Wikipedia.SmoothSixDPoincare.RegularLevel
