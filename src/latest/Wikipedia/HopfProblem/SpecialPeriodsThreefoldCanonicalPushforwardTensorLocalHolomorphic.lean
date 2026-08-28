import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardTensorLocalFiber

/-!
# Native holomorphicity of local tensor contraction

The proof compares the actual paired tensor chart `(i,j)` with the
original chart `i`. The coefficient is unchanged in these two charts.
Thus both maps are holomorphic over the preimage of the chosen base
chart; no continuity of a discontinuously selected preferred scalar
coordinate is assumed.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.TensorLocal

open HolomorphicCharacterBundle

variable {M N : Type} {ι κ : Type*} [TopologicalSpace M] [TopologicalSpace N]
  (A : TransitionData M ι) (B : TransitionData N κ)
  {E H F K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [TopologicalSpace K] [ChartedSpace K N]
  (I : ModelWithCorners ℂ E H) (J : ModelWithCorners ℂ F K)
  (f : M → N) (hf : ContMDiff I J ω f)
  [A.IsHolomorphic I] [B.IsHolomorphic J]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- Holomorphicity is checked in the actual original tensor and factor charts. -/
theorem unTensorMap_holomorphicAt (j : κ)
    (p : (tensor A (pullback B f hf.continuous)).core.TotalSpace)
    (hp : f p.proj ∈ B.baseSet j) :
    ContMDiffAt (I.prod I₁) (I.prod I₁) ω (unTensorMap A B f hf.continuous j) p := by
  let : (pullback B f hf.continuous).IsHolomorphic I :=
    pullback_isHolomorphic B f hf.continuous I J hf
  let : ContMDiffVectorBundle ω ℂ (tensor A (pullback B f hf.continuous)).core.Fiber I :=
    (tensor A (pullback B f hf.continuous)).core_contMDiffVectorBundle I
  let i := A.indexAt p.proj
  have hs : p ∈ ((tensor A (pullback B f hf.continuous)).core.localTriv (i, j)).source :=
    ⟨A.mem_baseSet_at p.proj, hp⟩
  have ht : unTensorMap A B f hf.continuous j p ∈ (A.core.localTriv i).source :=
    A.mem_baseSet_at p.proj
  apply ((A.core.localTriv i).contMDiffAt_iff ht).mpr
  refine ⟨Bundle.contMDiffAt_proj (tensor A (pullback B f hf.continuous)).core.Fiber, ?_⟩
  have hchart : ContMDiffAt (I.prod I₁) (I.prod I₁) ω
      ((tensor A (pullback B f hf.continuous)).core.localTriv (i, j)) p :=
    ((tensor A (pullback B f hf.continuous)).core.localTriv (i, j)).contMDiffOn.contMDiffAt
      (((tensor A (pullback B f hf.continuous)).core.localTriv (i, j)).open_source.mem_nhds hs)
  have he : (fun q : (tensor A (pullback B f hf.continuous)).core.TotalSpace =>
      (A.core.localTriv i (unTensorMap A B f hf.continuous j q)).2) =
      fun q => ((tensor A (pullback B f hf.continuous)).core.localTriv (i, j) q).2 :=
    funext (unTensorMap_localTriv A B f hf.continuous i j)
  rw [he]
  exact hchart.snd

/-- Tensoring with the original unit frame is holomorphic in the inverse native charts. -/
theorem tensorMap_holomorphicAt (j : κ) (p : A.core.TotalSpace)
    (hp : f p.proj ∈ B.baseSet j) :
    ContMDiffAt (I.prod I₁) (I.prod I₁) ω (tensorMap A B f hf.continuous j) p := by
  let : (pullback B f hf.continuous).IsHolomorphic I :=
    pullback_isHolomorphic B f hf.continuous I J hf
  let : ContMDiffVectorBundle ω ℂ (tensor A (pullback B f hf.continuous)).core.Fiber I :=
    (tensor A (pullback B f hf.continuous)).core_contMDiffVectorBundle I
  let i := A.indexAt p.proj
  have hs : p ∈ (A.core.localTriv i).source := A.mem_baseSet_at p.proj
  have ht : tensorMap A B f hf.continuous j p ∈
      ((tensor A (pullback B f hf.continuous)).core.localTriv (i, j)).source :=
    ⟨A.mem_baseSet_at p.proj, hp⟩
  apply (((tensor A (pullback B f hf.continuous)).core.localTriv (i, j)).contMDiffAt_iff ht).mpr
  refine ⟨Bundle.contMDiffAt_proj A.core.Fiber, ?_⟩
  have hchart : ContMDiffAt (I.prod I₁) (I.prod I₁) ω (A.core.localTriv i) p :=
    (A.core.localTriv i).contMDiffOn.contMDiffAt ((A.core.localTriv i).open_source.mem_nhds hs)
  have he : (fun q : A.core.TotalSpace =>
      ((tensor A (pullback B f hf.continuous)).core.localTriv (i, j)
        (tensorMap A B f hf.continuous j q)).2) = fun q => (A.core.localTriv i q).2 :=
    funext (tensorMap_localTriv A B f hf.continuous i j)
  rw [he]
  exact hchart.snd

theorem unTensorMap_holomorphicOn (j : κ) :
    ContMDiffOn (I.prod I₁) (I.prod I₁) ω (unTensorMap A B f hf.continuous j)
      {p | f p.proj ∈ B.baseSet j} :=
  fun p hp => (unTensorMap_holomorphicAt A B I J f hf j p hp).contMDiffWithinAt

theorem tensorMap_holomorphicOn (j : κ) :
    ContMDiffOn (I.prod I₁) (I.prod I₁) ω (tensorMap A B f hf.continuous j)
      {p | f p.proj ∈ B.baseSet j} :=
  fun p hp => (tensorMap_holomorphicAt A B I J f hf j p hp).contMDiffWithinAt

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.TensorLocal
