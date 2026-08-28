import Wikipedia.HopfProblem.DegreeCollapseNativeLevelBasinTransport

/-!
# Transporting an actual embedded immersed map to another regular level

When every image point reaches the other level, the native partial flow
diffeomorphism transports the whole map. Both its exact inverse relation
and its original-orbit relation are retained for later basin comparisons.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M G H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H} [TopologicalSpace X] [ChartedSpace H X] [IsManifold J ∞ X]

theorem AdaptedSurgeryWindows.exists_embedded_level_transport
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (γ : C(X, {x : M // f x = a})) (x₀ : X) :
    let _ := RegularLevel.chartedSpace hf ha
    let _ := RegularLevel.chartedSpace hf hb
    ContMDiff J 𝓘(ℝ, RegularLevel.Model E) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) γ z)) →
    (∀ z, (γ z).val ∈ FlowCancellation.levelBasin S.flow f b) →
    ∃ D : PartialDiffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        {x : M // f x = a} {x : M // f x = b} ∞,
      D.source = {x | x.val ∈ FlowCancellation.levelBasin S.flow f b} ∧
      D.target = {y | y.val ∈ FlowCancellation.levelBasin S.flow f a} ∧
      ∃ Γ : C(X, {x : M // f x = b}),
        ContMDiff J 𝓘(ℝ, RegularLevel.Model E) ∞ Γ ∧ Injective Γ ∧
        (∀ z, Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) Γ z)) ∧
        (∀ z, D (γ z) = Γ z) ∧ (∀ z, D.symm (Γ z) = γ z) ∧
        ∀ z, ∃ t : ℝ, S.flow t (γ z).val = (Γ z).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  let _ := RegularLevel.isManifold hf ha
  let _ := RegularLevel.isManifold hf hb
  change ContMDiff J 𝓘(ℝ, RegularLevel.Model E) ∞ γ → Injective γ →
    (∀ z, Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) γ z)) →
    (∀ z, (γ z).val ∈ FlowCancellation.levelBasin S.flow f b) → _
  intro hγ hγi hγd hreach
  obtain ⟨t, ht⟩ := hreach x₀
  let zb : {x : M // f x = b} := ⟨S.flow t (γ x₀).val, ht⟩
  obtain ⟨D, hsource, htarget, horbit⟩ :=
    S.exists_native_level_basin_transport hf ha hb (γ x₀) zb
  have hmaps (z : X) : γ z ∈ D.source := hsource.symm ▸ hreach z
  have hDγ : ContMDiff J 𝓘(ℝ, RegularLevel.Model E) ∞ (D ∘ γ) := by
    intro z
    exact (D.contMDiffOn_toFun.contMDiffAt (D.open_source.mem_nhds (hmaps z))).comp z
      hγ.contMDiffAt
  let Γ : C(X, {x : M // f x = b}) := ⟨D ∘ γ, hDγ.continuous⟩
  have hΓi : Injective Γ := by
    intro x y hxy
    exact hγi (D.toPartialEquiv.injOn (hmaps x) (hmaps y) hxy)
  have hΓd : ∀ z, Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) Γ z) := by
    intro z
    change Injective (mfderiv J 𝓘(ℝ, RegularLevel.Model E) (D ∘ γ) z)
    rw [mfderiv_comp z (D.mdifferentiableAt (by simp) (hmaps z))
      (hγ.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv D (hmaps z)).1.comp (hγd z)
  refine ⟨D, hsource, htarget, Γ, hDγ, hΓi, hΓd, fun _ => rfl, ?_, ?_⟩
  · intro z
    exact D.left_inv' (hmaps z)
  · intro z
    exact horbit (γ z) (hmaps z)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
