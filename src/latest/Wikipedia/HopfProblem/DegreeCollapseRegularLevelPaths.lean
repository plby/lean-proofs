import Wikipedia.HopfProblem.DegreeCollapseMinimumLevelPaths

/-!
# Paths in a regular level from the actual endpoint-obstruction dimensions

An ambient path is perturbed away from the full closed obstruction to
crossing the level. The native flow cylinder projects it to that level
with both endpoints fixed. No level connectedness is assumed.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.joinedIn_regular_level_of_endpoint_dimensions
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ criticalPoints E f) {d : ℕ}
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p → Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E)
    {x y : M} (hxa : f x = a) (hya : f y = a) (γ : Path x y) :
    JoinedIn {z : M | f z = a} x y := by
  let _ := S.finite.fintype
  let K := EndpointBasinIndex S a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := endpointBasinIndex_countable S a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_endpoint_obstruction_global_images hf a hhigh hlow
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞
      (fun z : K × V => g z.1 z.2) := contMDiff_discrete_family g hg
  let G : C(K × V, M) := ⟨fun z => g z.1 z.2, hG.continuous⟩
  have hrange : range G = (FlowCancellation.levelBasin S.flow f a)ᶜ := by
    rw [levelBasin_compl_eq_endpoint_obstruction S hf hreg, hcover]
    exact range_discrete_family g
  have hclosed : IsClosed (range G) := by
    rw [hrange, levelBasin_compl_eq_endpoint_obstruction S hf hreg]
    exact isClosed_endpoint_obstruction S hf a
  have hdim' : 1 + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim
  have hnot (z : M) (hz : f z = a) : z ∉ range G := by
    rw [hrange, mem_compl_iff, not_not]
    exact ⟨0, by simpa only [S.flow.map_zero_apply] using hz⟩
  obtain ⟨η, -, havoid⟩ := exists_smooth_path_avoiding_closed_image γ G hG hclosed hdim'
    (hnot x hxa) (hnot y hya)
  have hcross (t : unitInterval) : η t ∈ FlowCancellation.levelBasin S.flow f a := by
    have hh := havoid t
    simpa only [hrange, mem_compl_iff, not_not] using hh
  let _ := RegularLevel.chartedSpace hf hreg
  let xL : {z : M // f z = a} := ⟨x, hxa⟩
  let yL : {z : M // f z = a} := ⟨y, hya⟩
  obtain ⟨Φ, hsource, htarget, hformula, -⟩ := FlowCancellation.exists_native_level_flow_cylinder
    hf hreg S.smooth S.flow S.integral (fun z hz => S.descent z (hreg z hz)) xL
  have hcont : Continuous (fun t : unitInterval => Φ.symm (η t)) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous η.continuous
      (fun t => htarget.symm ▸ hcross t)
  have hinverse (z : {w : M // f w = a}) : Φ.symm z.val = (z, 0) := by
    have hs : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
    have he : Φ (z, 0) = z.val := by rw [hformula, S.flow.map_zero_apply]
    have hi : Φ.symm (Φ (z, 0)) = (z, 0) := Φ.left_inv' hs
    rwa [he] at hi
  let ξ : Path x y := {
    toFun := fun t => (Φ.symm (η t)).1.val
    continuous_toFun := continuous_subtype_val.comp (continuous_fst.comp hcont)
    source' := by
      rw [η.source]
      exact congrArg (fun z : {w : M // f w = a} × ℝ => z.1.val) (hinverse xL)
    target' := by
      rw [η.target]
      exact congrArg (fun z : {w : M // f w = a} × ℝ => z.1.val) (hinverse yL) }
  exact ⟨ξ, fun t => (Φ.symm (η t)).1.property⟩

theorem AdaptedSurgeryWindows.pathConnectedSpace_regular_level_of_endpoint_dimensions
    [PathConnectedSpace M]
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ criticalPoints E f) {d : ℕ}
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p → Module.finrank ℝ E - nativeMorseIndex E f p ≤ d)
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) (z₀ : {z : M // f z = a}) :
    PathConnectedSpace {z : M // f z = a} where
  nonempty := ⟨z₀⟩
  joined x y :=
    (S.joinedIn_regular_level_of_endpoint_dimensions hf hreg hhigh hlow hdim
      x.property y.property (PathConnectedSpace.somePath x.val y.val)).joined_subtype

theorem AdaptedSurgeryWindows.pathConnectedSpace_middle_level [PathConnectedSpace M]
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) {a : ℝ}
    (hreg : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hhigh : ∀ p : criticalPoints E f, a ≤ f p → 3 ≤ nativeMorseIndex E f p)
    (hlow : ∀ p : criticalPoints E f, f p ≤ a → nativeMorseIndex E f p ≤ 3)
    (z₀ : {z : M // f z = a}) : PathConnectedSpace {z : M // f z = a} :=
  S.pathConnectedSpace_regular_level_of_endpoint_dimensions hf hreg
    (fun p hp => by have hh := hhigh p hp; omega) hlow (by omega) z₀

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
