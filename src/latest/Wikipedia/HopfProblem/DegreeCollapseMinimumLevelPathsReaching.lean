import Wikipedia.HopfProblem.DegreeCollapseMinimumLevelPaths

/-!
# Minimum-basin paths in a lower level that all reach a higher level

Avoidance removes the full backward obstruction below the higher level.
Projection to the lower level then retains both the minimum endpoint and
the higher-level crossing condition, because both are orbit-invariant.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap TopologicalSpace
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.joinedIn_level_minimum_basin_reaching_level
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 0)
    {a b : ℝ} (hpb : f p < b) (hba : b ≤ a)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    {d : ℕ} (hlow : ∀ q : criticalPoints E f, f q ≤ a → nativeMorseIndex E f q ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) {x y : M} (hxb : f x = b) (hyb : f y = b)
    (hx : Tendsto (fun t => S.flow t x) atTop (𝓝 p.val))
    (hy : Tendsto (fun t => S.flow t y) atTop (𝓝 p.val))
    (hxa : x ∈ FlowCancellation.levelBasin S.flow f a)
    (hya : y ∈ FlowCancellation.levelBasin S.flow f a) :
    JoinedIn {z : M | f z = b ∧ Tendsto (fun t => S.flow t z) atTop (𝓝 p.val) ∧
      z ∈ FlowCancellation.levelBasin S.flow f a} x y := by
  let _ := S.finite.fintype
  let K := LowBackwardBasinIndex S a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := lowBackwardBasinIndex_countable S a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_low_backward_obstruction_images hf a hlow
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞
      (fun z : K × V => g z.1 z.2) := contMDiff_discrete_family g hg
  let G : C(K × V, M) := ⟨fun z => g z.1 z.2, hG.continuous⟩
  have hrange : range G = backwardLowBasins S a := by
    rw [hcover]
    exact range_discrete_family g
  have hclosed : IsClosed (range G) := by
    rw [hrange]
    exact isClosed_backwardLowBasins S hf a
  have hdim' : 1 + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim
  have hnot (z : M) (hz : z ∈ FlowCancellation.levelBasin S.flow f a) : z ∉ range G := by
    rw [hrange]
    intro hlowz
    have hc : z ∈ (FlowCancellation.levelBasin S.flow f a)ᶜ := by
      rw [levelBasin_compl_eq_endpoint_obstruction S hf ha]
      exact Or.inr hlowz
    exact hc hz
  let U : Opens M := ⟨{z | Tendsto (fun t => S.flow t z) atTop (𝓝 p.val)},
    S.isOpen_minimum_forward_basin hf p hp⟩
  let xU : U := ⟨x, hx⟩
  let yU : U := ⟨y, hy⟩
  have hjoined : Joined xU yU := (S.joinedIn_minimum_basin hf p hp hx hy).joined_subtype
  obtain ⟨η, -, havoid⟩ := exists_smooth_path_avoiding_closed_image_in_open U hjoined.somePath
    G hG hclosed hdim' (hnot x hxa) (hnot y hya)
  have hcross (c : ℝ) (hbc : b ≤ c) (hca : c ≤ a) (u : unitInterval) :
      (η u).val ∈ FlowCancellation.levelBasin S.flow f c := by
    obtain ⟨q, hq, _, _, hback, _, _⟩ := FlowCancellation.exists_native_descent_endpoints
      hf S.smooth S.flow S.integral S.zero S.descent S.distinct (η u).val
    have hqa : a < f q := lt_of_not_ge (fun h => havoid u (hrange.symm ▸
      (show (η u).val ∈ backwardLowBasins S a from ⟨⟨q, hq⟩, h, hback⟩)))
    exact FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
      hback (η u).property (hca.trans_lt hqa) (hpb.trans_le hbc)
  let _ := RegularLevel.chartedSpace hf hb
  let xL : {z : M // f z = b} := ⟨x, hxb⟩
  let yL : {z : M // f z = b} := ⟨y, hyb⟩
  obtain ⟨Φ, hsource, htarget, hformula, -⟩ := FlowCancellation.exists_native_level_flow_cylinder
    hf hb S.smooth S.flow S.integral (fun z hz => S.descent z (hb z hz)) xL
  have hcont : Continuous (fun u : unitInterval => Φ.symm (η u).val) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous
      (continuous_subtype_val.comp η.continuous) (fun u => htarget.symm ▸ hcross b le_rfl hba u)
  have hlevelInverse (z : {w : M // f w = b}) : Φ.symm z.val = (z, 0) := by
    have hs : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
    have he : Φ (z, 0) = z.val := by rw [hformula, S.flow.map_zero_apply]
    have hi : Φ.symm (Φ (z, 0)) = (z, 0) := Φ.left_inv' hs
    rwa [he] at hi
  let γ : Path x y := {
    toFun := fun u => (Φ.symm (η u).val).1.val
    continuous_toFun := continuous_subtype_val.comp (continuous_fst.comp hcont)
    source' := by
      rw [η.source]
      exact congrArg (fun z : {w : M // f w = b} × ℝ => z.1.val) (hlevelInverse xL)
    target' := by
      rw [η.target]
      exact congrArg (fun z : {w : M // f w = b} × ℝ => z.1.val) (hlevelInverse yL) }
  refine ⟨γ, fun u => ⟨(Φ.symm (η u).val).1.property, ?_, ?_⟩⟩
  · let z := Φ.symm (η u).val
    have hi : Φ z = (η u).val := Φ.right_inv' (htarget.symm ▸ hcross b le_rfl hba u)
    have hflow : S.flow z.2 z.1.val = (η u).val := (hformula z).symm.trans hi
    have hlim : Tendsto (fun t => S.flow t (S.flow z.2 z.1.val)) atTop (𝓝 p.val) :=
      hflow.symm ▸ (η u).property
    exact (flow_time_atTop_limit_iff S.flow z.2 z.1.val p.val).mp hlim
  · let z := Φ.symm (η u).val
    have hi : Φ z = (η u).val := Φ.right_inv' (htarget.symm ▸ hcross b le_rfl hba u)
    have hflow : S.flow z.2 z.1.val = (η u).val := (hformula z).symm.trans hi
    exact (FlowCancellation.levelBasin_flow_iff S.flow f a z.2 z.1.val).mp
      (hflow.symm ▸ hcross a hba le_rfl u)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
