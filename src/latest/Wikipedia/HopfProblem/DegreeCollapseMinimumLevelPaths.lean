import Wikipedia.HopfProblem.DegreeCollapseBackwardBasinObstacle
import Wikipedia.HopfProblem.DegreeCollapseDiscreteFamilySmooth
import Wikipedia.HopfProblem.DegreeCollapseClosedImagePathAvoidance
import Wikipedia.HopfProblem.DegreeCollapseOpenBasinPaths
import Wikipedia.HopfProblem.DegreeCollapseNativeFlowCylinder

/-!
# Connecting paths in an actual level inside a minimum's basin

Start with a path in the open minimum basin. Relative general position moves
it off every low backward basin, retaining both endpoints and the entire
minimum-basin condition. The native flow cylinder then projects the path
to the requested regular level. All projected points still tend to the same
minimum. Only the low critical indices enter the dimension inequality.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap TopologicalSpace
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.joinedIn_level_minimum_basin
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 0)
    {a : ℝ} (hpa : f p < a) (hreg : ∀ y, f y = a → y ∉ criticalPoints E f)
    {d : ℕ} (hlow : ∀ q : criticalPoints E f, f q ≤ a → nativeMorseIndex E f q ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) {x y : M} (hxa : f x = a) (hya : f y = a)
    (hx : Tendsto (fun t => S.flow t x) atTop (𝓝 p.val))
    (hy : Tendsto (fun t => S.flow t y) atTop (𝓝 p.val)) :
    JoinedIn {z : M | f z = a ∧ Tendsto (fun t => S.flow t z) atTop (𝓝 p.val)} x y := by
  let _ := S.finite.fintype
  let J := LowBackwardBasinIndex S a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable J := lowBackwardBasinIndex_countable S a
  let _ : DiscreteTopology J := inferInstance
  let _ : ChartedSpace Z J := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ J := IsManifold.of_discreteTopology ∞
  obtain ⟨b, hb, hcover⟩ := S.exists_low_backward_obstruction_images hf a hlow
  have hB : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞
      (fun z : J × V => b z.1 z.2) := contMDiff_discrete_family b hb
  let B : C(J × V, M) := ⟨fun z => b z.1 z.2, hB.continuous⟩
  have hrange : range B = backwardLowBasins S a := by
    rw [hcover]
    exact range_discrete_family b
  have hclosed : IsClosed (range B) := by
    rw [hrange]
    exact isClosed_backwardLowBasins S hf a
  have hdim' : 1 + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim
  have hnot (z : M) (hz : f z = a) : z ∉ range B := by
    rw [hrange]
    intro hlowz
    have hc : z ∈ (FlowCancellation.levelBasin S.flow f a)ᶜ := by
      rw [levelBasin_compl_eq_endpoint_obstruction S hf hreg]
      exact Or.inr hlowz
    exact hc ⟨0, by simpa only [S.flow.map_zero_apply] using hz⟩
  let U : Opens M := ⟨{z | Tendsto (fun t => S.flow t z) atTop (𝓝 p.val)},
    S.isOpen_minimum_forward_basin hf p hp⟩
  let xU : U := ⟨x, hx⟩
  let yU : U := ⟨y, hy⟩
  have hjoined : Joined xU yU := (S.joinedIn_minimum_basin hf p hp hx hy).joined_subtype
  obtain ⟨η, -, havoid⟩ := exists_smooth_path_avoiding_closed_image_in_open U hjoined.somePath
    B hB hclosed hdim' (hnot x hxa) (hnot y hya)
  have hcross (u : unitInterval) : (η u).val ∈ FlowCancellation.levelBasin S.flow f a := by
    obtain ⟨q, hq, -, -, hback, -, -⟩ := FlowCancellation.exists_native_descent_endpoints
      hf S.smooth S.flow S.integral S.zero S.descent S.distinct (η u).val
    have hqa : a < f q := lt_of_not_ge (fun h => havoid u (hrange.symm ▸
      (show (η u).val ∈ backwardLowBasins S a from ⟨⟨q, hq⟩, h, hback⟩)))
    exact FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
      hback (η u).property hqa hpa
  let _ := RegularLevel.chartedSpace hf hreg
  let xL : {z : M // f z = a} := ⟨x, hxa⟩
  let yL : {z : M // f z = a} := ⟨y, hya⟩
  obtain ⟨Φ, hsource, htarget, hformula, -⟩ := FlowCancellation.exists_native_level_flow_cylinder
    hf hreg S.smooth S.flow S.integral (fun z hz => S.descent z (hreg z hz)) xL
  have hcont : Continuous (fun u : unitInterval => Φ.symm (η u).val) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous
      (continuous_subtype_val.comp η.continuous) (fun u => htarget.symm ▸ hcross u)
  have hlevelInverse (z : {w : M // f w = a}) : Φ.symm z.val = (z, 0) := by
    have hs : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
    have he : Φ (z, 0) = z.val := by rw [hformula, S.flow.map_zero_apply]
    have hi : Φ.symm (Φ (z, 0)) = (z, 0) := Φ.left_inv' hs
    rwa [he] at hi
  let γ : Path x y := {
    toFun := fun u => (Φ.symm (η u).val).1.val
    continuous_toFun := continuous_subtype_val.comp (continuous_fst.comp hcont)
    source' := by
      rw [η.source]
      exact congrArg (fun z : {w : M // f w = a} × ℝ => z.1.val) (hlevelInverse xL)
    target' := by
      rw [η.target]
      exact congrArg (fun z : {w : M // f w = a} × ℝ => z.1.val) (hlevelInverse yL) }
  refine ⟨γ, fun u => ⟨(Φ.symm (η u).val).1.property, ?_⟩⟩
  let z := Φ.symm (η u).val
  have hi : Φ z = (η u).val := Φ.right_inv' (htarget.symm ▸ hcross u)
  have hflow : S.flow z.2 z.1.val = (η u).val := (hformula z).symm.trans hi
  have hlim : Tendsto (fun t => S.flow t (S.flow z.2 z.1.val)) atTop (𝓝 p.val) :=
    hflow.symm ▸ (η u).property
  exact (flow_time_atTop_limit_iff S.flow z.2 z.1.val p.val).mp hlim

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
