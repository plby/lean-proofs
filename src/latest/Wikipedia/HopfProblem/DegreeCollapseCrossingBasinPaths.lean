import Wikipedia.HopfProblem.DegreeCollapseBackwardObstructionAboveCut
import Wikipedia.HopfProblem.DegreeCollapseMinimumLevelPathsReaching

/-!
# Paths through the actual lower-boundary crossing basin

The original flow cylinder makes the whole basin of a connected regular
level path connected. Within that open basin, the backward obstruction
only has endpoints strictly above the lower level. Native avoidance and
projection therefore join points in an intermediate level while retaining
crossing of both the lower and upper levels. No common minimum endpoint,
and no index bound below the original lower level, is assumed.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap TopologicalSpace
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

omit [T2Space M] in
theorem AdaptedSurgeryWindows.pathConnectedSpace_levelBasin
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b : ℝ} (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    [PathConnectedSpace {y : M // f y = b}] :
    PathConnectedSpace (FlowCancellation.levelBasin S.flow f b) := by
  let _ := RegularLevel.chartedSpace hf hb
  let z₀ : {y : M // f y = b} := Classical.arbitrary _
  obtain ⟨Φ, hsource, htarget, _, _⟩ := FlowCancellation.exists_native_level_flow_cylinder
    hf hb S.smooth S.flow S.integral (fun z hz => S.descent z (hb z hz)) z₀
  refine ⟨⟨⟨z₀.val, 0, by simpa only [S.flow.map_zero_apply] using z₀.property⟩⟩, ?_⟩
  intro x y
  let η := PathConnectedSpace.somePath (Φ.symm x.val) (Φ.symm y.val)
  have hstay (s : unitInterval) : η s ∈ Φ.source := by rw [hsource]; trivial
  have hcross (s : unitInterval) : Φ (η s) ∈ FlowCancellation.levelBasin S.flow f b :=
    by
      have hh := Φ.map_source' (hstay s)
      rwa [htarget] at hh
  let γ : Path x y := {
    toFun s := ⟨Φ (η s), hcross s⟩
    continuous_toFun :=
      (Φ.contMDiffOn_toFun.continuousOn.comp_continuous η.continuous hstay).subtype_mk _
    source' := by
      apply Subtype.ext
      change Φ (η 0) = x.val
      rw [η.source]
      exact Φ.right_inv' (htarget.symm ▸ x.property)
    target' := by
      apply Subtype.ext
      change Φ (η 1) = y.val
      rw [η.target]
      exact Φ.right_inv' (htarget.symm ▸ y.property) }
  exact ⟨γ⟩

theorem AdaptedSurgeryWindows.joinedIn_level_crossing_both_cuts
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {c b a : ℝ} (hcb : c < b) (hba : b ≤ a)
    (hc : ∀ y, f y = c → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    [PathConnectedSpace {y : M // f y = c}]
    {d : ℕ} (hlow : ∀ q : criticalPoints E f, c < f q → f q ≤ a → nativeMorseIndex E f q ≤ d)
    (hdim : 1 + d < Module.finrank ℝ E) {x y : M} (hxb : f x = b) (hyb : f y = b)
    (hxc : x ∈ FlowCancellation.levelBasin S.flow f c)
    (hyc : y ∈ FlowCancellation.levelBasin S.flow f c)
    (hxa : x ∈ FlowCancellation.levelBasin S.flow f a)
    (hya : y ∈ FlowCancellation.levelBasin S.flow f a) :
    JoinedIn {z : M | f z = b ∧ z ∈ FlowCancellation.levelBasin S.flow f c ∧
      z ∈ FlowCancellation.levelBasin S.flow f a} x y := by
  let _ := S.finite.fintype
  let K := BetweenBackwardBasinIndex S c a
  let Z := EuclideanSpace ℝ (Fin 0)
  let V := EuclideanSpace ℝ (Fin d)
  let _ : Countable K := betweenBackwardBasinIndex_countable S c a
  let _ : DiscreteTopology K := inferInstance
  let _ : ChartedSpace Z K := ChartedSpace.ofDiscreteTopology
  let _ : IsManifold 𝓘(ℝ, Z) ∞ K := IsManifold.of_discreteTopology ∞
  obtain ⟨g, hg, hcover⟩ := S.exists_between_backward_obstruction_images hf c a hlow
  have hG : ContMDiff (𝓘(ℝ, Z).prod 𝓘(ℝ, V)) 𝓘(ℝ, E) ∞
      (fun z : K × V => g z.1 z.2) := contMDiff_discrete_family g hg
  let G : C(K × V, M) := ⟨fun z => g z.1 z.2, hG.continuous⟩
  have hrangeG : range G = backwardBetweenBasins S c a := by
    rw [hcover]
    exact range_discrete_family g
  let U : Opens M := ⟨FlowCancellation.levelBasin S.flow f c,
    (FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral
      (fun z hz => S.descent z (hc z hz))).1⟩
  let : PathConnectedSpace U := S.pathConnectedSpace_levelBasin hf hc
  let R := OpenObstacle.restrict G U
  have hrange : range R = (Subtype.val : U → M) ⁻¹' backwardLowBasins S a := by
    rw [OpenObstacle.range_restrict, hrangeG]
    ext z
    exact (S.backward_obstruction_on_crossing_basin hf hc z.property).symm
  have hclosed : IsClosed (range R) := by
    rw [hrange]
    exact (isClosed_backwardLowBasins S hf a).preimage continuous_subtype_val
  have hdim' : 1 + Module.finrank ℝ (Z × V) < Module.finrank ℝ E := by
    simpa only [Z, V, Module.finrank_prod, finrank_euclideanSpace_fin, zero_add] using hdim
  have hnot (z : U) (hz : z.val ∈ FlowCancellation.levelBasin S.flow f a) : z ∉ range R := by
    rw [hrange]
    intro hlowz
    have hbad : z.val ∈ (FlowCancellation.levelBasin S.flow f a)ᶜ := by
      rw [levelBasin_compl_eq_endpoint_obstruction S hf ha]
      exact Or.inr hlowz
    exact hbad hz
  let xU : U := ⟨x, hxc⟩
  let yU : U := ⟨y, hyc⟩
  obtain ⟨η, _, havoid⟩ := exists_smooth_path_avoiding_closed_image
    (PathConnectedSpace.somePath xU yU) R (OpenObstacle.contMDiff_restrict G U hG)
    hclosed hdim' (hnot xU hxa) (hnot yU hya)
  have hcross (l : ℝ) (hcl : c < l) (hla : l ≤ a) (u : unitInterval) :
      (η u).val ∈ FlowCancellation.levelBasin S.flow f l := by
    obtain ⟨p, hp, q, hq, hback, hforward, _⟩ := FlowCancellation.exists_native_descent_endpoints
      hf S.smooth S.flow S.integral S.zero S.descent S.distinct (η u).val
    have hends := S.endpoint_values_straddle_crossed_level hf hc (η u).property
      ⟨p, hp⟩ ⟨q, hq⟩ hback hforward
    have hap : a < f p := lt_of_not_ge (fun h => havoid u (hrange.symm ▸
      (show η u ∈ (Subtype.val : U → M) ⁻¹' backwardLowBasins S a from ⟨⟨p, hp⟩, h, hback⟩)))
    exact FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
      hback hforward (hla.trans_lt hap) (hends.2.trans hcl)
  let _ := RegularLevel.chartedSpace hf hb
  let xL : {z : M // f z = b} := ⟨x, hxb⟩
  let yL : {z : M // f z = b} := ⟨y, hyb⟩
  obtain ⟨Φ, hsource, htarget, hformula, _⟩ := FlowCancellation.exists_native_level_flow_cylinder
    hf hb S.smooth S.flow S.integral (fun z hz => S.descent z (hb z hz)) xL
  have hcont : Continuous (fun u : unitInterval => Φ.symm (η u).val) :=
    Φ.contMDiffOn_invFun.continuousOn.comp_continuous
      (continuous_subtype_val.comp η.continuous) (fun u => htarget.symm ▸ hcross b hcb hba u)
  have hinverse (z : {w : M // f w = b}) : Φ.symm z.val = (z, 0) := by
    have hs : (z, (0 : ℝ)) ∈ Φ.source := by rw [hsource]; trivial
    have he : Φ (z, 0) = z.val := by rw [hformula, S.flow.map_zero_apply]
    have hi : Φ.symm (Φ (z, 0)) = (z, 0) := Φ.left_inv' hs
    rwa [he] at hi
  let γ : Path x y := {
    toFun u := (Φ.symm (η u).val).1.val
    continuous_toFun := continuous_subtype_val.comp (continuous_fst.comp hcont)
    source' := by
      rw [η.source]
      exact congrArg (fun z : {w : M // f w = b} × ℝ => z.1.val) (hinverse xL)
    target' := by
      rw [η.target]
      exact congrArg (fun z : {w : M // f w = b} × ℝ => z.1.val) (hinverse yL) }
  refine ⟨γ, fun u => ⟨(Φ.symm (η u).val).1.property, ?_, ?_⟩⟩
  · let z := Φ.symm (η u).val
    have hi : Φ z = (η u).val := Φ.right_inv' (htarget.symm ▸ hcross b hcb hba u)
    have hflow : S.flow z.2 z.1.val = (η u).val := (hformula z).symm.trans hi
    exact (FlowCancellation.levelBasin_flow_iff S.flow f c z.2 z.1.val).mp
      (hflow.symm ▸ (η u).property)
  · let z := Φ.symm (η u).val
    have hi : Φ z = (η u).val := Φ.right_inv' (htarget.symm ▸ hcross b hcb hba u)
    have hflow : S.flow z.2 z.1.val = (η u).val := (hformula z).symm.trans hi
    exact (FlowCancellation.levelBasin_flow_iff S.flow f a z.2 z.1.val).mp
      (hflow.symm ▸ hcross a (hcb.trans_le hba) le_rfl u)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
