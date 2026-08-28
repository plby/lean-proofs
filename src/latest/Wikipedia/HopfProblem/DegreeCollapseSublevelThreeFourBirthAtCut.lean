import Wikipedia.HopfProblem.DegreeCollapseSublevelIndexedBirth
import Wikipedia.HopfProblem.DegreeCollapseBirthCutIndexControl
import Wikipedia.HopfProblem.DegreeCollapseMinimumBranchRealization

/-!
# Construct the three/four birth between a retained level and an upper cut

An actual point on the lower regular level supplies a short reverse-time
segment and a regular birth band strictly below the untouched upper cut.
The original lower level is literally retained, and the new index-three
point is first above it. Both new values remain below the upper cut.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem exists_three_four_birth_between_cuts
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (A : AdaptedSurgeryWindows E f) (hdim : 3 < Module.finrank ℝ E)
    {a b : ℝ} (hab : a < b)
    (hreg : ∀ y, f y = a → y ∉ criticalPoints E f) (z : {y : M // f y = a}) :
    ∃ (g : M → ℝ) (p r : M), ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      InjOn g (criticalPoints E g) ∧
      nativeMorseIndex E g p = 3 ∧ nativeMorseIndex E g r = 4 ∧
      a < g p ∧ g p < g r ∧ g r < b ∧
      (criticalPoints E g).ncard = (criticalPoints E f).ncard + 2 ∧
      (∀ y, y ∈ criticalPoints E g ↔ y ∈ criticalPoints E f ∨ y = p ∨ y = r) ∧
      (∀ y ∈ criticalPoints E f, g =ᶠ[𝓝 y] f) ∧
      (∀ y, b ≤ f y → g =ᶠ[𝓝 y] f) ∧ (∀ y, g y < b ↔ f y < b) ∧
      (∀ y, g y = a ↔ f y = a) ∧
      (∀ y, g y = a → y ∉ criticalPoints E g) ∧
      (∀ s : criticalPoints E g, g s < g p → g s < a) ∧
      nativeMorseCount E g 3 = nativeMorseCount E f 3 + 1 ∧
      nativeMorseCount E g 4 = nativeMorseCount E f 4 + 1 ∧
      ∀ j, j ≠ 3 → j ≠ 4 → nativeMorseCount E g j = nativeMorseCount E f j := by
  obtain ⟨l₀, u₀, hl₀, hau₀, hband⟩ := A.regular_interval_around_level hreg
  let u := min u₀ ((a + b) / 2)
  have hau : a < u := lt_min hau₀ (by linarith)
  have huu₀ : u ≤ u₀ := min_le_left _ _
  have hub : u < b := (min_le_right _ _).trans_lt (by linarith)
  have hc : Continuous (fun s : ℝ => f (A.flow s z.val)) :=
    hf.continuous.comp (A.flow.continuous continuous_id continuous_const)
  have h0 : (fun s : ℝ => f (A.flow s z.val)) 0 ∈ Iio u := by
    simpa only [Flow.map_zero_apply, z.property, mem_Iio] using hau
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp
    (hc.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds h0))
  let x := A.flow (-ε / 2) z.val
  have hxu : f x < u := hεball (by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith)
  have hax : a < f x := by
    have hh := FlowConstruction.strictAnti_flow_height hf (A.smooth.of_le (by simp))
      A.flow A.integral A.zero A.descent (hreg z.val z.property) (show -ε / 2 < 0 by linarith)
    simpa only [Flow.map_zero_apply, z.property] using hh
  let l := (a + f x) / 2
  have hal : a < l := by dsimp [l]; linarith
  have hlx : l < f x := by dsimp [l]; linarith
  have hclosed : ∀ y, f y ∈ Icc l u → y ∉ criticalPoints E f := by
    intro y hy
    exact hband y ⟨(hl₀.trans hal).le.trans hy.1, hy.2.trans huu₀⟩
  obtain ⟨g, p, r, hg, hmg, hinjg, _, _, hip, hir, hpr, hpval, hrval, hcount, hcrit,
      hexterior, hkeep, hupper, hcut, hcount₃, hcount₄, hother⟩ :=
    exists_indexed_birth_below_cut hf hm A.distinct hub.le hclosed ⟨hlx, hxu⟩ hdim
  have hcrit' (y : M) (hy : y ∈ criticalPoints E g) :
      y ∈ criticalPoints E f ∨ y = p ∨ y = r := (hcrit y).mp hy
  have hap : a < g p := hal.trans hpval.1
  have har : a < g r := hal.trans hrval.1
  obtain ⟨heq, _⟩ := birth_preserves_lower_levels hf.continuous hg
    (show (f ⁻¹' Ioo l u) ⊆ {y : M | l < f y} from fun _ hy => hy.1)
    hexterior hkeep hcrit' hpval.1.le hrval.1.le hal
  have hgr := regular_level_of_retained_critical_germs hreg hcrit' hkeep hap har
  have hgap := birth_first_new_value_gap hcrit' hkeep hreg
    (fun y hy => hband y ⟨hl₀.le.trans hy.1.le, hy.2.le.trans huu₀⟩) hpval.2 hpr
  exact ⟨g, p, r, hg, hmg, hinjg, hip, hir, hap, hpr, hrval.2.trans hub,
    hcount, hcrit, hkeep, hupper, hcut, heq, hgr, hgap, hcount₃, hcount₄, hother⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
