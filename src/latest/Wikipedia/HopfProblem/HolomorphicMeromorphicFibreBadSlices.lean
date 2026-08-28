import Wikipedia.HopfProblem.HolomorphicMeromorphicSlices
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Compactness.Lindelof

/-!
# Countably many fibrewise zero-germ parameters

For a holomorphic denominator with no zero germ on an open subset of
`ℂ × E`, only countably many complex parameters admit a zero germ after
restriction to a fibre. A countable cover by actual product balls reduces
the assertion to analytic continuation in each connected fibre ball and
the one-variable zero-countability theorem.
-/

open Set Filter Topology Metric

namespace Wikipedia.HopfProblem.HolomorphicMeromorphicFibreBadSlices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- On a connected product domain, a locally zero fibre germ extends
throughout the fibre. If the function is not identically zero, only
countably many parameters can have such a germ. -/
theorem countable_zero_germ_slice_parameters
    {U : Set ℂ} {V : Set E} {q : ℂ × E → ℂ}
    (hU : IsPreconnected U) (hV : IsPreconnected V)
    (hq : AnalyticOnNhd ℂ q (U ×ˢ V))
    (hne : ∃ a ∈ U, ∃ v ∈ V, q (a, v) ≠ 0) :
    Set.Countable {z | z ∈ U ∧ ∃ v ∈ V, (fun w => q (z, w)) =ᶠ[𝓝 v] 0} := by
  apply (HolomorphicMeromorphicSlices.countable_zero_slices hU hq hne).mono
  rintro z ⟨hz, v, hv, hzero⟩
  have hslice : AnalyticOnNhd ℂ (fun w => q (z, w)) V :=
    fun w hw => (hq (z, w) ⟨hz, hw⟩).curry_right
  exact ⟨hz, hslice.eqOn_zero_of_preconnected_of_eventuallyEq_zero hV hv hzero⟩

variable [SecondCountableTopology E]

/-- A holomorphic function with no ambient zero germ on an arbitrary
open product-space domain has only countably many parameters at which
its restriction to some fibre neighborhood is the zero germ. -/
theorem countable_bad_slice_parameters
    {Ω : Set (ℂ × E)} {q : ℂ × E → ℂ}
    (hΩ : IsOpen Ω) (hq : AnalyticOnNhd ℂ q Ω)
    (hne : ∀ p ∈ Ω, ¬ q =ᶠ[𝓝 p] 0) :
    Set.Countable {z : ℂ | ∃ v : E, (z, v) ∈ Ω ∧
      (fun w => q (z, w)) =ᶠ[𝓝 v] 0} := by
  classical
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  choose r hr hsub using fun p : Ω => (Metric.isOpen_iff.mp hΩ) p.val p.property
  let B : Ω → Set (ℂ × E) := fun p => ball p.val.1 (r p) ×ˢ ball p.val.2 (r p)
  have hBsub (p : Ω) : B p ⊆ Ω := by
    change ball p.val.1 (r p) ×ˢ ball p.val.2 (r p) ⊆ Ω
    rw [ball_prod_same]
    exact hsub p
  have hBopen (p : Ω) : IsOpen (B p) := isOpen_ball.prod isOpen_ball
  have hBmem (p : Ω) : p.val ∈ B p :=
    ⟨mem_ball_self (hr p), mem_ball_self (hr p)⟩
  have hBne (p : Ω) : ∃ a ∈ ball p.val.1 (r p), ∃ v ∈ ball p.val.2 (r p),
      q (a, v) ≠ 0 := by
    by_contra hz
    push Not at hz
    apply hne p.val p.property
    filter_upwards [(hBopen p).mem_nhds (hBmem p)] with w hw
    exact hz w.1 hw.1 w.2 hw.2
  have hcover : Ω ⊆ ⋃ p : Ω, B p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩, hBmem ⟨p, hp⟩⟩
  obtain ⟨c, hc, hcover⟩ := (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover
    B hBopen hcover
  let C : Ω → Set ℂ := fun p => {z | z ∈ ball p.val.1 (r p) ∧
    ∃ v ∈ ball p.val.2 (r p), (fun w => q (z, w)) =ᶠ[𝓝 v] 0}
  have hC (p : Ω) : (C p).Countable :=
    countable_zero_germ_slice_parameters Metric.isPreconnected_ball
      Metric.isPreconnected_ball (hq.mono (hBsub p)) (hBne p)
  have hcount : (⋃ p ∈ c, C p).Countable := hc.biUnion_iff.mpr (fun p _ => hC p)
  apply hcount.mono
  rintro z ⟨v, hzv, hzero⟩
  obtain ⟨p, hp⟩ := mem_iUnion.mp (hcover hzv)
  obtain ⟨hpc, hp⟩ := mem_iUnion.mp hp
  exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hpc, hp.1, v, hp.2, hzero⟩⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphicFibreBadSlices
