import Wikipedia.HopfProblem.HolomorphicMeromorphicSlices
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Compactness.Lindelof

/-!
# A constant product box from uncountably many locally constant fibres

An analytic function on an open subset of a second-countable complex
product space is independent of the fibre variable on some actual product
of balls if it is locally constant on a nonempty piece of each of
uncountably many fibres.  A countable product-ball cover and the
one-dimensional analytic zero-countability theorem prove the result.
The fibre-local identity is propagated only inside connected fibre balls.
-/

open Set Filter Topology Metric

namespace Wikipedia.HopfProblem.HolomorphicMeromorphicUncountableBoxes

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- If an analytic function on a product is not fibrewise constant,
the parameters admitting a locally constant germ anywhere in the
connected fibre domain form a countable set. -/
theorem countable_locally_constant_slice_parameters
    {U : Set ℂ} {V : Set E} {F : ℂ × E → ℂ}
    (hU : IsPreconnected U) (hV : IsPreconnected V)
    (hF : AnalyticOnNhd ℂ F (U ×ˢ V))
    (hne : ∃ a ∈ U, ∃ v ∈ V, ∃ w ∈ V, F (a, v) ≠ F (a, w)) :
    Set.Countable {z | z ∈ U ∧ ∃ v ∈ V,
      (fun w => F (z, w)) =ᶠ[𝓝 v] fun _ => F (z, v)} := by
  obtain ⟨a, ha, v, hv, w, hw, hne⟩ := hne
  have hfv : AnalyticOnNhd ℂ (fun z => F (z, v)) U :=
    fun z hz => (hF (z, v) ⟨hz, hv⟩).curry_left
  have hfw : AnalyticOnNhd ℂ (fun z => F (z, w)) U :=
    fun z hz => (hF (z, w) ⟨hz, hw⟩).curry_left
  have hc := HolomorphicMeromorphicSlices.countable_zero_set hU (hfv.sub hfw)
    ⟨a, ha, sub_ne_zero.mpr hne⟩
  apply hc.mono
  rintro z ⟨hz, u, hu, hlocal⟩
  have hslice : AnalyticOnNhd ℂ (fun y => F (z, y)) V :=
    fun y hy => (hF (z, y) ⟨hz, hy⟩).curry_right
  have heq : EqOn (fun y => F (z, y)) (fun _ => F (z, u)) V :=
    hslice.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hV hu hlocal
  exact ⟨hz, sub_eq_zero.mpr ((heq hv).trans (heq hw).symm)⟩

variable [SecondCountableTopology E]

/-- Uncountably many fibres with a genuinely locally constant piece
force fibrewise constancy on a nonempty product of actual open balls
contained in the original domain. -/
theorem exists_fibre_constant_ball_product
    {Ω : Set (ℂ × E)} {F : ℂ × E → ℂ} {S : Set ℂ}
    (hΩ : IsOpen Ω) (hF : AnalyticOnNhd ℂ F Ω) (hS : ¬ S.Countable)
    (hlocal : ∀ z ∈ S, ∃ v, (z, v) ∈ Ω ∧
      (fun w => F (z, w)) =ᶠ[𝓝 v] fun _ => F (z, v)) :
    ∃ (a : ℂ) (b : E) (r : ℝ), 0 < r ∧ ball a r ×ˢ ball b r ⊆ Ω ∧
      ∀ z ∈ ball a r, ∀ v ∈ ball b r, ∀ w ∈ ball b r, F (z, v) = F (z, w) := by
  classical
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  choose r hr hsub using fun p : Ω => (Metric.isOpen_iff.mp hΩ) p.val p.property
  let B : Ω → Set (ℂ × E) := fun p => ball p.val.1 (r p) ×ˢ ball p.val.2 (r p)
  have hBsub (p : Ω) : B p ⊆ Ω := by
    change ball p.val.1 (r p) ×ˢ ball p.val.2 (r p) ⊆ Ω
    rw [ball_prod_same]
    exact hsub p
  have hBopen (p : Ω) : IsOpen (B p) := isOpen_ball.prod isOpen_ball
  have hcover : Ω ⊆ ⋃ p : Ω, B p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p, hp⟩,
      ⟨mem_ball_self (hr ⟨p, hp⟩), mem_ball_self (hr ⟨p, hp⟩)⟩⟩
  obtain ⟨c, hc, hcover⟩ := (HereditarilyLindelofSpace.isLindelof Ω).elim_countable_subcover
    B hBopen hcover
  by_contra hnone
  let C : Ω → Set ℂ := fun p => {z | z ∈ ball p.val.1 (r p) ∧
    ∃ v ∈ ball p.val.2 (r p),
      (fun w => F (z, w)) =ᶠ[𝓝 v] fun _ => F (z, v)}
  have hC (p : Ω) : (C p).Countable := by
    apply countable_locally_constant_slice_parameters
      Metric.isPreconnected_ball Metric.isPreconnected_ball (hF.mono (hBsub p))
    have hnot : ¬ ∀ z ∈ ball p.val.1 (r p), ∀ v ∈ ball p.val.2 (r p),
        ∀ w ∈ ball p.val.2 (r p), F (z, v) = F (z, w) := by
      intro hconst
      exact hnone ⟨p.val.1, p.val.2, r p, hr p, hBsub p, hconst⟩
    push Not at hnot
    exact hnot
  have hcount : (⋃ p ∈ c, C p).Countable := hc.biUnion_iff.mpr (fun p _ => hC p)
  apply hS
  apply hcount.mono
  intro z hz
  obtain ⟨v, hzv, hconst⟩ := hlocal z hz
  obtain ⟨p, hp⟩ := mem_iUnion.mp (hcover hzv)
  obtain ⟨hpc, hp⟩ := mem_iUnion.mp hp
  exact mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨hpc, hp.1, v, hp.2, hconst⟩⟩

/-- On the resulting product box the function is the pullback of an
actual analytic function of the complex parameter. -/
theorem exists_analytic_factor_on_ball_product
    {Ω : Set (ℂ × E)} {F : ℂ × E → ℂ} {S : Set ℂ}
    (hΩ : IsOpen Ω) (hF : AnalyticOnNhd ℂ F Ω) (hS : ¬ S.Countable)
    (hlocal : ∀ z ∈ S, ∃ v, (z, v) ∈ Ω ∧
      (fun w => F (z, w)) =ᶠ[𝓝 v] fun _ => F (z, v)) :
    ∃ (a : ℂ) (b : E) (r : ℝ), 0 < r ∧ ball a r ×ˢ ball b r ⊆ Ω ∧
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball a r) ∧
        EqOn F (fun p => g p.1) (ball a r ×ˢ ball b r) := by
  obtain ⟨a, b, r, hr, hsub, hconst⟩ :=
    exists_fibre_constant_ball_product hΩ hF hS hlocal
  refine ⟨a, b, r, hr, hsub, (fun z => F (z, b)), ?_, ?_⟩
  · intro z hz
    exact (hF (z, b) (hsub ⟨hz, mem_ball_self hr⟩)).curry_left
  · rintro ⟨z, v⟩ ⟨hz, hv⟩
    exact hconst z hz v hv b (mem_ball_self hr)

end Wikipedia.HopfProblem.HolomorphicMeromorphicUncountableBoxes
