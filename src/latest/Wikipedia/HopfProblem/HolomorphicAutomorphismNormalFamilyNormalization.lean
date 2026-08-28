import Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamilyCompact

/-!
# Preserving a normal-family normalization

Locally uniform convergence controls evaluations at moving points. Thus
a norm normalization attained on a fixed compact set cannot disappear
in the limit. Continuity of the limit below is deduced from the actual
holomorphic approximants; it is not an additional assumption.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- Passing to a convergent reindexing preserves locally uniform convergence. -/
theorem locallyUniform_reindex {ι κ : Type*} {p : Filter ι} {q : Filter κ}
    {f : ι → E → F} {g : E → F} {U : Set E}
    (hf : TendstoLocallyUniformlyOn f g p U) {φ : κ → ι} (hφ : Tendsto φ q p) :
    TendstoLocallyUniformlyOn (fun i => f (φ i)) g q U := by
  intro u hu x hx
  obtain ⟨t, ht, h⟩ := hf u hu x hx
  exact ⟨t, ht, hφ.eventually h⟩

variable [NormedSpace ℂ E] [NormedSpace ℂ F]

/-- Locally uniform convergence of holomorphic maps also controls
evaluation at a moving point converging inside the domain. -/
theorem tendsto_evaluation_moving {ι : Type*} {p : Filter ι} [p.NeBot]
    {U : Set E} (hU : IsOpen U) {f : ι → E → F} {g : E → F}
    (hf : TendstoLocallyUniformlyOn f g p U)
    (hfd : ∀ᶠ i in p, DifferentiableOn ℂ (f i) U)
    {x : ι → E} {z : E} (hz : z ∈ U) (hx : Tendsto x p (𝓝 z)) :
    Tendsto (fun i => f i (x i)) p (𝓝 (g z)) := by
  have hc : ContinuousOn g U :=
    hf.continuousOn (hfd.mono fun i hi => hi.continuousOn).frequently
  apply hf.tendsto_comp (hc z hz) hz
  rwa [hU.nhdsWithin_eq hz]

/-- A fixed norm at the moving normalization points persists at the limit. -/
theorem norm_eq_of_moving {ι : Type*} {p : Filter ι} [p.NeBot]
    {U : Set E} (hU : IsOpen U) {f : ι → E → F} {g : E → F}
    (hf : TendstoLocallyUniformlyOn f g p U)
    (hfd : ∀ᶠ i in p, DifferentiableOn ℂ (f i) U)
    {x : ι → E} {z : E} (hz : z ∈ U) (hx : Tendsto x p (𝓝 z))
    {r : ℝ} (hnorm : ∀ᶠ i in p, ‖f i (x i)‖ = r) : ‖g z‖ = r := by
  apply tendsto_nhds_unique (tendsto_evaluation_moving hU hf hfd hz hx).norm
  exact tendsto_const_nhds.congr' (hnorm.mono fun i hi => hi.symm)

/-- When each approximant attains the same norm on a fixed compact subset
of the domain, the limit attains it there as well. -/
theorem exists_point_norm_eq_of_compact {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {f : ℕ → E → F} {g : E → F}
    (hf : TendstoLocallyUniformlyOn f g atTop U)
    (hfd : ∀ n, DifferentiableOn ℂ (f n) U) {r : ℝ}
    (hnorm : ∀ n, ∃ x ∈ K, ‖f n x‖ = r) :
    ∃ z ∈ K, ‖g z‖ = r := by
  choose x hxK hxnorm using hnorm
  obtain ⟨z, hz, φ, hφ, hxconv⟩ := hK.tendsto_subseq hxK
  refine ⟨z, hz, norm_eq_of_moving hU (locallyUniform_reindex hf hφ.tendsto_atTop)
    (Eventually.of_forall fun n => hfd (φ n)) (hKU hz) hxconv ?_⟩
  exact Eventually.of_forall fun n => hxnorm (φ n)

/-- Positive compact normalization gives a genuinely nonzero limit. -/
theorem exists_ne_zero_of_compact_normalization {U K : Set E} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) {f : ℕ → E → F} {g : E → F}
    (hf : TendstoLocallyUniformlyOn f g atTop U)
    (hfd : ∀ n, DifferentiableOn ℂ (f n) U) {r : ℝ} (hr : 0 < r)
    (hnorm : ∀ n, ∃ x ∈ K, ‖f n x‖ = r) :
    ∃ z ∈ K, g z ≠ 0 := by
  obtain ⟨z, hz, hnormz⟩ := exists_point_norm_eq_of_compact hU hK hKU hf hfd hnorm
  exact ⟨z, hz, norm_pos_iff.mp (hnormz.symm ▸ hr)⟩

end Wikipedia.HopfProblem.HolomorphicAutomorphismNormalFamily
