import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Basic

/-!
# The boundary norm of a disc homeomorphism

The inverse image of every smaller closed disc is compact in the ambient
plane. Consequently, a homeomorphism from a plane domain to the unit disc
has norm tending to one when the source tends to a point outside the domain.
In particular this holds at every boundary point of an open domain.

This is a properness statement, not an assumption that the homeomorphism
already extends continuously to the boundary.
-/

noncomputable section

open Set Metric Filter Topology

namespace Wikipedia.HopfProblem.RiemannMapping

/-- Smaller closed discs have compact inverse images in the ambient source
plane under a homeomorphism onto the open unit disc. -/
theorem isCompact_discHomeomorph_preimage_closedBall
    {U : Set ℂ} (e : U ≃ₜ ball (0 : ℂ) 1) {r : ℝ} (hr : r < 1) :
    IsCompact ((Subtype.val : U → ℂ) ''
      (e ⁻¹' ((Subtype.val : ball (0 : ℂ) 1 → ℂ) ⁻¹' closedBall 0 r))) := by
  apply IsCompact.image _ continuous_subtype_val
  apply e.isCompact_preimage.mpr
  apply IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall _ _) ?_
  simpa only [Subtype.range_coe] using closedBall_subset_ball hr

/-- The norm of a disc homeomorphism tends to one along every source filter
whose ambient limit lies outside the domain. -/
theorem tendsto_norm_discHomeomorph_of_notMem
    {U : Set ℂ} (e : U ≃ₜ ball (0 : ℂ) 1)
    {α : Type*} {l : Filter α} {z : α → U} {a : ℂ}
    (ha : a ∉ U) (hz : Tendsto (fun i => (z i : ℂ)) l (𝓝 a)) :
    Tendsto (fun i => ‖(e (z i) : ℂ)‖) l (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    let K : Set ℂ := (Subtype.val : U → ℂ) ''
      (e ⁻¹' ((Subtype.val : ball (0 : ℂ) 1 → ℂ) ⁻¹' closedBall 0 r))
    have hK : IsCompact K := isCompact_discHomeomorph_preimage_closedBall e hr
    have haK : a ∉ K := by
      rintro ⟨w, _, hwa⟩
      exact ha (hwa ▸ w.property)
    have hevent : ∀ᶠ i in l, (z i : ℂ) ∉ K :=
      hz.eventually (hK.isClosed.isOpen_compl.mem_nhds haK)
    filter_upwards [hevent] with i hi
    apply lt_of_not_ge
    intro hle
    apply hi
    refine ⟨z i, ?_, rfl⟩
    simpa only [mem_preimage, mem_closedBall, dist_zero_right] using hle
  · intro r hr
    apply Filter.Eventually.of_forall
    intro i
    have hi : ‖(e (z i) : ℂ)‖ < 1 := by
      simpa only [mem_ball, dist_zero_right] using (e (z i)).property
    exact hi.trans hr

/-- At a boundary point of an open domain, the norm of a disc
homeomorphism tends to one along every source filter converging there. -/
theorem tendsto_norm_discHomeomorph_of_mem_frontier
    {U : Set ℂ} (hU : IsOpen U) (e : U ≃ₜ ball (0 : ℂ) 1)
    {α : Type*} {l : Filter α} {z : α → U} {a : ℂ}
    (ha : a ∈ frontier U) (hz : Tendsto (fun i => (z i : ℂ)) l (𝓝 a)) :
    Tendsto (fun i => ‖(e (z i) : ℂ)‖) l (𝓝 1) := by
  apply tendsto_norm_discHomeomorph_of_notMem e _ hz
  exact (hU.frontier_eq ▸ ha).2

/-- The intrinsic source-filter formulation of the boundary norm limit.
The filter is the pullback of ambient neighborhoods to the domain. -/
theorem tendsto_norm_discHomeomorph_comap_nhds
    {U : Set ℂ} (hU : IsOpen U) (e : U ≃ₜ ball (0 : ℂ) 1)
    {a : ℂ} (ha : a ∈ frontier U) :
    Tendsto (fun z : U => ‖(e z : ℂ)‖)
      (comap (Subtype.val : U → ℂ) (𝓝 a)) (𝓝 1) :=
  tendsto_norm_discHomeomorph_of_mem_frontier hU e ha tendsto_comap

/-- Any complex-valued representative of a disc homeomorphism has norm
tending to one within the domain at a boundary point. Its values outside
the domain, including its value at the boundary point, are irrelevant. -/
theorem tendsto_norm_discHomeomorph_nhdsWithin
    {U : Set ℂ} (hU : IsOpen U) (e : U ≃ₜ ball (0 : ℂ) 1)
    {f : ℂ → ℂ} (he : ∀ z : U, f z = (e z : ℂ))
    {a : ℂ} (ha : a ∈ frontier U) :
    Tendsto (fun z => ‖f z‖) (𝓝[U] a) (𝓝 1) := by
  have hz : Tendsto (Subtype.val : U → ℂ)
      (comap (Subtype.val : U → ℂ) (𝓝[U] a)) (𝓝 a) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have ht := tendsto_norm_discHomeomorph_of_mem_frontier hU e ha hz
  apply (tendsto_comap'_iff (i := (Subtype.val : U → ℂ)) ?_).mp
  · simpa only [Function.comp_def, he] using ht
  · simpa only [Subtype.range_coe] using (self_mem_nhdsWithin : U ∈ 𝓝[U] a)

end Wikipedia.HopfProblem.RiemannMapping
