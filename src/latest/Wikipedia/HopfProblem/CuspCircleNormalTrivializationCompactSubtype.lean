import Wikipedia.HopfProblem.CuspCircleNormalTrivializationCompactNeighborhood
import Mathlib.Topology.Sets.Opens

/-!
# Uniform injective neighborhoods for maps on actual open subtypes

The map is defined only on its given open domain. The compact zero
section and its injective neighborhood are constructed inside that
subtype. The open subtype inclusion then gives an ambient open set,
and the compact-base tube lemma supplies a single positive normal radius.
No arbitrary extension of the map outside its domain is used.
-/

open Set TopologicalSpace

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

variable {B F Y : Type*} [TopologicalSpace B] [CompactSpace B]
  [PseudoMetricSpace F] [Zero F] [TopologicalSpace Y] [T2Space Y]

/-- A continuous locally injective map on an actual open subtype, injective
on its compact zero section, is injective throughout a uniform-radius
normal neighborhood contained in the original domain. -/
theorem exists_pos_injOn_open_subtype_prod_ball
    {O : Opens (B × F)} {f : O → Y}
    (hzero : ∀ b : B, (b, (0 : F)) ∈ O)
    (hf : Continuous f)
    (hloc : ∀ x : O, ∃ V : Set O, IsOpen V ∧ x ∈ V ∧ InjOn f V)
    (hinjzero : Function.Injective
      (fun b : B => f ⟨(b, (0 : F)), hzero b⟩)) :
    ∃ r : ℝ, 0 < r ∧ (univ : Set B) ×ˢ Metric.ball (0 : F) r ⊆ (O : Set (B × F)) ∧
      InjOn f {x : O | x.val.2 ∈ Metric.ball (0 : F) r} := by
  let s : B → O := fun b => ⟨(b, (0 : F)), hzero b⟩
  have hs : Continuous s := (continuous_id.prodMk continuous_const).subtype_mk hzero
  have hK : IsCompact (range s) := isCompact_range hs
  have hKinj : InjOn f (range s) := by
    rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩ he
    exact congrArg s (hinjzero he)
  obtain ⟨V, hV, hKV, hVf⟩ := exists_open_injOn_of_compact hf hloc hK hKinj
  let U : Set (B × F) := Subtype.val '' V
  have hU : IsOpen U := O.isOpen.isOpenMap_subtype_val V hV
  have hUO : U ⊆ (O : Set (B × F)) := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hzeroU : ∀ b : B, (b, (0 : F)) ∈ U := by
    intro b
    exact ⟨s b, hKV (mem_range_self b), rfl⟩
  obtain ⟨r, hr, hball⟩ := exists_pos_prod_ball_subset hU (0 : F) hzeroU
  refine ⟨r, hr, hball.trans hUO, hVf.mono ?_⟩
  intro x hx
  have hxU : x.val ∈ U := hball ⟨mem_univ x.val.1, hx⟩
  obtain ⟨y, hy, hyx⟩ := hxU
  exact (Subtype.ext hyx : y = x) ▸ hy

/-- The local-homeomorphism version uses only the native map on the open
subtype and its actual zero-section values. -/
theorem exists_pos_injOn_open_subtype_prod_ball_of_isLocalHomeomorph
    {O : Opens (B × F)} {f : O → Y}
    (hzero : ∀ b : B, (b, (0 : F)) ∈ O)
    (hf : IsLocalHomeomorph f)
    (hinjzero : Function.Injective
      (fun b : B => f ⟨(b, (0 : F)), hzero b⟩)) :
    ∃ r : ℝ, 0 < r ∧ (univ : Set B) ×ˢ Metric.ball (0 : F) r ⊆ (O : Set (B × F)) ∧
      InjOn f {x : O | x.val.2 ∈ Metric.ball (0 : F) r} := by
  apply exists_pos_injOn_open_subtype_prod_ball hzero hf.continuous _ hinjzero
  intro x
  obtain ⟨e, he, hfe⟩ := hf x
  exact ⟨e.source, e.open_source, he, hfe ▸ e.injOn⟩

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
