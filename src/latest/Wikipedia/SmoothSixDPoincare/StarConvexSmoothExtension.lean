import Mathlib.Analysis.Convex.Star
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Smooth extension near a compact star-convex source region

A small open thickening of the region is still star-convex and lies inside
the given smoothness domain. A smooth scalar cutoff constructs a map from the
whole source into this neighborhood, equal to the identity near the region.
Precomposition therefore extends a locally smooth manifold-valued map to a
globally smooth one without changing any germ along the compact region.
-/

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.DiskFraming

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Positive metric thickenings preserve star-convexity about zero. -/
theorem starConvex_thickening_zero {K : Set D} (hK : StarConvex ℝ (0 : D) K) (δ : ℝ) :
    StarConvex ℝ (0 : D) (thickening δ K) := by
  rw [starConvex_zero_iff]
  intro x hx a ha₀ ha₁
  obtain ⟨z, hz, hxz⟩ := mem_thickening_iff.mp hx
  apply mem_thickening_iff.mpr
  refine ⟨a • z, hK.smul_mem hz ha₀ ha₁, ?_⟩
  calc
    dist (a • x) (a • z) = a * dist x z := by
      simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha₀]
    _ ≤ dist x z := mul_le_of_le_one_left dist_nonneg ha₁
    _ < δ := hxz

variable [FiniteDimensional ℝ D]

/-- A globally smooth source map lands in the given open neighborhood and is the identity
on an actual open neighborhood of the compact star-convex region. -/
theorem exists_smooth_map_into_neighborhood {K U : Set D} (hK : IsCompact K)
    (hz : (0 : D) ∈ K) (hstar : StarConvex ℝ (0 : D) K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ : D → D, ContDiff ℝ ∞ ρ ∧ MapsTo ρ univ U ∧
      ∃ V : Set D, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn ρ id V := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  let W := thickening δ K
  have hW : IsOpen W := isOpen_thickening
  have hKW : K ⊆ W := self_subset_thickening hδ K
  have hstarW : StarConvex ℝ (0 : D) W := starConvex_thickening_zero hstar δ
  obtain ⟨L, hL, hKL, hLW⟩ := exists_compact_between hK hW hKW
  obtain ⟨β, hβ, hβrange, hβsupport, hβone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (𝓘(ℝ, D)) (n := (⊤ : ℕ∞)) hW hL.isClosed hLW
  let ρ : D → D := fun x => β x • x
  refine ⟨ρ, hβ.contDiff.smul contDiff_id, ?_, interior L, isOpen_interior, hKL,
    fun x hx => hδU (hLW (interior_subset hx)), ?_⟩
  · intro x _
    have hb := hβrange (mem_range_self x)
    by_cases hx : x ∈ W
    · exact hδU (hstarW.smul_mem hx hb.1 hb.2)
    · have hb0 : β x = 0 := by
        by_contra hn
        have hxs : x ∈ Function.support β := hn
        rw [hβsupport] at hxs
        exact hx hxs
      change β x • x ∈ U
      rw [hb0, zero_smul]
      exact hKU hz
  · intro x hx
    change β x • x = x
    rw [(hβone x).mp (interior_subset hx), one_smul]

end Wikipedia.SmoothSixDPoincare.DiskFraming

namespace Wikipedia.SmoothSixDPoincare

variable {D G H N : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [FiniteDimensional ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

/-- Locally smooth native maps extend globally while keeping every germ on the compact region. -/
theorem exists_smooth_extension_near_starConvex {f : D → N} {K U : Set D}
    (hK : IsCompact K) (hz : (0 : D) ∈ K) (hstar : StarConvex ℝ (0 : D) K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hf : ContMDiffOn 𝓘(ℝ, D) J ∞ f U) :
    ∃ g : D → N, ContMDiff 𝓘(ℝ, D) J ∞ g ∧
      ∃ V : Set D, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn g f V := by
  obtain ⟨ρ, hρ, hρU, V, hV, hKV, hVU, hρid⟩ :=
    DiskFraming.exists_smooth_map_into_neighborhood hK hz hstar hU hKU
  refine ⟨f ∘ ρ, contMDiffOn_univ.mp (hf.comp hρ.contMDiff.contMDiffOn hρU),
    V, hV, hKV, hVU, ?_⟩
  intro x hx
  exact congrArg f (hρid hx)

/-- A locally smooth map on a finite-dimensional source extends globally, fixing its point germ. -/
theorem exists_smooth_extension_near_point {f : D → N} {U : Set D} {x₀ : D}
    (hf : ContMDiffOn 𝓘(ℝ, D) J ∞ f U) (hU : IsOpen U) (hx₀ : x₀ ∈ U) :
    ∃ g : D → N, ContMDiff 𝓘(ℝ, D) J ∞ g ∧ g =ᶠ[𝓝 x₀] f := by
  let shift : D → D := fun x => x + x₀
  have hshift : ContDiff ℝ ∞ shift := contDiff_id.add contDiff_const
  have hf' : ContMDiffOn 𝓘(ℝ, D) J ∞ (f ∘ shift) (shift ⁻¹' U) :=
    hf.comp hshift.contMDiff.contMDiffOn (fun _ hx => hx)
  have hzero : ({0} : Set D) ⊆ shift ⁻¹' U := by
    intro x hx
    have hx0 : x = 0 := hx
    subst x
    simpa only [shift, mem_preimage, zero_add] using hx₀
  obtain ⟨g, hg, V, hV, h0V, _, heq⟩ :=
    exists_smooth_extension_near_starConvex isCompact_singleton (mem_singleton 0)
      (starConvex_singleton (0 : D)) (hU.preimage hshift.continuous) hzero hf'
  let g' : D → N := fun x => g (x - x₀)
  have hg' : ContMDiff 𝓘(ℝ, D) J ∞ g' :=
    hg.comp (contDiff_id.sub contDiff_const).contMDiff
  have htime : Filter.Tendsto (fun x : D => x - x₀) (𝓝 x₀) (𝓝 0) := by
    have htime' : Filter.Tendsto (fun x : D => x - x₀) (𝓝 x₀) (𝓝 (x₀ - x₀)) :=
      (continuous_id.sub continuous_const : Continuous (fun x : D => x - x₀)).continuousAt.tendsto
    rwa [sub_self] at htime'
  refine ⟨g', hg', ?_⟩
  filter_upwards [htime (hV.mem_nhds (h0V (mem_singleton 0)))] with x hx
  change g (x - x₀) = f x
  simpa only [Function.comp_apply, shift, sub_add_cancel] using heq hx

end Wikipedia.SmoothSixDPoincare
