import Wikipedia.HopfProblem.RiemannBoundaryInjectivity
import Mathlib.Topology.DenseEmbedding

/-!
# Compactification of a disc homeomorphism by actual boundary limits

A homeomorphism from a dense subspace of a compact Hausdorff space to the
open disc extends to a homeomorphism onto the closed disc when its actual
forward and inverse boundary limits exist.  Continuity, injectivity and
surjectivity of the extension are proved, rather than included in the
boundary data.  The triangle's analytic boundary charts are intended to
supply those limits.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.RiemannBoundary

variable {X : Type*} [TopologicalSpace X] {D : Set X}

def discCompactificationMap (hD : Dense D) (e : D ≃ₜ ball (0 : ℂ) 1) : X → ℂ :=
  hD.extend (fun z : D => (e z : ℂ))

theorem discCompactificationMap_coe (hD : Dense D) (e : D ≃ₜ ball (0 : ℂ) 1) (z : D) :
    discCompactificationMap hD e z = (e z : ℂ) :=
  hD.extend_eq (continuous_subtype_val.comp e.continuous) z

/-- The boundary data consist of limits of the original maps, not an
assumed compactification homeomorphism. -/
def DiscBoundaryLimits (e : D ≃ₜ ball (0 : ℂ) 1) : Prop :=
  ∀ x ∉ D, ∃ w : ℂ, ‖w‖ = 1 ∧
    Tendsto (fun z : D => (e z : ℂ)) (comap Subtype.val (𝓝 x)) (𝓝 w) ∧
    Tendsto (discHomeomorphInverse e) (𝓝[ball (0 : ℂ) 1] w) (𝓝 x)

theorem discCompactificationMap_continuous (hD : Dense D)
    (e : D ≃ₜ ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) :
    Continuous (discCompactificationMap hD e) := by
  apply hD.continuous_extend
  intro x
  by_cases hx : x ∈ D
  · refine ⟨(e ⟨x, hx⟩ : ℂ), ?_⟩
    rw [← hD.isDenseInducing_val.nhds_eq_comap ⟨x, hx⟩]
    exact (continuous_subtype_val.comp e.continuous).continuousAt
  · obtain ⟨w, _, hw, _⟩ := hb x hx
    exact ⟨w, hw⟩

theorem discCompactificationMap_boundary (hD : Dense D)
    (e : D ≃ₜ ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) {x : X} (hx : x ∉ D) :
    ‖discCompactificationMap hD e x‖ = 1 ∧
      Tendsto (discHomeomorphInverse e)
        (𝓝[ball (0 : ℂ) 1] (discCompactificationMap hD e x)) (𝓝 x) := by
  obtain ⟨w, hw, ht, hi⟩ := hb x hx
  have he : discCompactificationMap hD e x = w := hD.extend_eq_of_tendsto ht
  rw [he]
  exact ⟨hw, hi⟩

theorem discCompactificationMap_norm_le (hD : Dense D)
    (e : D ≃ₜ ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) (x : X) :
    ‖discCompactificationMap hD e x‖ ≤ 1 := by
  by_cases hx : x ∈ D
  · rw [discCompactificationMap_coe hD e ⟨x, hx⟩]
    exact (show ‖(e ⟨x, hx⟩ : ℂ)‖ < 1 by
      simpa only [mem_ball, dist_zero_right] using (e ⟨x, hx⟩).property).le
  · exact ((discCompactificationMap_boundary hD e hb hx).1).le

variable [T2Space X]

theorem discCompactificationMap_injective (hD : Dense D)
    (e : D ≃ₜ ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) :
    Function.Injective (discCompactificationMap hD e) := by
  intro x y hxy
  by_cases hx : x ∈ D
  · by_cases hy : y ∈ D
    · apply congrArg Subtype.val (e.injective ?_ : (⟨x, hx⟩ : D) = ⟨y, hy⟩)
      apply Subtype.ext
      simpa only [discCompactificationMap_coe hD e ⟨x, hx⟩,
        discCompactificationMap_coe hD e ⟨y, hy⟩] using hxy
    · have hn := (discCompactificationMap_boundary hD e hb hy).1
      rw [← hxy, discCompactificationMap_coe hD e ⟨x, hx⟩] at hn
      have hlt : ‖(e ⟨x, hx⟩ : ℂ)‖ < 1 := by
        simpa only [mem_ball, dist_zero_right] using (e ⟨x, hx⟩).property
      exact (hlt.ne hn).elim
  · by_cases hy : y ∈ D
    · have hn := (discCompactificationMap_boundary hD e hb hx).1
      rw [hxy, discCompactificationMap_coe hD e ⟨y, hy⟩] at hn
      have hlt : ‖(e ⟨y, hy⟩ : ℂ)‖ < 1 := by
        simpa only [mem_ball, dist_zero_right] using (e ⟨y, hy⟩).property
      exact (hlt.ne hn).elim
    · obtain ⟨hn, ht⟩ := discCompactificationMap_boundary hD e hb hx
      have hu := (discCompactificationMap_boundary hD e hb hy).2
      rw [← hxy] at hu
      have : NeBot (𝓝[ball (0 : ℂ) 1] (discCompactificationMap hD e x)) :=
        mem_closure_iff_nhdsWithin_neBot.mp (unitCircle_mem_closure_unitBall hn)
      exact tendsto_nhds_unique ht hu

variable [CompactSpace X]

omit [T2Space X] in
theorem discCompactificationMap_range (hD : Dense D)
    (e : D ≃ₜ ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) :
    range (discCompactificationMap hD e) = closedBall (0 : ℂ) 1 := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    simpa using discCompactificationMap_norm_le hD e hb x
  · have hclosed : IsClosed (range (discCompactificationMap hD e)) :=
      (isCompact_range (discCompactificationMap_continuous hD e hb)).isClosed
    have hdisc : ball (0 : ℂ) 1 ⊆ range (discCompactificationMap hD e) := by
      intro y hy
      refine ⟨(e.symm ⟨y, hy⟩ : X), ?_⟩
      rw [discCompactificationMap_coe, e.apply_symm_apply]
    rw [← closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    exact closure_minimal hdisc hclosed

/-- A compact Hausdorff disc compactification, constructed from genuine
forward and inverse boundary limits. -/
def closedDiscHomeomorph (hD : Dense D)
    (e : D ≃ₜ ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) :
    X ≃ₜ closedBall (0 : ℂ) 1 := by
  let F : X → closedBall (0 : ℂ) 1 := fun x =>
    ⟨discCompactificationMap hD e x, by simpa using discCompactificationMap_norm_le hD e hb x⟩
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      exact discCompactificationMap_injective hD e hb (congrArg Subtype.val hxy)
    · intro y
      have hy : (y : ℂ) ∈ range (discCompactificationMap hD e) := by
        rw [discCompactificationMap_range hD e hb]
        exact y.property
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F hF)
    ((discCompactificationMap_continuous hD e hb).subtype_mk _)

theorem closedDiscHomeomorph_coe (hD : Dense D)
    (e : D ≃ₜ ball (0 : ℂ) 1) (hb : DiscBoundaryLimits e) (z : D) :
    (closedDiscHomeomorph hD e hb z : ℂ) = (e z : ℂ) :=
  discCompactificationMap_coe hD e z

end Wikipedia.HopfProblem.RiemannBoundary
