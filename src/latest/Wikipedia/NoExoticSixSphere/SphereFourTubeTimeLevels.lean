import Wikipedia.NoExoticSixSphere.SphereFourTubeTimeModification

/-!
# The exact zero set and nonnegative exterior of the modified time

The new zero set is the old zero set together with the unit normal sphere
in the actual tube. Its nonnegative half is exactly the old half minus
the open unit tube. Near every old zero the time functions agree on an
actual neighborhood, not merely pointwise on that zero set.
-/

noncomputable section

open Function Set Metric Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)
  (τ : M → ℝ)
  (hinner : ∀ p : Sphere 3 × Vector 4, ‖p.2‖ ≤ 3 / 2 → τ (Φ p) = ‖p.2‖ ^ 2 - 1)
  (houter : ∀ p : Sphere 3 × Vector 4, 1 < ‖p.2‖ → 0 < τ (Φ p))

include hinner houter in
theorem modified_time_zero_on_tube_iff (p : Sphere 3 × Vector 4) :
    τ (Φ p) = 0 ↔ ‖p.2‖ = 1 := by
  by_cases hp : ‖p.2‖ ≤ 3 / 2
  · rw [hinner p hp]
    have hn := norm_nonneg p.2
    constructor <;> intro h <;> nlinarith
  · have hn : 1 < ‖p.2‖ := by linarith
    exact iff_of_false (ne_of_gt (houter p hn)) (ne_of_gt hn)

include hinner houter in
theorem modified_time_nonneg_on_tube_iff (p : Sphere 3 × Vector 4) :
    0 ≤ τ (Φ p) ↔ 1 ≤ ‖p.2‖ := by
  by_cases hp : ‖p.2‖ ≤ 3 / 2
  · rw [hinner p hp]
    have hn := norm_nonneg p.2
    constructor <;> intro h <;> nlinarith
  · have hn : 1 < ‖p.2‖ := by linarith
    exact iff_of_true (houter p hn).le hn.le

variable (hΦ : Φ.source = univ) (t : M → ℝ)
  (hpos : ∀ x ∈ Φ.target, 0 < t x)
  (hout : ∀ x ∉ closedRegion Φ 2, τ x = t x)

include hΦ hout in
theorem modified_time_eq_old_of_not_target {x : M} (hx : x ∉ Φ.target) : τ x = t x :=
  hout x (fun h ↦ hx (closedRegion_subset_target Φ hΦ 2 h))

include hinner houter hΦ hpos hout in
theorem modified_time_zero_iff (x : M) :
    τ x = 0 ↔ t x = 0 ∨ ∃ p : Sphere 3 × Vector 4, ‖p.2‖ = 1 ∧ Φ p = x := by
  constructor
  · intro hx
    by_cases hxΦ : x ∈ Φ.target
    · let p := Φ.symm x
      have hpx : Φ p = x := Φ.toPartialEquiv.right_inv hxΦ
      refine Or.inr ⟨p, ?_, hpx⟩
      exact (modified_time_zero_on_tube_iff Φ τ hinner houter p).mp (hpx ▸ hx)
    · exact Or.inl ((modified_time_eq_old_of_not_target Φ τ hΦ t hout hxΦ).symm.trans hx)
  · rintro (hx | ⟨p, hp, rfl⟩)
    · have hxΦ : x ∉ Φ.target := fun h ↦ (ne_of_gt (hpos x h)) hx
      exact (modified_time_eq_old_of_not_target Φ τ hΦ t hout hxΦ).trans hx
    · exact (modified_time_zero_on_tube_iff Φ τ hinner houter p).mpr hp

include hinner houter hΦ hpos hout in
theorem modified_time_nonneg_iff (x : M) :
    0 ≤ τ x ↔ 0 ≤ t x ∧ x ∉ openRegion Φ 1 := by
  by_cases hxΦ : x ∈ Φ.target
  · let p := Φ.symm x
    have hpx : Φ p = x := Φ.toPartialEquiv.right_inv hxΦ
    have hn : 0 ≤ τ x ↔ 1 ≤ ‖(Φ.symm x).2‖ := by
      simpa only [hpx] using modified_time_nonneg_on_tube_iff Φ τ hinner houter p
    rw [hn, mem_openRegion_iff Φ hΦ, and_iff_right hxΦ, not_lt]
    exact (and_iff_right (hpos x hxΦ).le).symm
  · have hxU : x ∉ openRegion Φ 1 := fun h ↦ hxΦ ((mem_openRegion_iff Φ hΦ 1 x).mp h).1
    rw [modified_time_eq_old_of_not_target Φ τ hΦ t hout hxΦ]
    exact (and_iff_left hxU).symm

include hΦ hpos hout in
theorem modified_time_eventuallyEq_old_zero [T2Space M] {x : M} (hx : t x = 0) :
    τ =ᶠ[𝓝 x] t := by
  have hxK : x ∉ closedRegion Φ 2 := fun h ↦
    (ne_of_gt (hpos x (closedRegion_subset_target Φ hΦ 2 h))) hx
  filter_upwards [((isCompact_closedRegion Φ hΦ 2).isClosed.isOpen_compl).mem_nhds hxK]
    with y hy
  exact hout y hy

end NoExoticSixSphere.SphereFourTube
